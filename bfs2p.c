/* bfs2p.c: breadth-first search with disk swapping for larger graphs,
   version with parallelism
   copyright (c) 2021 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* parallel version of bfs2.c
   - supports directed graphs
   - need (#states/8) bytes for bit array of visited states, for immediate
     duplicate check, though it's split into lazily allocated parts
   - store list of visited states for each iteration in lists that are flushed
     to disk as needed (all disk access is linear, should be fast on non-ssd)
   - since we don't store parent position, backward search is used to
     reconstruct the solution (much faster than the initial search since we
     don't check for duplicates)
   - some potential problems for parallel speedup
     - the queue is split equally between threads, but processing time could
       end up being uneven. currently, a thread has to wait for other threads
       to finish their queue before all threads are assigned a new queue
     - all threads have to synchronize between each search iteration (so less
       speedup for narrow and deep search trees)
     - unavoidable atomic operations like loading/saving to disk
     - pushing to the queue is currently atomic (TODO next thing to fix)
   - TODO solution output isn't parallelized at all, i guess i should do it
   usage:
   - solver t a b < file.txt OR
     solver t b < file.txt OR
     solver t < file.txt, where
     t is the number of threads 
     a is megabytes allocated for incoming states (default=50 mb, should be plenty)
     b is megabytes allocated for outgoing states per thread (default=50 mb, should be plenty)
     file.txt is the level to be solved
     i haven't measured performance yet as a function of a,b
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "pthread.h"
/*  for 64-bit filesize */
#ifdef __MINGW64__
	#include <sys/time.h>   /*  is this portable? */
	#include <windows.h>
	#include <winbase.h>
#elif defined (_MSC_VER)
	#include <windows.h>
	#include <winbase.h>
	#include <time.h>
#else
	#include <sys/stat.h>
	#include <time.h>
#endif
#include "solver.h"

static struct bfs_s {
	long long n;                       /* number of states */

	unsigned char **visited;           // pointer to pointers to visited states
	long long visitedsize;             /* number of bytes in bitmask */
	long long blocksize;               // number of bits in each sub-block
	int blockb;                        // number of bits in sub-block size
	long long chunks;                  // number of sub-blocks in **visited

	unsigned char *b1;                 /* memory area: read states from */
	unsigned char *b2;                 /* memory area: write states to */
	long long b1len;                   /* length of memory area b1 in bytes */
	long long b1slen;                  /* length of memory area b1 in states */
	long long b2len;                   /* length of memory area b2 in bytes */
	long long b2slen;                  /* length of memory area b2 in states */

	unsigned long long cure;           /* end of current iteration (offset) */

	int slen;                          /* length of state in bytes */
	int gen;                           /* iteration number */
	long long tot;                     /* total number of states visited */

	char outputmode;                   /* 0:normal search, 1:output solution */
	char foundback;                    /* 1:found previous state in solution search */
	unsigned long long outputstate;    /* state we're searching for */
} bfs;

static int threads;                // number of threads
static pthread_mutex_t *mutex_check;

static void error(char *s) { puts(s); exit(1); }

/* convert pointer-thing to unsigned long long */
static unsigned long long getval(unsigned char *p) {
	unsigned long long n=0;
	for(int i=0;i<bfs.slen;i++) n+=((unsigned long long)p[i])<<(i*8);
	return n;
}

/* copy state, needs addresses! */
static void copypos(unsigned char *to,unsigned char *from) {
	memcpy(to,from,bfs.slen);
}

int isvisited(long long state) {
	unsigned long long blockno=state>>bfs.blockb;
	unsigned char *ptr=bfs.visited[blockno];
	if(!ptr) return 0; // block not allocated => state not visited
	return bfs.visited[blockno][(state&(bfs.blocksize-1))>>3]&(1<<((state&(bfs.blocksize-1))&7));
}

void setvisited(long long state) {
	unsigned long long blockno=state>>bfs.blockb;
	unsigned char *ptr=bfs.visited[blockno];
	if(!ptr) {
		if(!(bfs.visited[blockno]=calloc((bfs.blocksize+7)/8,1))) error("error allocating newly encountered sub-block");
		ptr=bfs.visited[blockno];
	}
	bfs.visited[blockno][(state&(bfs.blocksize-1))>>3]|=((1<<((state&(bfs.blocksize-1)&7))));
}

/* this is supposed to work in linux too */
/* return file size, or -1 if failed */
static long long filesize(const char *s) {
#ifdef _MSC_VER
	HANDLE f=CreateFile(s,GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);
	LARGE_INTEGER z;
	if(INVALID_HANDLE_VALUE==f || !GetFileSizeEx(f,&z)) return -1;
	CloseHandle(f);
	return z.QuadPart;
#else
	long long l;
	FILE *f=fopen64(s,"rb");
	if(!f) return -1;
	fseeko64(f,0,SEEK_END);
	l=ftello64(f);
	fclose(f);
	return l;
#endif
}

static void solver_init() {
	bfs.slen=state_size();
	if(bfs.slen>8) error("state size too large (more than 8 bytes)");
	bfs.b1slen=bfs.b1len/bfs.slen;
	bfs.b2slen=bfs.b2len/bfs.slen;
	/* make life easier by making buffer length divisible by state length */
	bfs.b1len=bfs.b1slen*bfs.slen;
	bfs.b2len=bfs.b2slen*bfs.slen;
	bfs.n=getval(domain_size())+1;
	if(bfs.n==0 || bfs.n>=(1ULL<<60)-1) error("state space too large (more than 2^60 states)");
	bfs.visitedsize=(bfs.n+7)/8;
	// break down bit array into smaller sub-blocks (blocksize)
	if(!bfs.blocksize) {
		bfs.blocksize=1;
		bfs.blockb=0;
		while(bfs.blocksize<bfs.n) bfs.blocksize*=2,bfs.blockb++;
	}
	bfs.chunks=(bfs.n+bfs.blocksize-1)/bfs.blocksize;
	if(!(bfs.visited=malloc(bfs.chunks*sizeof(void *)))) error("out of memory allocating array to bitarrays");
	// mark each chunk as not allocated (not sure if calloc was safe here)
	for(int i=0;i<bfs.chunks;i++) bfs.visited[i]=NULL;
	if(!(mutex_check=malloc(bfs.chunks*sizeof(pthread_mutex_t *)))) error("out of memory allocating array to bitarrays");
	for(int i=0;i<bfs.chunks;i++) pthread_mutex_init(&mutex_check[i],NULL);
	if(!(bfs.b1=malloc(bfs.b1len))) error("out of memory allocating memory area 1");
	if(!(bfs.b2=malloc(bfs.b2len))) error("out of memory allocating memory area 2");
	bfs.outputmode=0;
}

static void createnewgenfile(int gen) {
	char t[100];
	sprintf(t,"GEN-%04d",gen);
	FILE *g=fopen(t,"wb");
	if(!g) error("couldn't create current generation file");
	if(fclose(g)) error("error on creating current generation file");
}

/* flushes currently generated states to file GEN-(gen+1) */
static void flushcur() {
	char t[100];
	sprintf(t,"GEN-%04d",bfs.gen+1);
	FILE *g=fopen(t,"ab");
	if(!g) error("couldn't append to current generation file");
	long long wrote=fwrite(bfs.b2,1,bfs.cure,g);
	if(wrote!=bfs.cure) error("write error");
	if(fclose(g)) error("error on appending to current generation file");
	bfs.cure=0;
	printf(".");fflush(stdout);
}

static pthread_mutex_t mutex_solution;
static pthread_mutex_t mutex_flush; // mutex on flushing output states
static int solution_found;          // win flag
static unsigned long long win_state;

// this part also takes a significant amount of time and should also be
// parallelized
// the master thread should take care of file stuff, while 
static void showsolution() {
	bfs.outputstate=win_state;
	printf("we won! solution steps (in reverse):\n");
	printf("move %d\n",bfs.gen+1);
	decode_state((void *)&win_state,0);
	print_state(0);
	/* go through all iteration files in reverse order, do a reverse search to
	   find actual states */
	bfs.outputmode=1;
	for(;bfs.gen>=0;bfs.gen--) {
		char s[100];
		sprintf(s,"GEN-%04d",bfs.gen);
		long long len=filesize(s);
		if(len<0) error("couldn't get file size of gen file");
		FILE *f=fopen(s,"rb");
		if(!f) error("couldn't open previous gen file");
		while(len>0) {
			long long grab=len<bfs.b1len?len:bfs.b1len;
			long long got=fread(bfs.b1,1,grab,f);
			if(got!=grab) error("read error");
			len-=grab;
			for(long long at=0;at<grab;at+=bfs.slen) {
				decode_state(bfs.b1+at,0);
				bfs.foundback=0;
				visit_neighbours(0);
				if(bfs.foundback) {
					bfs.outputstate=getval(bfs.b1+at);
					printf("move %d\n",bfs.gen);
					decode_state(bfs.b1+at,0);
					print_state(0);
					goto gendone;
				}
			}
		}
	gendone:
		fclose(f);
	}
	exit(0);
}

void add_child(unsigned char *p,int thr) {
	if(!bfs.outputmode) {
		if(solution_found) return;
		unsigned long long state=getval(p); // each thread has its own p, no need to mutex
		// one mutex per sub-array
		pthread_mutex_lock(&mutex_check[state>>bfs.blockb]);
		if(isvisited(state)) {
			pthread_mutex_unlock(&mutex_check[state>>bfs.blockb]);
			return;
		}
		setvisited(state);
		pthread_mutex_unlock(&mutex_check[state>>bfs.blockb]);
		pthread_mutex_lock(&mutex_solution);
		if(solution_found) {
			pthread_mutex_unlock(&mutex_solution);
			return;
		} else if(won(thr)) {
			solution_found=1;
			win_state=state;
			pthread_mutex_unlock(&mutex_solution);
			return;
		}
		pthread_mutex_unlock(&mutex_solution);
// TODO let each thread have its own output buffer, then we can avoid another
// mutex (except for flushing to disk)
		pthread_mutex_lock(&mutex_flush);
		if(bfs.cure==bfs.b2len) flushcur();
		copypos(bfs.b2+bfs.cure,p);
		bfs.cure+=bfs.slen;
		pthread_mutex_unlock(&mutex_flush);
	} else if(bfs.outputmode && !bfs.foundback) {
		unsigned long long state=getval(p);
		if(state==bfs.outputstate) bfs.foundback=1;
	}
}

static int pid[MAXTHR];

static long long bfs_grab;          // number of elements in current chunk
static pthread_mutex_t mutex_bfsq;  // mutex on bfs queue pointer
static pthread_barrier_t barrier;

// worker thread
static void *solver_bfs_worker(void *ptr) {
	int thr=*((int *)ptr);
	while(!solution_found) {
		// divide queue between threads, remove need for mutex
		long long bfs_at_local=(thr-1)*bfs.slen;
		// wait for start of next chunk
		pthread_barrier_wait(&barrier);
		// loop during current chunk
		while(1) {
			// poll queue
			if(bfs_at_local<bfs_grab && !solution_found) {
				decode_state(bfs.b1+bfs_at_local,thr);
				bfs_at_local+=bfs.slen*threads;
				visit_neighbours(thr);
			} else {
				pthread_mutex_unlock(&mutex_bfsq);
				// current queue is done
				pthread_barrier_wait(&barrier);
				break;
			}
		}
	}
	pthread_exit(NULL);
	return NULL;
}

// parallel version
// this is the master thread that manages the queue and makes states
// available for the worker threads
static void solver_bfs_p() {
	/* save initial state to disk as iteration (generation) 0 */
	copypos(bfs.b2,encode_state(0));
	setvisited(getval(encode_state(0)));
	bfs.cure=bfs.slen;
	bfs.gen=-1;
	createnewgenfile(0);
	flushcur();
	bfs.tot=0;
	solution_found=0;
	// create threads
	pthread_mutex_init(&mutex_bfsq,NULL);
	pthread_mutex_init(&mutex_flush,NULL);
	pthread_mutex_init(&mutex_solution,NULL);
	pthread_barrier_init(&barrier,NULL,threads+1);
	pthread_t t[MAXTHR];
	for(int i=1;i<=threads;i++) {
		// maybe overly conservative way of passing id, but whatever
		pid[i]=i;
		int rc=pthread_create(&t[i],NULL,solver_bfs_worker,pid+i);
		if(rc) error("error spawning threads");
	}
	for(bfs.gen=0;;bfs.gen++) {
		char s[100],t[100];
		sprintf(s,"GEN-%04d",bfs.gen);
		sprintf(t,"GEN-%04d",bfs.gen+1);
		long long len=filesize(s);
		if(len<0) error("couldn't get file size of gen file");
		FILE *f=fopen(s,"rb");
		if(!f) error("couldn't open previous gen file");
		createnewgenfile(bfs.gen+1);
		bfs.cure=0;
		bfs.tot+=len/bfs.slen;
		printf("%d: q %lld tot %lld\n",bfs.gen,len/bfs.slen,bfs.tot);fflush(stdout);
		if(!len) break;
		while(len>0) {
			long long grab=len<bfs.b1len?len:bfs.b1len;
			long long got=fread(bfs.b1,1,grab,f);
			if(got!=grab) error("read error");
			len-=grab;
			bfs_grab=grab;
			// start workers
			pthread_barrier_wait(&barrier);
			// wait until all workers are done with their chunk
			pthread_barrier_wait(&barrier);
		}
		if(bfs.cure) flushcur();
		fclose(f);
		if(solution_found) break;
	}
	for(int i=1;i<threads;i++) pthread_join(t[i],NULL);
	pthread_mutex_destroy(&mutex_bfsq);
	pthread_mutex_destroy(&mutex_flush);
	pthread_mutex_destroy(&mutex_solution);
	for(int i=0;i<bfs.chunks;i++) pthread_mutex_destroy(&mutex_check[i]);
	if(solution_found) showsolution();
	else puts("no solution found");
}

static void usage() {
	puts("bfs2p by stubbscroll in 2021\n");
	puts("usage: bfs2p t [m [[[a] b]] < file.txt");
	puts("where t is the number of threads (1 master thread and t-1 worker threads)");
	puts("      a is the number of megabytes allocated for incoming states (default 400)");
	puts("      b is the number of megabytes allocated for outgoing states (default 50)");
	puts("      m is the size of each subarray in bits (0=no subarrays)");
	puts("      file.txt is the puzzle to be solved");
	puts("temp files with names GEN-xxxx will be created in the current directory");
	exit(0);
}

int main(int argc,char **argv) {
	int ram1=400,ram2=50,m=20;
	if(argc<2) usage();
	else if(argc==3) m=strtol(argv[2],0,10);
	else if(argc==4) m=strtol(argv[2],0,10),ram2=strtol(argv[3],0,10);
	else if(argc>4) m=strtol(argv[2],0,10),ram1=strtol(argv[3],0,10),ram2=strtol(argv[4],0,10);
	threads=strtol(argv[1],0,10);
	if(threads<1 || threads>=MAXTHR) error("number of threads should be between 1 and 999");
	bfs.blockb=m;
	if(m==0) bfs.blocksize=0,bfs.blockb=0;
	else bfs.blocksize=1LL<<m;
	bfs.b1len=ram1*1048576LL;
	bfs.b2len=ram2*1048576LL;
	domain_init();
	solver_init();
	solver_bfs_p();
	return 0;
}
