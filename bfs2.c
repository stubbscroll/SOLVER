/* bfs2.c: breadth-first search with disk swapping for larger graphs
   copyright (c) 2017 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* improved version of bfs.c
   - supports directed graphs
   - need (#states/8) bytes for bitmask of visited states, for immediate
     duplicate check
   - store list of visited states for each iteration in lists that are flushed
     to disk as needed (all disk access is linear, should be fast on non-ssd)
   - since we stored no edges, we need to do backward search used to
     reconstruct the solution (much faster than the initial search since we
     don't check for duplicates)
   - faster than bfsd, while being able to search farther (assuming we have
     enough memory for the bitmask)
   * TODO vbyte compression can be added for less space usage
   * TODO solution output could be made much faster by sorting each iteration,
     and requiring each domain to have a backwards move generator. then a binary
     search could be done within an iteration for the desired position. however,
     it's painful to implement (especially the backwards move generator, which
     is pointless otherwise)
   usage:
   - solver m a b < file.txt OR
   - solver m b < file.txt OR
     solver m < file.txt, where
     2^m is the size of each allocation unit (m=0: 1 unit for entire bit array)
     a is megabytes allocated for incoming states (can be small)
     b is megabytes allocated for outgoing states (huge is good)
     file.txt is the level to be solved
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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
	printf(".");
}

static void showsolution() {
	bfs.outputstate=getval(encode_state(0));
	// memory stats
	long long used=0;
	for(int i=0;i<bfs.chunks;i++) if(bfs.visited[i]) used++;
	printf("lazy allocation: %lld of %lld sub-arrays touched\n",used,bfs.chunks);
	printf("we won! solution steps (in reverse):\n");
	printf("move %d\n",bfs.gen+1);
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
		unsigned long long state=getval(p);
		if(isvisited(state)) return;
		setvisited(state);
		if(won(thr)) showsolution();
		if(bfs.cure==bfs.b2len) flushcur();
		copypos(bfs.b2+bfs.cure,p);
		bfs.cure+=bfs.slen;
	} else if(bfs.outputmode && !bfs.foundback) {
		unsigned long long state=getval(p);
		if(state==bfs.outputstate) bfs.foundback=1;
	}
}

static void solver_bfs() {
	/* save initial state to disk as iteration (generation) 0 */
	copypos(bfs.b2,encode_state(0));
	setvisited(getval(encode_state(0)));
	bfs.cure=bfs.slen;
	bfs.gen=-1;
	createnewgenfile(0);
	flushcur();
	bfs.tot=0;
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
		printf("%d: q %lld tot %lld\n",bfs.gen,len/bfs.slen,bfs.tot);
		if(!len) break;
		while(len>0) {
			long long grab=len<bfs.b1len?len:bfs.b1len;
			long long got=fread(bfs.b1,1,grab,f);
			if(got!=grab) error("read error");
			len-=grab;
			for(long long at=0;at<grab;at+=bfs.slen) {
				decode_state(bfs.b1+at,0);
				visit_neighbours(0);
			}
		}
		if(bfs.cure) flushcur();
		fclose(f);
	}
}

int main(int argc,char **argv) {
	int ram1=50,ram2=50,m=16;
	if(argc==2) m=strtol(argv[1],0,10);
	if(argc==3) m=strtol(argv[1],0,10),ram2=strtol(argv[2],0,10);
	else if(argc>3) m=strtol(argv[1],0,10),ram1=strtol(argv[2],0,10),ram2=strtol(argv[3],0,10);
	bfs.b1len=ram1*1048576LL;
	bfs.b2len=ram2*1048576LL;
	bfs.blockb=m;
	if(m==0) bfs.blocksize=0,bfs.blockb=0;
	else bfs.blocksize=1LL<<m;
	domain_init();
	solver_init();
	solver_bfs();
	return 0;
}
