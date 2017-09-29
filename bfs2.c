/* bfs2.c: breadth-first search with disk swapping for larger graphs
   copyright (c) 2017 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* improved version of bfs.c
   - supports directed graphs
   - need (#states/8) bytes for bitmask of visited states
   - store list of visited states for each iteration in lists that are flushed
     to disk as needed
   - duplicates are checked immediately against the bitmask
   - backward search used to reconstruct solution
   - expected to be faster than bfsd
   * vbyte compression can be added for less space usage
   usage:
   - solver a b < file.txt, where
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
	unsigned char *visited;            /* bitmask of visited states */
	long long visitedsize;             /* number of bytes in bitmask */

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

#define ISVISITED(state) (bfs.visited[(state)>>3]&(1<<((state)&7)))
#define SETVISITED(state) bfs.visited[(state)>>3]|=((1<<((state)&7)))

/* this is supposed to work in linux too */
/* return file size, or -1 if failed */
long long filesize(const char *s) {
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

/* save len bytes from memory *b as given name */
void savefile(unsigned char *b,size_t len,char *name) {
	FILE *f=fopen(name,"wb");
	if(!f) error("couldn't write file");
	unsigned long long n=fwrite(b,1,len,f);
	if(n!=len) error("write error");
	if(fclose(f)) error("error closing file for writing");
}

void solver_init() {
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
	if(!(bfs.visited=calloc(bfs.visitedsize,1))) error("out of memory allocating state space bitmask");
	if(!(bfs.b1=malloc(bfs.b1len))) error("out of memory allocating memory area 1");
	if(!(bfs.b2=malloc(bfs.b2len))) error("out of memory allocating memory area 2");
	bfs.outputmode=0;
}

void createnewgenfile(int gen) {
	char t[100];
	sprintf(t,"GEN-%04d",gen);
	FILE *g=fopen(t,"wb");
	if(!g) error("couldn't create current generation file");
	if(fclose(g)) error("error on creating current generation file");
}

/* flushes currently generated states to file GEN-(gen+1) */
void flushcur() {
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

void showsolution() {
	bfs.outputstate=getval(encode_state());
	printf("we won! solution steps (in reverse):\n");
	printf("move %d\n",bfs.gen+1);
	print_state();
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
				decode_state(bfs.b1+at);
				bfs.foundback=0;
				visit_neighbours();
				if(bfs.foundback) {
					bfs.outputstate=getval(bfs.b1+at);
					printf("move %d\n",bfs.gen);
					decode_state(bfs.b1+at);
					print_state();
					goto gendone;
				}
			}
		}
	gendone:
		fclose(f);
	}
	exit(0);
}

void add_child(unsigned char *p) {
	if(!bfs.outputmode) {
		unsigned long long state=getval(p);
		if(ISVISITED(state)) return;
		SETVISITED(state);
		if(won()) showsolution();
		if(bfs.cure==bfs.b2len) flushcur();
		copypos(bfs.b2+bfs.cure,p);
		bfs.cure+=bfs.slen;
	} else if(bfs.outputmode && !bfs.foundback) {
		unsigned long long state=getval(p);
		if(state==bfs.outputstate) bfs.foundback=1;
	}
}

void solver_bfs() {
	/* save initial state to disk as iteration (generation) 0 */
	copypos(bfs.b2,encode_state());
	SETVISITED(getval(encode_state()));
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
		printf("%d: q "LONG" tot "LONG"\n",bfs.gen,len/bfs.slen,bfs.tot);
		if(!len) break;
		while(len>0) {
			long long grab=len<bfs.b1len?len:bfs.b1len;
			long long got=fread(bfs.b1,1,grab,f);
			if(got!=grab) error("read error");
			len-=grab;
			for(long long at=0;at<grab;at+=bfs.slen) {
				decode_state(bfs.b1+at);
				visit_neighbours();
			}
		}
		if(bfs.cure) flushcur();
		fclose(f);
	}
}

int main(int argc,char **argv) {
	int ram1=50,ram2=50;
	if(argc>1) ram2=strtol(argv[1],0,10);
	else if(argc>2) ram1=strtol(argv[1],0,10),ram2=strtol(argv[2],0,10);
	bfs.b1len=ram1*1048576LL;
	bfs.b2len=ram2*1048576LL;
	domain_init();
	solver_init();
	solver_bfs();
	return 0;
}
