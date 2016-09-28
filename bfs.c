/* simple bfs:
   - supports directed graphs
   - number of states must fit in unsigned long long (minus 2 that are reserved
     for start state and unvisited)
   - state space must fit in memory, need (16*number of states) bytes
   - n states are encoded as integers [0,n-1] (need not be tight)
*/

#include <stdio.h>
#include <stdlib.h>
#include "solver.h"

#define ROOT 0xFFFFFFFFFFFFFFFFull
#define UNVISITED 0xFFFFFFFFFFFFFFFEull

static struct bfs_s {
	unsigned long long *prev;     /* prev[i]: parent of state i, ROOT for start state,
	                                 UNVISITED for unvisited */
	unsigned long long *q;        /* bfs queue */
	unsigned long long qs,qe;     /* start and end pointers in queue */
	unsigned long long n;         /* number of states */
	int slen;                     /* length of state in bytes */
	unsigned long long cur;       /* state we're currently processing */
} bfs;

static void error(char *s) { puts(s); exit(1); }

/* convert pointer-thing to unsigned long long */
static unsigned long long getval(unsigned char *p) {
	unsigned long long n=0;
	int i;
	for(i=0;i<bfs.slen;i++) n+=((unsigned long long)p[i])<<(i*8);
	return n;
}

/* convert unsigned long long to pointer-thing */
static unsigned char *getptr(unsigned long long v) {
	static unsigned char p[8];
	int i;
	for(i=0;i<bfs.slen;i++) p[i]=v&255,v>>=8;
	return p;
}

/* allocate queue and visited arrays */
static void solver_init() {
	unsigned long long i;
	bfs.slen=state_size();
	if(bfs.slen>8) error("state size too large");
	bfs.n=getval(domain_size())+1;
	if(bfs.n==0 || bfs.n>=(1ULL<<60)-1) error("state space too large");
	if(!(bfs.prev=malloc(bfs.n*sizeof(unsigned long long)))) error("out of memory allocating prev");
	if(!(bfs.q=malloc(bfs.n*sizeof(unsigned long long)))) error("out of memory allocating q");
	printf("states "LONG"\n",bfs.n);
	for(i=0;i<bfs.n;i++) bfs.prev[i]=UNVISITED;
}

static void showsolution(unsigned long long state) {
	unsigned long long *sol,v;
	int len=0,i;
	puts("we won! solution steps:");
	v=state;
	while(v!=ROOT) len++,v=bfs.prev[v];
	if(!(sol=malloc(len*sizeof(unsigned long long)))) error("out of memory when showing solution");
	v=state; i=len;
	while(v!=ROOT) sol[--i]=v,v=bfs.prev[v];
	for(i=0;i<len;i++) {
		printf("move %d\n",i);
		decode_state(getptr(sol[i]));
		print_state();
	}
	exit(0);
}

void add_child(unsigned char *p) {
	unsigned long long next=getval(p);
	if(bfs.prev[next]==UNVISITED) {
		bfs.prev[next]=bfs.cur;
		if(won()) showsolution(next);
		bfs.q[bfs.qe++]=next;
		if(bfs.qe==bfs.n) bfs.qe=0;
		if(bfs.qs==bfs.qe) error("bfs queue exhausted");
	}
}

static void solver_bfs() {
	bfs.qs=bfs.qe=0;
	bfs.q[bfs.qe++]=getval(encode_state());
	bfs.prev[bfs.q[0]]=ROOT;
	while(bfs.qs<bfs.qe) {
		decode_state(getptr(bfs.cur=bfs.q[bfs.qs]));
		bfs.qs++; if(bfs.qs==bfs.n) bfs.qs=0;
		if(bfs.qs%100000==0) printf("processed "ULONG" states, "ULONG" in queue\n",bfs.qs,bfs.qe-bfs.qs);
		visit_neighbours();
	}
}

int main() {
	domain_init();
	solver_init();
	solver_bfs();
	return 0;
}
