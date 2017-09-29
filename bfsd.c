/* bfsd.c: breadth-first search with delayed duplicate detection
   copyright (c) 2016-2017 by stubbscroll,
   under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* improved version of bfs.c
   - supports directed graphs
   - store list of all visited states instead of marking them in array
   - solution output is not currently supported, as no parent info is stored (to
     save memory). storing each iteration separately will allow output
   - delayed duplicate detection: check for duplicates in batches - after we
     generate all moves from an iteration or we run out of memory. more efficient
     since we only need one linear scan of previously visited states per batch
   - store states explicitly, list of visited states is sorted
   - no size restriction on state size
   - search gives up when the list of all previous states + current iteration
     (after duplicate check) cannot fit in memory
   - the algorithm stores several lists of sorted states. when sorting, the
     first byte is the least significant
   * implement in later versions: disk swapping, vbyte compression
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "solver.h"

static struct bfs_s {
	unsigned char *b;             /* memory area */
	long long blen;               /* length of memory area in bytes */
	long long bblen;              /* length of memory area in number of states */
	long long prevprevs,prevpreve; /* all states from iteration-2 and earlier */
	long long prevs,preve;        /* previous iteration */
	long long curs,cure;          /* current iteration */
	long long prevprevn,prevn,curn; /* number of states in all iterations<=cur-2, previous and current */
	long long curnn;              /* number of processed (duplicate-checked) states in current iteration */
	long long curin;              /* number of unprocessed states in current iteration */
	long long curcs;              /* start of unprocessed part of current iteration */

	int repack;                   /* number of repacks done in current iteration */
	
	int iter;                     /* number of iterations done */
	long long tot;                /* total number of positions visited */
	
	int slen;                     /* length of state in bytes */
} bfs;

static void error(char *s) { puts(s); exit(1); }

static void solver_init() {
	bfs.slen=state_size();
	bfs.bblen=bfs.blen/bfs.slen;
	bfs.blen=bfs.bblen*bfs.slen;
	if(!(bfs.b=malloc(bfs.blen))) error("out of memory");
	/* init bfs */
	bfs.prevs=bfs.preve=bfs.prevn=0;
	bfs.curs=bfs.cure=bfs.curn=0;
	bfs.iter=0;
	bfs.tot=1; /* includes start state */
	bfs.repack=0;
}

/* copy pos, needs addresses! */
static void copypos(unsigned char *to,unsigned char *from) {
	memcpy(to,from,bfs.slen);
}

/* slow, generic comparator, potential hotspot */
static int comppos(const void *A,const void *B) {
	const unsigned char *a=A,*b=B;
	int i;
	for(i=bfs.slen-1;i>=0;i--) {
		if(a[i]<b[i]) return -1;
		if(a[i]>b[i]) return 1;
	}
	return 0;
}

/* sorts and compresses a memory chunk starting at curs with curn positions,
   all stored explicitly. returns the new number of positions */
static long long sortandcompress(long long curs,long long curn) {
	long long i,j;
	long long ip,jp,p;
	if(curn<1) return 0;
	qsort(bfs.b+curs,curn,bfs.slen,comppos);
	for(i=j=1,ip=jp=curs+bfs.slen,p=curs;i<curn;i++,ip+=bfs.slen) if(comppos(bfs.b+p,bfs.b+ip)) {
		if(i!=j) copypos(bfs.b+jp,bfs.b+ip);
		j++; p=jp; jp+=bfs.slen;
	}
	return j;
}

/* remove duplicates against two lists */
static long long removeduplicates2(long long prevprevs,long long prevprevn,long long prevs,long long prevn,long long curs,long long curn) {
	long long prevprevat=0,prevat=0,curat=0,curv=curs,curto=0;
	while(curat<curn) {
		while(prevprevat<prevprevn && comppos(bfs.b+prevprevs,bfs.b+curs)<0) prevprevat++,prevprevs+=bfs.slen;
		while(prevat<prevn && comppos(bfs.b+prevs,bfs.b+curs)<0) prevat++,prevs+=bfs.slen;
		if(prevprevat<prevprevn && !comppos(bfs.b+prevprevs,bfs.b+curs)) goto skip;
		if(prevat<prevn && !comppos(bfs.b+prevs,bfs.b+curs)) goto skip;
		if(curv!=curs) copypos(bfs.b+curv,bfs.b+curs);
		curv+=bfs.slen;
		curto++;
	skip:
		curat++;
		curs+=bfs.slen;
	}
	return curto;
}

/* remove duplicates against one list */
static long long removeduplicates1(long long prevs,long long prevn,long long curs,long long curn) {
	long long prevat=0,curat=0,curv=curs,curto=0;
	while(curat<curn) {
		while(prevat<prevn && comppos(bfs.b+prevs,bfs.b+curs)<0) prevat++,prevs+=bfs.slen;
		if(prevat<prevn && !comppos(bfs.b+prevs,bfs.b+curs)) goto skip;
		if(curv!=curs) copypos(bfs.b+curv,bfs.b+curs);
		curv+=bfs.slen;
		curto++;
	skip:
		curat++;
		curs+=bfs.slen;
	}
	return curto;
}

static void hexchar(int x){
	if(x<10) printf("%d",x);
	else printf("%c",'A'+x-10);
}
static void printhex(int x) {
	hexchar(x/16); hexchar(x&15);
}
static void printrawstate(unsigned char *p) {
	for(int i=0;i<bfs.slen;i++) {
		printhex(p[i]);
		printf(" ");
	}
	printf("\n");
}

void add_child(unsigned char *p) {
	if(bfs.cure==bfs.blen) {
		/* current generation too large, repack TODO */
		error("TODO repack not yet implemented");
	}
	if(won()) {
		printf("we won in %d moves\n",bfs.iter+1);
		error("output of solution not currently supported");
	}
//	printf("  FOUND NEW STATE %I64d: ",bfs.cure);printrawstate(p);print_state();
	copypos(bfs.b+bfs.cure,p);
	bfs.cure+=bfs.slen;
	bfs.curin++;
}

static void printqueue() {
	long long i;
	for(i=0;i<bfs.prevpreve;i+=bfs.slen) printf("prevprev %6I64d: ",i),printrawstate(bfs.b+i);
	for(;i<bfs.preve;i+=bfs.slen) printf("prev     %6I64d: ",i),printrawstate(bfs.b+i);
	for(;i<bfs.cure;i+=bfs.slen) printf("cur      %6I64d: ",i),printrawstate(bfs.b+i);
}

static void solver_bfs() {
	long long at;
	/* insert initial position into previous iteration */
	copypos(bfs.b,encode_state());
	bfs.curcs=bfs.preve=bfs.curs=bfs.cure=bfs.slen;
	bfs.prevn=1;
	while(bfs.prevn) {
		if(bfs.repack) printf("[%d] ",bfs.repack),bfs.repack=0;
		printf("%d: q "LONG" tot "LONG"\n",bfs.iter,bfs.prevn,bfs.tot);
		for(bfs.curnn=bfs.curin=0,at=bfs.prevs;at<bfs.preve;at+=bfs.slen) {
			decode_state(bfs.b+at);
//			printf("POP FROM %I64d: ",at);printrawstate(bfs.b+at);print_state();
			visit_neighbours();
		}
		/* sort current iteration and remove duplicates within the iteration */
		/* up to this point, only cure, curin and curnn are set (not curn) */
//		puts("QUEUE before dupl");printqueue();
		bfs.curn=sortandcompress(bfs.curs,bfs.curnn+bfs.curin);
		bfs.cure=bfs.curs+bfs.curn*bfs.slen;
//		puts("QUEUE after sort");printqueue();
		/* remove duplicates against previous iterations (stored in prev and prevprev) */
		bfs.curn=removeduplicates2(bfs.prevprevs,bfs.prevprevn,bfs.prevs,bfs.prevn,bfs.curs,bfs.curn);
		bfs.cure=bfs.curs+bfs.curn*bfs.slen;
//		puts("QUEUE after dupl");printqueue();
		/* prepare for next iteration:
		   merge prevprev and prev, set prev to cur, set cur to empty */
		bfs.prevprevn=sortandcompress(bfs.prevprevs,bfs.prevprevn+bfs.prevn);
		/* update pointers and counts */
		bfs.prevpreve=bfs.prevprevs+bfs.prevprevn*bfs.slen;
		bfs.prevs=bfs.prevpreve; bfs.prevn=bfs.curn;
		bfs.preve=bfs.prevs+bfs.prevn*bfs.slen;
		bfs.curs=bfs.cure=bfs.curcs=bfs.preve;
		bfs.tot+=bfs.curn;
		bfs.curn=0;
		bfs.iter++;
//		puts("QUEUE after iter-stuff");printqueue();
	}
	puts("no solution found");
}

int main(int argc,char **argv) {
	int ram=50;
	if(argc>1) ram=strtol(argv[1],0,10);
	bfs.blen=ram*1048576LL;
	domain_init();
	solver_init();
	solver_bfs();
	return 0;
}
