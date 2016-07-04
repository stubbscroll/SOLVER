/* bfs on undirected graph
   - state graph must be undirected, so some domains will not work (like
     sokoban)
   - store only previous 2 iterations + the one we're generating (this is
     sufficient for duplicate checking)
   - as a consequence of the above, solution output is not currently supported.
     this requires each iteration to be saved (for instance to disk)
   - delayed duplicate detection: check for duplicates in batches - after we
     generate all moves from an iteration or we run out of memory. more
     efficient since we only need one linear scan of each previous iteration
     per batch
   - store states explicitly, sort states within each iteration
   - no size restriction on state size
   - search gives up when the two previous iterations + iteration under
     generation cannot all fit in memory
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
	long long prevprevs,prevpreve; /* previous previous iteration: start,end (actual offsets in b) */
	long long prevs,preve;        /* previous iteration */
	long long curs,cure;          /* current iteration */
	long long prevprevn,prevn,curn; /* number of elements in each iteration */
	long long curnn;              /* number of processed (duplicate-checked) states in current iteration */
	long long curin;              /* number of unprocessed states in current iteration */
	long long curcs;              /* start of unprocessed part of current iteration */

	int repack;                   /* number of repacks done in current iteration */

	int iter;                     /* number of iterations done */
	long long tot;                /* total number of positions visited */

	int slen;                     /* length of state in bytes */
} bfs;

static void hexchar(int x){
	if(x<10) printf("%d",x);
	else printf("%c",'A'+x-10);
}
static void printhex(int x) {
	hexchar(x/16); hexchar(x&15);
}

static void error(char *s) { puts(s); exit(1); }

void solver_init() {
	bfs.slen=state_size();
	bfs.bblen=bfs.blen/bfs.slen;
	bfs.blen=bfs.bblen*bfs.slen;
	if(!(bfs.b=malloc(bfs.blen))) error("out of memory");
	/* init bfs */
	bfs.prevs=bfs.preve=bfs.prevn=0;
	bfs.prevprevs=bfs.prevpreve=bfs.prevprevn=0;
	bfs.curs=bfs.cure=bfs.curn=0;
	bfs.iter=0;
	bfs.tot=1; /* start state */
	bfs.repack=0;
}

/* copy pos, needs addresses! */
static void copypos(unsigned char *to,unsigned char *from) {
	memcpy(to,from,bfs.slen);
}

/* slow, generic comparator, potential hotspot */
int comppos(const void *A,const void *B) {
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

static void printrawstate(unsigned char *p) {
	for(int i=0;i<bfs.slen;i++) printhex(p[i]),printf(" ");printf("\n");
}

void add_child(unsigned char *p) {
	if(bfs.cure==bfs.blen) {
		/* current generation too large, repack */
		/* memory layout at this point:
		   prevprevn states containing second last iteration
		   prevn states containing last iteration
		   curnn states containing sorted states of current iteration with duplicates
		     from previous iterations removed
		   curcs: index (in number of states) of first unsorted, un-duplicate-checked
		     state
		   curin: number of unsorted states
		   repack: number of times we've repacked this iteration */
		/* sort the unsorted states and remove duplicates */
		bfs.curin=sortandcompress(bfs.curcs,bfs.curin);
		/* remove states that are duplicates from previous iterations */
		/* if the state graph is both undirected and bipartite (example: bricks with
		   steps), we don't need to check against prev for duplicates! TODO include
		   it later */
		bfs.curin=removeduplicates2(bfs.prevprevs,bfs.prevprevn,bfs.prevs,bfs.prevn,bfs.curcs,bfs.curin);
		/* sort states found since last repack into previously sorted chunk from
		   current generation */
		/* TODO merge is sufficient, but it needs to be in-place. i don't think sorting
		   here increases the asymptotic runtime complexity of the complete program,
		   though */
		if(bfs.repack) bfs.curnn=sortandcompress(bfs.curs,bfs.curin+bfs.curnn);
		else bfs.curnn=bfs.curin;
		bfs.curin=0;
		bfs.cure=bfs.curcs=bfs.curs+bfs.curnn*bfs.slen;
		bfs.repack++;
		if(bfs.cure+bfs.slen>bfs.blen) {
			printf("memory full after %d repacks\n",bfs.repack);
			error("out of memory");
		}
	}
//	printf("  FOUND NEW STATE %I64d: ",bfs.cure);
//	printrawstate(p);
//	print_state();
	if(won()) {
		printf("we won in %d moves\n",bfs.iter+1);
		error("output of solution not currently supported");
	}
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

void solver_bfs() {
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
//			printf("POP FROM %I64d: ",at);
//			printrawstate(bfs.b+at);
//			print_state();
			visit_neighbours();
		}
		/* sort current iteration and remove duplicates within the iteration */
		/* up to this point, only cure, curin and curnn are set (not curn) */
//		puts("QUEUE before dupl");printqueue();
		bfs.curn=sortandcompress(bfs.curs,bfs.curnn+bfs.curin);
		bfs.cure=bfs.curs+bfs.curn*bfs.slen;
//		puts("QUEUE after sort");printqueue();
		/* remove duplicates against prev and prevprev */
		bfs.curn=removeduplicates2(bfs.prevprevs,bfs.prevprevn,bfs.prevs,bfs.prevn,bfs.curs,bfs.curn);
		bfs.cure=bfs.curs+bfs.curn*bfs.slen;
//		puts("QUEUE after dupl");printqueue();
		/* copy prev+cur to start of area */
		memcpy(bfs.b,bfs.b+bfs.prevs,(bfs.prevn+bfs.curn)*bfs.slen);
		/* set counts */
		bfs.prevprevn=bfs.prevn; bfs.prevn=bfs.curn;
		/* set pointers based on counts */
		bfs.prevs=bfs.prevpreve=bfs.prevprevn*bfs.slen;
		bfs.preve=bfs.curcs=bfs.curs=bfs.cure=bfs.prevs+bfs.prevn*bfs.slen;
		bfs.tot+=bfs.curn;
		bfs.iter++;
//		puts("QUEUE after iter-stuff");printqueue();
	}
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
