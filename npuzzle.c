/* npuzzle.c: solver for generalized 15-puzzle
   copyright (c) 2016 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* n-puzzle solver (generalised 15-puzzle)
   - check parity of input and report if it is unsolvable
   - size limit: when number of states don't fit in statetype
   usage:
   - read puzzle from standard input
   - if input is the start state, search without goal
   - if input is another state, solve for start state
   file format:
   - size x,y: set level size
   - map: followed by y lines with map data
     1-9: number between 1 and 9
     A-Z: number between 10 and 35
     a-z: number between 36 and 61
     {n}: literal number
      : empty cell
     0: alternative representation for empty cell
   state encoding:
   - permutation of numbers
   - TODO check if i can easily remove unsolvable states from mapping
   - dunno if i should use naive lexicographic rank/unrank, O(n) variant that
     uses lots of memory, or ruskey/myrvold. do some tests and pick the most
     well-behaving one
   - for O(n) time variant, consider using POPCNT if available, the speedup
     should be significant, and we can lift the puzzle size restriction
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <ctype.h>
#include "solver.h"

#define MAX 20
#define CROSSOVER 25 /* only use fast (memory-hungry) rank/unrank for x*y<=CROSSOVER */

/* can use __uint128_t for compilers that support it for even larger puzzles */
typedef unsigned long long statetype;

static int dx[]={1,0,-1,0};
static int dy[]={0,1,0,-1};

static struct static_s {
	int x,y;                   /* size */
	int xy;                    /* number of cells on board */
	statetype dsize;           /* domain size (number of states) */
	int slen;                  /* length of state in bytes */
	int goal;                  /* 1=search for goal, 0=exhaust graph */
} info;

static struct state_s {
	int map[MAX][MAX];
} cur[MAXTHR];

static void error(char *s) { puts(s); exit(1); }

/* convert pointer-thing to statetype */
static statetype getval(unsigned char *p) {
	statetype n=0;
	int i;
	for(i=0;i<info.slen;i++) n+=((statetype)p[i])<<(i*8);
	return n;
}

static unsigned char p[MAXTHR][16];

/* convert statetype to pointer-thing */
static unsigned char *getptr(statetype v,int thr) {
	int i;
	for(i=0;i<info.slen;i++) p[thr][i]=v&255,v>>=8;
	return p[thr];
}

/* check if current state is solvable
   solvable iff parity of permutation + parity of manhattan distance of blank
   tile to lower right is even */
static int issolvable(int thr) {
	int i,j,k,cab=0,parity=0,perm[MAX*MAX],len;
	/* find zero */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(!cur[thr].map[i][j]) cab=info.x+info.y-i-j-2;
	/* find permutation parity (ignore the empty cell) */
	for(j=k=0;j<info.y;j++) for(i=0;i<info.x;i++) if(cur[thr].map[i][j]) perm[k++]=cur[thr].map[i][j]-1;
	for(i=0;i<info.xy-1;i++) if(perm[i]>-1 && perm[i]!=i) {
		for(k=i,len=-1,j=perm[k],perm[k]=-1,k=j;j>-1;j=perm[k],perm[k]=-1,k=j,len++);
		parity+=len;
	}
	return (cab+parity+1)&1;
}

static char *dp;       /* dp table for rank/unrank, dp[i]: number of 1-bits in i */
static statetype factorial[64];

void domain_init() {
	char s[1000],t[100],c;
	int i,j,k,val;
	double dsize;
	statetype z;
	while(fgets(s,998,stdin)) {
		if(s[0]=='#') continue; /* non-map line starting with #: comment */
		sscanf(s,"%98s",t);
		if(!strcmp(t,"size")) {
			if(2!=sscanf(s,"size %d %d",&info.x,&info.y)) error("wrong parameters for size");
			if(info.x>MAX || info.y>MAX) error("map too large, increase MAX and recompile");
		} else if(!strcmp(t,"map")) {
			for(j=0;j<info.y;j++) {
				if(!fgets(s,998,stdin)) error("map ended unexpectedly");
				for(k=i=0;i<info.x;i++) {
					c=s[k++];
					if(c=='{') {
						val=0;
						while(isdigit(s[k])) val=val*10+s[k]-'0';
						if(s[k++]!='}') error("expected } in map");
						cur[0].map[i][j]=val;
					} else if(isdigit(c)) cur[0].map[i][j]=c-'0';
					else if(isupper(c)) cur[0].map[i][j]=c-'A'+10;
					else if(islower(c)) cur[0].map[i][j]=c-'a'+36;
					else if(c==' ') cur[0].map[i][j]=0;
					else error("illegal char");
				}
			}
		}
	}
	if(info.x<2 || info.y<2) error("size must be at least 2 in each dimension");
	info.xy=info.x*info.y;
	/* sanity: check that numbers from 0 to xy-1 occurs */
	for(k=0;k<info.xy;k++) {
		for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur[0].map[i][j]==k) goto ok;
		error("input must contains numbers from 1 to x*y-1");
	ok:;
	}
	/* check domain size */
	dsize=info.dsize=1;
	for(i=2;i<=info.xy;i++) dsize*=i,info.dsize*=i;
	/* if numbers went haywire, we overflowed */
	if(fabs(dsize-info.dsize)/dsize>0.001) error("state space too large");
	/* check if input is goal state. if so, then change search mode to "just
	   search as far as we can" */
	for(info.slen=0,z=info.dsize;z;info.slen++,z>>=8);
	info.goal=0;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur[0].map[i][j]!=(i+j*info.x+1)%info.xy) info.goal=1;
	/* check if start state is solvable */
	if(!issolvable(0)) error("unsolvable input state");
	/* precalculate tables for rank/unrank */
	factorial[0]=1;
	for(i=1;i<64;i++) factorial[i]=factorial[i-1]*i;
	if(info.xy<=CROSSOVER) {
		if(!(dp=malloc(1<<(info.xy-1)))) error("out of memory allocating dp table");
		for(dp[0]=0,i=1;i<(1<<(info.xy-1));i++) dp[i]=dp[i>>1]+(i&1);
	}
}

unsigned char *domain_size() {
	return getptr(info.dsize-1,0);
}

int state_size() {
	return info.slen;
}

void print_state(int thr) {
	int i,j;
	for(j=0;j<info.y;j++) {
		for(i=0;i<info.x;i++) printf("%3d",cur[thr].map[i][j]);
		putchar('\n');
	}
	putchar('\n');
}

static void hexchar(int x){
	if(x<10) printf("%d",x);
	else printf("%c",'A'+x-10);
}
static void printhex(int x) {
	hexchar(x/16); hexchar(x&15);
}

unsigned char *encode_state(int thr) {
	statetype v=0;
	int i,j,k,a,l;
	if(0 && info.xy<=CROSSOVER) {
		/* O(n) time, O(2^n) space */
		int taken=0;
		for(k=j=0;j<info.y;j++) for(i=0;i<info.x;i++,k++) {
			/* at step k: add k-th element (minus lower, earlier elements) * (x*y-k-1)! */
			a=cur[thr].map[i][j]-dp[taken&((1<<cur[thr].map[i][j])-1)];
			v+=a*factorial[info.xy-k-1];
			taken|=1<<cur[thr].map[i][j];
		}
	} else {
		/* O(n^2) time */
		long long taken=0;
		for(k=j=0;j<info.y;j++) for(i=0;i<info.x;i++,k++) {
			/* at step k: add k-th element (minus lower, earlier elements) * (x*y-k-1)! */
			for(a=l=0;l<cur[thr].map[i][j];l++) if(!(taken&(1LL<<l))) a++;
			v+=a*factorial[info.xy-k-1];
			taken|=1<<cur[thr].map[i][j];
		}
	}
	return getptr(v,thr);
}

void decode_state(unsigned char *p,int thr) {
	statetype v=getval(p);
	int i,j,k,a,l,m;
	long long taken=0;
	for(k=j=0;j<info.y;j++) for(i=0;i<info.x;i++,k++) {
		a=v/factorial[info.xy-k-1]; v%=factorial[info.xy-k-1];
		/* find the a-th element not yet taken */
		for(m=l=0;;m++) if(!(taken&(1LL<<m))) { l++; if(l>a) break; }
		cur[thr].map[i][j]=m;
		taken|=1LL<<m;
	}
}

int won(int thr) {
	int i,j,k;
	/* enumerate entire tree mode, never win */
	if(!info.goal) return 0;
	for(k=j=0;j<info.y;j++) for(i=0;i<info.x;i++,k++) if(cur[thr].map[i][j]!=(k+1)%info.xy) return 0;
	return 1;
}

void visit_neighbours(int thr) {
	int i,j,cx=0,cy=0,d,x2,y2,v;
	/* find blank */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(!cur[thr].map[i][j]) cx=i,cy=j;
	for(d=0;d<4;d++) {
		x2=cx+dx[d]; y2=cy+dy[d];
		if(x2<0 || y2<0 || x2>=info.x || y2>=info.y) continue;
		v=cur[thr].map[x2][y2];
		cur[thr].map[cx][cy]=v; cur[thr].map[x2][y2]=0;
		add_child(encode_state(thr),thr);
		cur[thr].map[x2][y2]=v;
	}
	cur[thr].map[cx][cy]=0;
}
