/* soko3.c: sokoban solver with deadlock checking and block slapping
   copyright (c) 2016 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* improved sokoban solver. same as soko2, but with block slapping
   - block slapping can't be turned off, use soko or soko2 instead
   - find deadlocks:
     - block that cannot be moved to any goal (block on dead cells)
     - block stuck in 2x2 or N configuration
   - detection of goal corridor with deadlock checking: blocks must be pushed
     all the way in, or else it's an illegal configuration
   - tighter state encoding, 1-1 mapping from integers to permutation of
     floor cells and blocks
   usage:
   - read puzzle from standard input
   file format:
   - size x y: set level size
   - goal x y: set man goal position (use if man goal overlaps with block,
     man-only floor or starting position). x,y are 0-indexed
   - skip-n-deadlock: skip the deadlock check that searches for the N pattern
   - skip-goal-corridor-deadlock: skip the deadlock check that checks for bad
     states in block corridor
   - map: followed by y lines with map data
     - #: wall
     -  : floor
     - @: man
     - $: block
     - .: destination
     - _: "dead cell" (cell where man can go, but not blocks)
     - *: block starting on destination
     - +: man starting on destination
     - =: man starting on dead cell
     - g: goal position for man
   * there are two ways to define man goal, and it's optional. if it's not
     defined, the puzzle is solved when all blocks are on destinations
   state encoding:
   - player dir+(5*man position+(number of floor cells)*(permutation rank of blocks/floor on))
     live cells only). this should be shorter than raw permutation rank over
     floor/blocks/man over all floor cells.
   - man position can have 5 values: 0-3 for player dirs, 4 for not moved
   - TODO find another way to represent direction, the current method is
     extremely wasteful (uses 25% more memory than needed). also, zero out
     direction when player is not near any slappable block for further savings
   - permutation of blocks and floor is calculated first, then man position is
     calculated as if blocks were walls (replaces the old, slightly worse
     encoding where the man was considered first, and two cases depending on
     whether man was on live or dead floor)
   - the only gaps in the current encoding are due to deadlocked states. the
     most common deadlocks (2x2 and N) could be removed from the mapping, but
     that requires a much more computationally intensive algorithm based on
     dynamic programming using frontiers. i haven't investigated the potential
     gains of this method, but it would certainly be much, much slower
   deadlock routines only subject to shallow testing, they seem to work
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "solver.h"

#define MAX 33

/* can use __uint128_t for compilers that support it for even larger puzzles */
typedef unsigned long long statetype;

static int dx[]={1,0,-1,0};
static int dy[]={0,1,0,-1};

/* static info about instance */
static struct static_s {
	char smap[MAX][MAX]; /* map showing walls (#), goals (.), floor ( ),
	                        dead cells (d) */
	int idmap[MAX][MAX]; /* floor id, [0, floor-1], -1 if non-floor */
	int id2map[MAX][MAX];/* floor id, [0, lfloor-1], non-dead floor only */
	int idx[MAX*MAX];    /* reverse id map */
	int idy[MAX*MAX];
	int id2x[MAX*MAX];   /* reverse id map for non-dead floor */
	int id2y[MAX*MAX];
	int x,y;             /* map size */
	int blocks;          /* number of blocks (and elements in id-map) */
	int floor;           /* number of floor */
	int lfloor;          /* number of non-dead floor */
	int goalx,goaly;     /* player goal */
	statetype dsize;     /* domain size (number of states) */
	int slen;            /* number of bytes in state */

	int hascorridor;     /* 1: has a goal corridor */
	int corridorlen;     /* length of corridor */
	int corridorx;       /* x-coordinate of start of corridor */
	int corridory;       /* y-coordinate of start of corridor */
	int corridordir;     /* direction of corridor (inwards) */
} info;

/* solver options */
static struct options_s {
	int skipndeadlock;   /* 1: skip checking for n-deadlock pattern */
	int skipgoaldeadlock; /* 1: skip checking for goal corridor deadlock */
} options;

static struct state_s {
	char map[MAX][MAX];
	int playerdir;       /* 0-3 dir (from dx[], dy[]), 4=not moved yet */
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
// each thread need its own pointer-thing because the info needs to live until
// the next call of this function
static unsigned char *getptr(statetype v,int thr) {
	int i;
	for(i=0;i<info.slen;i++) p[thr][i]=v&255,v>>=8;
	return p[thr];
}

/* ----- state representation: permutation rank ---------------------------- */

/* usage:
   - counts[i] contains the number of elements of id i
   - multiset[] is the permutation
   - plen is the length of the permutation
   rank: set all of these
   unrank: set counts and plen, multiset is returned
*/
/* warning, these routines are not general multinomial routines. there's a lot
   of hardcoded stuff for this domain */

#define MAXPASCAL 1025
static statetype pas[MAXPASCAL][MAXPASCAL];
static int counts[MAXTHR][2];                      /* only floor and block */
static int multiset[MAXTHR][MAX*MAX];              /* current board string (permutation) */
static int plen[MAXTHR];                           /* number of elements in permutation */

/* fast version (inline), result in res. will destroy upper,lower,i */
#define EVAL_MULT(res,upper,lower,i,coeff,evallen) { res=1; upper=coeff[0]; lower=0; for(i=1;i<evallen;i++) upper+=coeff[i],lower+=coeff[i-1],res*=pas[upper][lower]; }

/* calculate permutation rank of sequence in multiset[] */
static statetype permrank(int thr) {
	statetype res=0,r2;
	int i,j,k,upper,lower,left[2];
	for(i=0;i<2;i++) left[i]=counts[thr][i];
	for(i=0;i<plen[thr];i++) {
		for(j=0;j<multiset[thr][i];j++) if(left[j]) {
			left[j]--;
			EVAL_MULT(r2,upper,lower,k,left,2);
			res+=r2;
			left[j]++;
		}
		left[multiset[thr][i]]--;
	}
	return res;
}

/* given permutation rank, return sequence in multiset[] */
static void permunrank(statetype rank,int thr) {
	statetype run,next,r2;
	int i,j,upper,lower,k,left[2];
	for(i=0;i<2;i++) left[i]=counts[thr][i];
	for(i=0;i<plen[thr];i++) {
		for(run=j=0;j<2;j++) if(left[j]) {
			left[j]--;
			EVAL_MULT(r2,upper,lower,k,left,2);
			next=run+r2;
			if(next>rank) {
				multiset[thr][i]=j,rank-=run;
				break;
			}
			left[j]++;
			run=next;
		}
	}
}
#undef EVAL_MULT

static double doublenck(int n,int k) {
	int hi=n,lo=1;
	double r=1;
	while(k--) r*=(double)hi/lo,hi--,lo++;
	return r;
}

/* start of sokoban routines ----------------------------------------------- */

/* find dead cells */
static void deadsearch() {
	static int q[MAX*MAX*2];
	int qs=0,qe=0,i,j,cx,cy,x2,y2,x3,y3,d;
	/* start search at goal cells, all reachable cells with backwards moves
	   are marked as non-dead, the rest are dead */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(info.smap[i][j]=='.') q[qe++]=i,q[qe++]=j;
	while(qs<qe) {
		cx=q[qs++]; cy=q[qs++];
		for(d=0;d<4;d++) {
			x2=cx+dx[d]; y2=cy+dy[d];
			x3=x2+dx[d]; y3=y2+dy[d];
			if(x3<0 || y3<0 || x3>=info.x || y3>=info.y || info.smap[x2][y2]=='_' || info.smap[x2][y2]=='#' || info.smap[x2][y2]=='.' || info.smap[x3][y3]=='#') continue;
			if(info.smap[x2][y2]==' ') continue;
			info.smap[x2][y2]=' ';
			q[qe++]=x2; q[qe++]=y2;
		}
	}
	/* change cells from '_' to 'd' */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(info.smap[i][j]=='_') info.smap[i][j]='d';
}

/* find goal corridor that looks roughly like this:
   ##### normal
   #.... level
   ##### here
   it's a string of goals (.) that has a space behind it, a wall in front
   of it and walls on all sides (all out-of-bounds cells count as wall).
	 this routine finds the first corridor of length of at least 3 and uses it.
*/
static void findgoalcorridor() {
	info.hascorridor=0;
	for(int i=0;i<info.x;i++) for(int j=0;j<info.y;j++) if(info.smap[i][j]=='.') {
		for(int d=0;d<4;d++) {
			int bx=i+dx[d^2],by=j+dy[d^2];
			/* no open space behind: abort this goal+direction */
			if(bx<0 || by<0 || bx>=info.x || by>=info.y || info.smap[bx][by]!=' ') continue;
			int length=1;
			int x2=i,y2=j;
			int dl=(d+1)&3,dr=(d+3)&3;
			while(1) {
				/* check left and right, out-of-bounds or wall is ok */
				int x3=x2+dx[dl],y3=y2+dy[dl];
				if(x3>=0 && y3>=0 && x3<info.x && y3<info.y && info.smap[x3][y3]!='#') goto notcorridor;
				x3=x2+dx[dr]; y3=y2+dy[dr];
				if(x3>=0 && y3>=0 && x3<info.x && y3<info.y && info.smap[x3][y3]!='#') goto notcorridor;
				/* check in front */
				x2+=dx[d]; y2+=dy[d];
				if(x2<0 || y2<0 || x2>=info.x || y2>=info.y) break; /* we won */
				if(info.smap[x2][y2]=='#') break; /* we won */
				if(info.smap[x2][y2]=='.') {
					length++;
					continue;
				}
				goto notcorridor;
			}
			if(length<3) continue; /* not long enough */
			info.hascorridor=1;
			info.corridorlen=length;
			info.corridorx=i;
			info.corridory=j;
			info.corridordir=d;
			return;
		notcorridor:;
		}
	}
}

/* read input and populate info and cur */
void domain_init() {
	char s[1000],t[100],c;
	int i,j,men=0,goals=0;
	double dsize;
	statetype z;
	/* permutation init */
	for(i=0;i<MAXPASCAL;i++) {
		pas[i][0]=pas[i][i]=1;
		for(j=1;j<i;j++) pas[i][j]=pas[i-1][j]+pas[i-1][j-1];
	}
	info.goalx=info.goaly=-1;
	info.x=info.y=0;
	info.hascorridor=0;
	options.skipndeadlock=0;
	options.skipgoaldeadlock=0;
	cur[0].playerdir=4;
	memset(info.smap,0,sizeof(info.smap));
	memset(cur[0].map,0,sizeof(cur[0].map));
	while(fgets(s,998,stdin)) {
		if(s[0]=='#') continue; /* non-map line starting with #: comment */
		if(s[0]==13 || s[0]==10) continue; /* blank line */
		sscanf(s,"%98s",t);
		if(!strcmp(t,"size")) {
			if(2!=sscanf(s,"size %d %d",&info.x,&info.y)) error("wrong parameters for size");
			if(info.x>MAX || info.y>MAX) error("map too large, increase MAX and recompile");
		} else if(!strcmp(t,"goal")) {
			if(2!=sscanf(s,"goal %d %d",&info.goalx,&info.goaly)) error("wrong parameters for goal");
			if(info.goalx<0 || info.goaly<0 || info.goalx>=info.x || info.goaly>=info.y) error("man goal outside of map");
		} else if(!strcmp(t,"skip-n-deadlock")) {
			options.skipndeadlock=1;
		} else if(!strcmp(t,"skip-goal-corridor-deadlock")) {
			options.skipgoaldeadlock=1;
		} else if(!strcmp(t,"map")) {
			for(j=0;j<info.y;j++) {
				if(!fgets(s,998,stdin)) error("map ended unexpectedly");
				for(i=0;i<info.x;i++) {
					c=s[i];
					if(c=='#') info.smap[i][j]='#',cur[0].map[i][j]='#';
					else if(c==' ') info.smap[i][j]='d',cur[0].map[i][j]=' ';
					else if(c=='.') info.smap[i][j]='.',cur[0].map[i][j]=' ';
					else if(c=='$') info.smap[i][j]='d',cur[0].map[i][j]='$';
					else if(c=='_') info.smap[i][j]='_',cur[0].map[i][j]=' ';
					else if(c=='*') info.smap[i][j]='.',cur[0].map[i][j]='$';
					else if(c=='@') info.smap[i][j]='d',cur[0].map[i][j]='@';
					else if(c=='+') info.smap[i][j]='.',cur[0].map[i][j]='@';
					else if(c=='=') info.smap[i][j]='_',cur[0].map[i][j]='@';
					else if(c=='g') info.smap[i][j]='d',cur[0].map[i][j]=' ',info.goalx=i,info.goaly=j;
					else printf("illegal char %d\n",c),exit(1);
				}
			}
		} else {
			printf("ignored unknown command %s\n",t);
		}
	}
	/* at this point, cells not yet determined as live or dead are marked with
	   'd', while user-set dead cells are marked with '_' */
	/* search for non-dead cells */
	deadsearch();
	/* generate id-map */
	memset(info.idmap,-1,sizeof(info.idmap));
	memset(info.id2map,-1,sizeof(info.id2map));
	info.floor=info.blocks=info.lfloor=0;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) {
		if(info.smap[i][j]==' ' || info.smap[i][j]=='.') {
			info.id2x[info.lfloor]=i;
			info.id2y[info.lfloor]=j;
			info.id2map[i][j]=info.lfloor++;
		}
		if(info.smap[i][j]==' ' || info.smap[i][j]=='.' || info.smap[i][j]=='d') {
			info.idx[info.floor]=i;
			info.idy[info.floor]=j;
			info.idmap[i][j]=info.floor++;
		}
		if(info.smap[i][j]=='.') goals++;
		if(cur[0].map[i][j]=='@') men++;
		if(cur[0].map[i][j]=='$') info.blocks++;
	}
	printf("%d live floor, %d floor, %d blocks, %d goals\n",info.lfloor,info.floor,info.blocks,goals);
	if(men!=1) error("map must contain 1 man");
	if(goals!=info.blocks) error("map must contain same number of blocks and destinations");
	if(!goals) error("map must contain at least 1 block");
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur[0].map[i][j]=='$' && info.id2map[i][j]<0)
		error("illegal start config, block starts on dead space");
	/* find goal corridor */
	if(!options.skipgoaldeadlock) findgoalcorridor();
	/* check size: (#floors-#blocks) * (lfloor choose blocks) */
	/* multiply by 5 for player dir */
	dsize=5*(info.floor-info.blocks)*doublenck(info.lfloor,info.blocks);
	info.dsize=5*(info.floor-info.blocks)*pas[info.lfloor][info.blocks];
	/* if numbers went haywire, we overflowed */
	if(fabs(dsize-info.dsize)/dsize>0.001) error("state space too large");
	for(info.slen=0,z=info.dsize;z;info.slen++,z>>=8);
	printf("loaded sokoban puzzle, state space %.0f, state %d bytes\n",dsize,info.slen);
	// copy the cur[] array to all threads
	for(int i=1;i<MAXTHR;i++) cur[i]=cur[0];
}

unsigned char *domain_size() {
	return getptr(info.dsize-1,0);
}

int state_size() {
	return info.slen;
}

/* this doesn't currently output _ correctly, because the dead space search
   overwrote them with d. care about it later. we don't want to print out all
   the automatically detected 'd's, so we need to store the '_'s somewhere
   else */
void print_state(int thr) {
	int i,j;
	for(j=0;j<info.y;j++) {
		for(i=0;i<info.x;i++) {
			if(cur[thr].map[i][j]==' ' && info.smap[i][j]=='_') putchar('_');
			else if(cur[thr].map[i][j]==' ' && info.smap[i][j]=='.') putchar('.');
			else putchar(cur[thr].map[i][j]);
		}
		putchar('\n');
	}
	putchar('\n');
}

unsigned char *encode_state(int thr) {
	statetype v=0;
	int i,j,k;
	/* find man: count number of floor (dead or live) before man */
	for(v=i=j=0;j<info.y;j++) for(i=0;i<info.x;i++) {
		if(cur[thr].map[i][j]=='@') goto foundman;
		else if(cur[thr].map[i][j]=='$') continue;
		else if(info.smap[i][j]=='#') continue;
		v++;
	}
foundman:
	/* set playerdir to 4 (no direction) if there are no slappable blocks nearby */
	if(cur[thr].playerdir<4) {
		int x2=i+dx[cur[thr].playerdir],y2=j+dy[cur[thr].playerdir];
		/* can we continue in direction at all? check for wall */
		if(x2<0 || y2<0 || x2>=info.x || y2>=info.y || info.smap[x2][y2]=='#') {
//			printf("pruned dir %d (blocked by wall)\n",cur[thr].playerdir);print_state();
			cur[thr].playerdir=4;
			goto donedir;
		}
		/* we have block in front of us, check if it can be pushed */
		if(cur[thr].map[x2][y2]=='$') {
			int x3=x2+dx[cur[thr].playerdir],y3=y2+dy[cur[thr].playerdir];
			if(x3<0 || y3<0 || x3>=info.x || y3>=info.y || (info.smap[x3][y3]!=' ' && info.smap[x3][y3]!='.') || cur[thr].map[x3][y3]=='$') {
//				printf("pruned dir %d (blocked by block)\n",cur[thr].playerdir);print_state();
				cur[thr].playerdir=4;
				goto donedir;
			}
		}
		/* we can move, so check for slappable blocks on both sides */
		int dd=(cur[thr].playerdir+1)&3;
		x2=i+dx[dd]; y2=j+dy[dd];
		int x3=x2+dx[dd],y3=y2+dy[dd];
		if(x3>=0 && y3>=0 && x3<info.x && y3<info.y && cur[thr].map[x2][y2]=='$' && cur[thr].map[x3][y3]==' ' && info.smap[x3][y3]!='d') goto donedir;
		dd^=2;
		x2=i+dx[dd]; y2=j+dy[dd];
		x3=x2+dx[dd]; y3=y2+dy[dd];
		if(x3>=0 && y3>=0 && x3<info.x && y3<info.y && cur[thr].map[x2][y2]=='$' && cur[thr].map[x3][y3]==' ' && info.smap[x3][y3]!='d') goto donedir;
//		printf("pruned dir %d (no slappable blocks)\n",cur[thr].playerdir);print_state();
		cur[thr].playerdir=4;
	}
donedir:
	/* generate permutation for live cells only (floor and blocks) */
	counts[thr][0]=counts[thr][1]=plen[thr]=0;
	for(k=0;k<info.lfloor;k++) {
		i=info.id2x[k];
		j=info.id2y[k];
		if(cur[thr].map[i][j]==' ' || cur[thr].map[i][j]=='@') counts[thr][0]++,multiset[thr][plen[thr]++]=0;
		else if(cur[thr].map[i][j]=='$') counts[thr][1]++,multiset[thr][plen[thr]++]=1;
	}
	v+=permrank(thr)*(info.floor-info.blocks);
	v=v*5+cur[thr].playerdir;
	return getptr(v,thr);
}

void decode_state(unsigned char *p,int thr) {
	statetype v=getval(p);
	int i,j,k,w,l;
	/* clear map */
	for(i=0;i<info.floor;i++) cur[thr].map[info.idx[i]][info.idy[i]]=' ';
	/* extract player dir */
	cur[thr].playerdir=v%5; v/=5;
	/* extract man, but don't place him yet */
	w=v%(info.floor-info.blocks); v/=(info.floor-info.blocks);
	/* init unrank */
	counts[thr][0]=info.lfloor-info.blocks;
	counts[thr][1]=info.blocks;
	plen[thr]=counts[thr][0]+counts[thr][1];
	permunrank(v,thr);
	for(k=l=0;k<info.lfloor;k++) {
		i=info.id2x[k];
		j=info.id2y[k];
		cur[thr].map[i][j]=multiset[thr][l++]?'$':' ';
	}
	for(j=0;j<info.y;j++) for(i=0;i<info.x;i++) {
		if(info.smap[i][j]=='#' || cur[thr].map[i][j]=='$') continue;
		if(w--<1) {
			cur[thr].map[i][j]='@';
			goto manplaced;
		}
	}
manplaced:;
}

int won(int thr) {
	int i,j;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(info.smap[i][j]=='.' && cur[thr].map[i][j]!='$') return 0;
	if(info.goalx>-1 && info.goaly>-1 && cur[thr].map[info.goalx][info.goaly]!='@') return 0;
	return 1;
}

/* check for 2x2 deadlock with blocks+wall */
static int bad2x2v2(int thr) {
	for(int i=0;i<info.x-1;i++) for(int j=0;j<info.y-1;j++) {
		/* no blocks, no deadlock */
		if(cur[thr].map[i][j]!='$' && cur[thr].map[i+1][j]!='$' && cur[thr].map[i][j+1]!='$' && cur[thr].map[i+1][j+1]!='$') continue;
		/* insta-reject trivial case with 4 walls */
		if(info.smap[i][j]=='#' && info.smap[i+1][j]=='#' && info.smap[i][j+1]=='#' && info.smap[i+1][j+1]=='#') continue;
		int badblock=0;
		/* every cell in 2x2 must have block or wall and at least one block not on goal */
		if(info.smap[i][j]=='#');
		else if(cur[thr].map[i][j]=='$') {
			if(info.smap[i][j]!='.') badblock++;
		} else continue;
		if(info.smap[i+1][j]=='#');
		else if(cur[thr].map[i+1][j]=='$') {
			if(info.smap[i+1][j]!='.') badblock++;
		} else continue;
		if(info.smap[i][j+1]=='#');
		else if(cur[thr].map[i][j+1]=='$') {
			if(info.smap[i][j+1]!='.') badblock++;
		} else continue;
		if(info.smap[i+1][j+1]=='#');
		else if(cur[thr].map[i+1][j+1]=='$') {
			if(info.smap[i+1][j+1]!='.') badblock++;
		} else continue;
		if(badblock) return 1;
	}
	return 0;
}

/* detect deadlocked N-patterns */
/* check for #$
              $#
*/
/* TODO can optimize further by precalculating a list of (x,y) coordinates
   where this wall pattern occurs, and check only these */
static int badnhor1(int thr) {
	for(int i=0;i<info.x-2;i++) for(int j=0;j<info.y-1;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i][j]!='#' || info.smap[i+2][j+1]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur[thr].map[i+1][j]!='$' || cur[thr].map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i+1][j]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

/* check for  $#
             #$
*/
static int badnhor2(int thr) {
	for(int i=0;i<info.x-2;i++) for(int j=0;j<info.y-1;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i][j+1]!='#' || info.smap[i+2][j]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur[thr].map[i+1][j]!='$' || cur[thr].map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i+1][j]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

/* check for #
             $$
              #
*/
static int badnver1(int thr) {
	for(int i=0;i<info.x-1;i++) for(int j=0;j<info.y-2;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i][j]!='#' || info.smap[i+1][j+2]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur[thr].map[i][j+1]!='$' || cur[thr].map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i][j+1]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

/* check for  #
             $$
             #
*/
static int badnver2(int thr) {
	for(int i=0;i<info.x-1;i++) for(int j=0;j<info.y-2;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i+1][j]!='#' || info.smap[i][j+2]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur[thr].map[i][j+1]!='$' || cur[thr].map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i][j+1]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

static int hasgoaldeadlock(int thr) {
	if(!info.hascorridor) return 0;
	/* count number of blocks */
	int x2=info.corridorx,y2=info.corridory;
	int d=info.corridordir,len=info.corridorlen;
	/* check: deadlock if the following pattern exists: .$.
	   (which means the man pushed a block halfway in, but ran away).
	   i believe this is sufficient to catch all goal deadlocks and
	   inefficiencies */
	for(int i=0;i<len-2;i++) {
		if(cur[thr].map[x2+(i+0)*dx[d]][y2+(i+0)*dy[d]]==' ' &&
		   cur[thr].map[x2+(i+1)*dx[d]][y2+(i+1)*dy[d]]=='$' &&
		   cur[thr].map[x2+(i+2)*dx[d]][y2+(i+2)*dy[d]]==' ') return 1;
	}
	return 0;
}

static int deadpos2(int thr) {
	/* check for 2x2 configurations of wall/block where >=1 block is not on goal */
	if(bad2x2v2(thr)) return 1;
	/* check for N-pattern */
	if(!options.skipndeadlock) {
		if(badnhor1(thr)) return 1;
		if(badnhor2(thr)) return 1;
		if(badnver1(thr)) return 1;
		if(badnver2(thr)) return 1;
	}
	/* check for blocks not pushed fully in the goal corridor */
	if(!options.skipgoaldeadlock) {
		if(hasgoaldeadlock(thr)) return 1;
	}
	return 0;
}

void visit_neighbours(int thr) {
	int cx=0,cy=0,i,j,d,x2,y2,x3,y3,olddir=cur[thr].playerdir,dl,dr;
	int x2a,x2aa,y2a,y2aa;
	/* find man */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur[thr].map[i][j]=='@') cx=i,cy=j;
	for(d=0;d<4;d++) {
		dl=(d+3)&3; dr=(d+1)&3;
		cur[thr].playerdir=d;
		x2=cx+dx[d]; y2=cy+dy[d];
		if(x2<0 || y2<0 || x2>=info.x || y2>=info.y || info.smap[x2][y2]=='#') continue;
		if(cur[thr].map[x2][y2]==' ') {
			/* move man */
			cur[thr].map[cx][cy]=' ';
			cur[thr].map[x2][y2]='@';
			if(!deadpos2(thr)) add_child(encode_state(thr),thr);
			/* block slap left */
			x2a=cx+dx[dl]; y2a=cy+dy[dl];
			x2aa=x2a+dx[dl]; y2aa=y2a+dy[dl];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur[thr].map[x2a][y2a]=='$' && cur[thr].map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur[thr].map[x2a][y2a]=' '; cur[thr].map[x2aa][y2aa]='$';
				if(!deadpos2(thr)) add_child(encode_state(thr),thr);
				cur[thr].map[x2a][y2a]='$'; cur[thr].map[x2aa][y2aa]=' ';
			}
			/* block slap right */
			x2a=cx+dx[dr]; y2a=cy+dy[dr];
			x2aa=x2a+dx[dr]; y2aa=y2a+dy[dr];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur[thr].map[x2a][y2a]=='$' && cur[thr].map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur[thr].map[x2a][y2a]=' '; cur[thr].map[x2aa][y2aa]='$';
				if(!deadpos2(thr)) add_child(encode_state(thr),thr);
				cur[thr].map[x2a][y2a]='$'; cur[thr].map[x2aa][y2aa]=' ';
			}
			cur[thr].map[cx][cy]='@';
			cur[thr].map[x2][y2]=' ';
		} else if(cur[thr].map[x2][y2]=='$') {
			x3=x2+dx[d]; y3=y2+dy[d];
			if(x3<0 || y3<0 || x3>=info.x || y3>=info.y || info.smap[x3][y3]=='#' || info.smap[x3][y3]=='d' || cur[thr].map[x3][y3]!=' ') continue;
			/* push block */
			cur[thr].map[cx][cy]=' ';
			cur[thr].map[x2][y2]='@';
			cur[thr].map[x3][y3]='$';
			if(!deadpos2(thr)) add_child(encode_state(thr),thr);
			/* block slap left */
			x2a=cx+dx[dl]; y2a=cy+dy[dl];
			x2aa=x2a+dx[dl]; y2aa=y2a+dy[dl];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur[thr].map[x2a][y2a]=='$' && cur[thr].map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur[thr].map[x2a][y2a]=' '; cur[thr].map[x2aa][y2aa]='$';
				if(!deadpos2(thr)) add_child(encode_state(thr),thr);
				cur[thr].map[x2a][y2a]='$'; cur[thr].map[x2aa][y2aa]=' ';
			}
			/* block slap right */
			x2a=cx+dx[dr]; y2a=cy+dy[dr];
			x2aa=x2a+dx[dr]; y2aa=y2a+dy[dr];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur[thr].map[x2a][y2a]=='$' && cur[thr].map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur[thr].map[x2a][y2a]=' '; cur[thr].map[x2aa][y2aa]='$';
				if(!deadpos2(thr)) add_child(encode_state(thr),thr);
				cur[thr].map[x2a][y2a]='$'; cur[thr].map[x2aa][y2aa]=' ';
			}
			cur[thr].map[cx][cy]='@';
			cur[thr].map[x2][y2]='$';
			cur[thr].map[x3][y3]=' ';
		}
	}
}
