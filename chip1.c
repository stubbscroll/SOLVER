/* chip1.c: sokoban solver with simple deadlock checking, and with added
   support for popup walls and force floors
   copyright (c) 2019 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* improved sokoban solver
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
   - goal x y: set man goal position (use if man goal overlaps with block
     or starting position)
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
     - g: man goal (aka exit)
     - i suppose i could add ice
   - additional elements
     - < > ^ v: force floor (everything needs 0 moves to travel fully, no
       overriding)
     - o: open popup wall (when taken, change to # in current state map)
   * there are two ways to define man goal. if it's not defined, the puzzle
     is solved when all blocks are on destinations
   * it's not allowed to push a block onto force floor that doesn't end on
     floor tile
   * the man can enter force floor if it ends on floor or pushable block
   state encoding:
   - bit array of popup walls + 2^popups * player dir+(5*man position+(number of floor cells)*(permutation rank of blocks/floor on))
     live cells only). this should be shorter than raw permutation rank over
     floor/blocks/man over all floor cells
   - man position can have 5 values: 0-3 for player dirs, 4 for not moved
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
   - TODO profile and speed up the program. the deadlock check looks very
     inefficient
   - TODO find more ways to detect deadlocks
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
	int idpx[MAX*MAX];   /* reverse id map for popup walls */
	int idpy[MAX*MAX];
	int x,y;             /* map size */
	int goalx,goaly;     /* man goal */
	int blocks;          /* number of blocks (and elements in id-map) */
	int floor;           /* number of floor */
	int popup;           /* number of popup walls */
	int lfloor;          /* number of non-dead floor */
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
	int skipndeadlock;    /* 1: skip checking for n-deadlock pattern */
	int skipgoaldeadlock; /* 1: skip checking for goal corridor deadlock */
} options;

static struct state_s {
	char map[MAX][MAX];
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
static int counts[2];                      /* only floor and block */
static int multiset[MAX*MAX];              /* current board string (permutation) */
static int plen;                           /* number of elements in permutation */

/* fast version (inline), result in res. will destroy upper,lower,i */
#define EVAL_MULT(res,upper,lower,i,coeff,evallen) { res=1; upper=coeff[0]; lower=0; for(i=1;i<evallen;i++) upper+=coeff[i],lower+=coeff[i-1],res*=pas[upper][lower]; }

/* calculate permutation rank of sequence in multiset[] */
static statetype permrank() {
	statetype res=0,r2;
	int i,j,k,upper,lower,left[2];
	for(i=0;i<2;i++) left[i]=counts[i];
	for(i=0;i<plen;i++) {
		for(j=0;j<multiset[i];j++) if(left[j]) {
			left[j]--;
			EVAL_MULT(r2,upper,lower,k,left,2);
			res+=r2;
			left[j]++;
		}
		left[multiset[i]]--;
	}
	return res;
}

/* given permutation rank, return sequence in multiset[] */
static void permunrank(statetype rank) {
	statetype run,next,r2;
	int i,j,upper,lower,k,left[2];
	for(i=0;i<2;i++) left[i]=counts[i];
	for(i=0;i<plen;i++) {
		for(run=j=0;j<2;j++) if(left[j]) {
			left[j]--;
			EVAL_MULT(r2,upper,lower,k,left,2);
			next=run+r2;
			if(next>rank) {
				multiset[i]=j,rank-=run;
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

static int isforcefloor(int i,int j) {
	return info.smap[i][j]=='<' || info.smap[i][j]=='>' || info.smap[i][j]=='^' || info.smap[i][j]=='v';
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
	info.x=info.y=0;
	info.goalx=info.goaly=-1;
	info.hascorridor=0;
	options.skipndeadlock=0;
	options.skipgoaldeadlock=0;
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
					else if(c==' ') info.smap[i][j]=' ',cur[0].map[i][j]=' ';
					else if(c=='.') info.smap[i][j]='.',cur[0].map[i][j]=' ';
					else if(c=='$') info.smap[i][j]=' ',cur[0].map[i][j]='$';
					else if(c=='_') info.smap[i][j]='_',cur[0].map[i][j]=' ';
					else if(c=='*') info.smap[i][j]='.',cur[0].map[i][j]='$';
					else if(c=='@') info.smap[i][j]=' ',cur[0].map[i][j]='@';
					else if(c=='+') info.smap[i][j]='.',cur[0].map[i][j]='@';
					else if(c=='=') info.smap[i][j]='_',cur[0].map[i][j]='@';
					else if(c=='g') info.smap[i][j]=' ',cur[0].map[i][j]=' ',info.goalx=i,info.goaly=j;
					else if(c=='o') info.smap[i][j]='_',cur[0].map[i][j]='o';
					else if(c=='<') info.smap[i][j]='<',cur[0].map[i][j]=' ';
					else if(c=='>') info.smap[i][j]='>',cur[0].map[i][j]=' ';
					else if(c=='^') info.smap[i][j]='^',cur[0].map[i][j]=' ';
					else if(c=='v') info.smap[i][j]='v',cur[0].map[i][j]=' ';
					else printf("illegal char %d\n",c),exit(1);
				}
			}
		} else {
			printf("ignored unknown command %s\n",t);
		}
	}
	/* disable deadsearch until it works with force floors */
	/* generate id-map */
	memset(info.idmap,-1,sizeof(info.idmap));
	memset(info.id2map,-1,sizeof(info.id2map));
	info.floor=info.blocks=info.lfloor=info.popup=0;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) {
		if(isforcefloor(i,j)) continue; /* force floors can't contain things */
		if(info.smap[i][j]==' ' || info.smap[i][j]=='.') {
			info.id2x[info.lfloor]=i;
			info.id2y[info.lfloor]=j;
			info.id2map[i][j]=info.lfloor++;
		}
		if(info.smap[i][j]==' ' || info.smap[i][j]=='.' || info.smap[i][j]=='d' || info.smap[i][j]=='_') {
			info.idx[info.floor]=i;
			info.idy[info.floor]=j;
			info.idmap[i][j]=info.floor++;
		}
		if(cur[0].map[i][j]=='o') {
			info.idpx[info.popup]=i;
			info.idpy[info.popup++]=j;
		}
		if(info.smap[i][j]=='.') goals++;
		if(cur[0].map[i][j]=='@') men++;
		if(cur[0].map[i][j]=='$') info.blocks++;
	}
	if(men!=1) error("map must contain 1 man");
	if(goals!=info.blocks) error("map must contain same number of blocks and destinations");
	if(!goals) error("map must contain at least 1 block");
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur[0].map[i][j]=='$' && info.id2map[i][j]<0)
		error("illegal start config, block starts on dead space");
	/* find goal corridor */
	if(!options.skipgoaldeadlock) findgoalcorridor();
	/* check size: (#floors-#blocks) * (lfloor choose blocks) */
	/* because man can't stand on blocks! */
	dsize=(info.floor-info.blocks)*doublenck(info.lfloor,info.blocks)*pow(2,info.popup);
	info.dsize=(info.floor-info.blocks)*pas[info.lfloor][info.blocks]*(1ULL<<info.popup);
	/* if numbers went haywire, we overflowed */
	if(fabs(dsize-info.dsize)/dsize>0.001) error("state space too large");
	for(info.slen=0,z=info.dsize;z;info.slen++,z>>=8);
	printf("loaded sokoban puzzle, state space %.0f, state %d bytes\n",dsize,info.slen);
}

unsigned char *domain_size() {
	return getptr(info.dsize-1,0);
}

int state_size() {
	return info.slen;
}

/* this doesn't currently output _ correctly, because the dead space search
   overwrote them with d. care about it later */
void print_state(int thr) {
	int i,j;
	for(j=0;j<info.y;j++) {
		for(i=0;i<info.x;i++) {
			if(cur[thr].map[i][j]==' ' && info.smap[i][j]=='_') putchar('_');
			else if(cur[thr].map[i][j]==' ' && info.smap[i][j]=='.') putchar('.');
			else if(isforcefloor(i,j)) putchar(info.smap[i][j]);
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
	for(v=j=0;j<info.y;j++) for(i=0;i<info.x;i++) {
		if(cur[thr].map[i][j]=='@') goto foundman;
		else if(cur[thr].map[i][j]=='$') continue;
		else if(info.smap[i][j]=='#') continue;
		else if(isforcefloor(i,j)) continue;
		v++;
	}
foundman:
	/* generate permutation for live cells only (floor and blocks) */
	counts[0]=counts[1]=plen=0;
	for(k=0;k<info.lfloor;k++) {
		i=info.id2x[k];
		j=info.id2y[k];
		if(cur[thr].map[i][j]==' ' || cur[thr].map[i][j]=='@') counts[0]++,multiset[plen++]=0;
		else if(cur[thr].map[i][j]=='$') counts[1]++,multiset[plen++]=1;
	}
	v+=permrank()*(info.floor-info.blocks);
	/* popup walls */
	for(i=info.popup-1;i>=0;i--) {
		char c=cur[thr].map[info.idpx[i]][info.idpy[i]];
		/* set bit to 1 (popup wall is wall) if tile contains wall or man or
		   floor (floor means we walked off the tile) */
		v=(v<<1)+(c=='#' || c=='@' || c==' ' || c=='_');
	}
	return getptr(v,thr);
}

void decode_state(unsigned char *p,int thr) {
	statetype v=getval(p);
	int i,j,k,w,l;
	/* clear map */
	for(i=0;i<info.floor;i++) cur[thr].map[info.idx[i]][info.idy[i]]=' ';
	/* read popup walls */
	for(i=0;i<info.popup;i++) {
		cur[thr].map[info.idpx[i]][info.idpy[i]]=(v&1)?'#':'o';
		v>>=1;
	}
	/* extract man, but don't place him yet */
	w=v%(info.floor-info.blocks); v/=(info.floor-info.blocks);
	/* init unrank */
	counts[0]=info.lfloor-info.blocks;
	counts[1]=info.blocks;
	plen=counts[0]+counts[1];
	permunrank(v);
	for(k=l=0;k<info.lfloor;k++) {
		i=info.id2x[k];
		j=info.id2y[k];
		cur[thr].map[i][j]=multiset[l++]?'$':' ';
	}
	for(j=0;j<info.y;j++) for(i=0;i<info.x;i++) {
		if(info.smap[i][j]=='#' || cur[thr].map[i][j]=='$' || isforcefloor(i,j)) continue;
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

/* return 1 if tile (i,j) has an acting wall */
/* popped-up walls are stored in a different array from normal walls */
static int iswall(int i,int j,int thr) {
	return info.smap[i][j]=='#' || cur[thr].map[i][j]=='#';
}

/* check for 2x2 deadlock with blocks+wall */
static int bad2x2v2(int thr) {
	for(int i=0;i<info.x-1;i++) for(int j=0;j<info.y-1;j++) {
		/* no blocks, no deadlock */
		if(cur[thr].map[i][j]!='$' && cur[thr].map[i+1][j]!='$' && cur[thr].map[i][j+1]!='$' && cur[thr].map[i+1][j+1]!='$') continue;
		/* insta-reject trivial case with 4 walls */
		if(iswall(i,j,thr) && iswall(i+1,j,thr) && iswall(i,j+1,thr) && iswall(i+1,j+1,thr)) continue;
		int badblock=0;
		/* every cell in 2x2 must have block or wall and at least one block not on goal */
		if(iswall(i,j,thr));
		else if(cur[thr].map[i][j]=='$') {
			if(info.smap[i][j]!='.') badblock++;
		} else continue;
		if(iswall(i+1,j,thr));
		else if(cur[thr].map[i+1][j]=='$') {
			if(info.smap[i+1][j]!='.') badblock++;
		} else continue;
		if(iswall(i,j+1,thr));
		else if(cur[thr].map[i][j+1]=='$') {
			if(info.smap[i][j+1]!='.') badblock++;
		} else continue;
		if(iswall(i+1,j+1,thr));
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
   where this wall pattern occurs, and that have live non-destination cells,
   and check only these */
static int badnhor1(int thr) {
	for(int i=0;i<info.x-2;i++) for(int j=0;j<info.y-1;j++) {
		/* walls not in place, deadlock not possible */
		if(!iswall(i,j,thr) || !iswall(i+2,j+1,thr)) continue;
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
		if(!iswall(i,j+1,thr) || !iswall(i+2,j,thr)) continue;
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
		if(!iswall(i,j,thr) || !iswall(i+1,j+2,thr)) continue;
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
		if(!iswall(i+1,j,thr) || !iswall(i,j+2,thr)) continue;
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

/* given tile (*i,*j) with force floor, return where we eventually end up
   (also in (*i,*j)) plus new direction *d */
static void followforcefloor(int *i,int *j,int *d) {
	int steps=0;
	while(isforcefloor(*i,*j)) {
		char c=info.smap[*i][*j];
		if(c=='<') (*i)--,*d=2;
		else if(c=='>') (*i)++,*d=0;
		else if(c=='^') (*j)--,*d=3;
		else if(c=='v') (*j)++,*d=1;
		steps++;
		if(steps>MAX*MAX) puts("infinite loop"),exit(1);
	}
}

void visit_neighbours(int thr) {
	int cx=0,cy=0,i,j,d,x2,y2,x3,y3;
	/* find man */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur[thr].map[i][j]=='@') cx=i,cy=j;
	for(d=0;d<4;d++) {
		x2=cx+dx[d]; y2=cy+dy[d];
		if(x2<0 || y2<0 || x2>=info.x || y2>=info.y || iswall(x2,y2,thr)) continue;
		int d2=d;
		if(isforcefloor(x2,y2)) followforcefloor(&x2,&y2,&d2);
		/* special case: we move to the tile we came from: ignore the move */
		if(cx==x2 && cy==y2) continue;
		char bak=cur[thr].map[x2][y2]; /* preserve status of popup wall */
		if(cur[thr].map[x2][y2]==' ' || cur[thr].map[x2][y2]=='o') {
			/* move man */
			cur[thr].map[cx][cy]=' ';
			cur[thr].map[x2][y2]='@';
			if(!deadpos2(thr)) add_child(encode_state(thr),thr);
			cur[thr].map[cx][cy]='@';
			cur[thr].map[x2][y2]=bak;
		} else if(cur[thr].map[x2][y2]=='$') {
			x3=x2+dx[d2]; y3=y2+dy[d2];
			if(x3<0 || y3<0 || x3>=info.x || y3>=info.y || iswall(x3,y3,thr) || info.smap[x3][y3]=='_' || info.smap[x3][y3]=='d' || cur[thr].map[x3][y3]!=' ') continue;
			int d3=d2;
			if(isforcefloor(x3,y3)) followforcefloor(&x3,&y3,&d3);
			if(iswall(x3,y3,thr) || info.smap[x3][y3]=='_' || info.smap[x3][y3]=='d' || cur[thr].map[x3][y3]!=' ') continue;
			/* check special case 1: we get whacked by the block we just pushed */
			if(x2==x3 && y2==y3) continue;
			/* check special case 2: we push block to the tile we moved from */
			if(cx==x3 && cy==y3) {
				cur[thr].map[cx][cy]='$';
				cur[thr].map[x2][y2]='@';
				if(!deadpos2(thr)) add_child(encode_state(thr),thr);
				cur[thr].map[cx][cy]='@';
				cur[thr].map[x2][y2]='$';
			} else {
				/* normal case: push the block normally, all relevant tiles are different */
				cur[thr].map[cx][cy]=' ';
				cur[thr].map[x2][y2]='@';
				cur[thr].map[x3][y3]='$';
				if(!deadpos2(thr)) add_child(encode_state(thr),thr);
				cur[thr].map[cx][cy]='@';
				cur[thr].map[x2][y2]='$';
				cur[thr].map[x3][y3]=' ';
			}
		}
	}
}
