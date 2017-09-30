/* soko3.c: sokoban solver with deadlock checking and block slapping
   copyright (c) 2016 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* improved sokoban solver. same as soko2, but with block slapping
   - block slapping can't be turned off, use soko or soko2 instead
   - find deadlocks:
     - block that cannot be moved to any goal (block on dead cells)
     - block stuck in 2x2 or N configuration
   - tighter state encoding, 1-1 mapping from integers to permutation of
     floor cells and blocks
   usage:
   - read puzzle from standard input
   file format:
   - size x y: set level size
   - goal x y: set man goal position (use if man goal overlaps with block,
     man-only floor or starting position). x,y are 0-indexed
   - skip-n-deadlock: skip the deadlock check that searches for the N pattern
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
} info;

/* solver options */
static struct options_s {
	int skipndeadlock;   /* 1: skip checking for n-deadlock pattern */
} options;

static struct state_s {
	char map[MAX][MAX];
	int playerdir;       /* 0-3 dir (from dx[], dy[]), 4=not moved yet */
} cur;

static void error(char *s) { puts(s); exit(1); }

/* convert pointer-thing to statetype */
static statetype getval(unsigned char *p) {
	statetype n=0;
	int i;
	for(i=0;i<info.slen;i++) n+=((statetype)p[i])<<(i*8);
	return n;
}

/* convert statetype to pointer-thing */
static unsigned char *getptr(statetype v) {
	static unsigned char p[16];
	int i;
	for(i=0;i<info.slen;i++) p[i]=v&255,v>>=8;
	return p;
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
void permunrank(statetype rank) {
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
	options.skipndeadlock=0;
	cur.playerdir=4;
	memset(info.smap,0,sizeof(info.smap));
	memset(cur.map,0,sizeof(cur.map));
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
		} else if(!strcmp(t,"map")) {
			for(j=0;j<info.y;j++) {
				if(!fgets(s,998,stdin)) error("map ended unexpectedly");
				for(i=0;i<info.x;i++) {
					c=s[i];
					if(c=='#') info.smap[i][j]='#',cur.map[i][j]='#';
					else if(c==' ') info.smap[i][j]='d',cur.map[i][j]=' ';
					else if(c=='.') info.smap[i][j]='.',cur.map[i][j]=' ';
					else if(c=='$') info.smap[i][j]='d',cur.map[i][j]='$';
					else if(c=='_') info.smap[i][j]='_',cur.map[i][j]=' ';
					else if(c=='*') info.smap[i][j]='.',cur.map[i][j]='$';
					else if(c=='@') info.smap[i][j]='d',cur.map[i][j]='@';
					else if(c=='+') info.smap[i][j]='.',cur.map[i][j]='@';
					else if(c=='=') info.smap[i][j]='_',cur.map[i][j]='@';
					else if(c=='g') info.smap[i][j]='d',cur.map[i][j]=' ',info.goalx=i,info.goaly=j;
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
		if(cur.map[i][j]=='@') men++;
		if(cur.map[i][j]=='$') info.blocks++;
	}
	if(men!=1) error("map must contain 1 man");
	if(goals!=info.blocks) error("map must contain same number of blocks and destinations");
	if(!goals) error("map must contain at least 1 block");
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur.map[i][j]=='$' && info.id2map[i][j]<0)
		error("illegal start config, block starts on dead space");
	/* check size: (#floors-#blocks) * (lfloor choose blocks) */
	/* multiply by 5 for player dir */
	dsize=5*(info.floor-info.blocks)*doublenck(info.lfloor,info.blocks);
	info.dsize=5*(info.floor-info.blocks)*pas[info.lfloor][info.blocks];
	/* if numbers went haywire, we overflowed */
	if(fabs(dsize-info.dsize)/dsize>0.001) error("state space too large");
	for(info.slen=0,z=info.dsize;z;info.slen++,z>>=8);
	printf("loaded sokoban puzzle, state space %.0f, state %d bytes\n",dsize,info.slen);
}

unsigned char *domain_size() {
	return getptr(info.dsize-1);
}

int state_size() {
	return info.slen;
}

/* this doesn't currently output _ correctly, because the dead space search
   overwrote them with d. care about it later */
void print_state() {
	int i,j;
	for(j=0;j<info.y;j++) {
		for(i=0;i<info.x;i++) {
			if(cur.map[i][j]==' ' && info.smap[i][j]=='_') putchar('_');
			else if(cur.map[i][j]==' ' && info.smap[i][j]=='.') putchar('.');
			else putchar(cur.map[i][j]);
		}
		putchar('\n');
	}
	putchar('\n');
}

unsigned char *encode_state() {
	statetype v=0;
	int i,j,k;
	/* find man: count number of floor (dead or live) before man */
	for(v=j=0;j<info.y;j++) for(i=0;i<info.x;i++) {
		if(cur.map[i][j]=='@') goto foundman;
		else if(cur.map[i][j]=='$') continue;
		else if(info.smap[i][j]=='#') continue;
		v++;
	}
foundman:
	/* generate permutation for live cells only (floor and blocks */
	counts[0]=counts[1]=plen=0;
	for(k=0;k<info.lfloor;k++) {
		i=info.id2x[k];
		j=info.id2y[k];
		if(cur.map[i][j]==' ' || cur.map[i][j]=='@') counts[0]++,multiset[plen++]=0;
		else if(cur.map[i][j]=='$') counts[1]++,multiset[plen++]=1;
	}
	v+=permrank()*(info.floor-info.blocks);
	v=v*5+cur.playerdir;
	return getptr(v);
}

void decode_state(unsigned char *p) {
	statetype v=getval(p);
	int i,j,k,w,l;
	/* clear map */
	for(i=0;i<info.floor;i++) cur.map[info.idx[i]][info.idy[i]]=' ';
	/* extract player dir */
	cur.playerdir=v%5; v/=5;
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
		cur.map[i][j]=multiset[l++]?'$':' ';
	}
	for(j=0;j<info.y;j++) for(i=0;i<info.x;i++) {
		if(info.smap[i][j]=='#' || cur.map[i][j]=='$') continue;
		if(w--<1) {
			cur.map[i][j]='@';
			goto manplaced;
		}
	}
manplaced:;
}

int won() {
	int i,j;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(info.smap[i][j]=='.' && cur.map[i][j]!='$') return 0;
	if(info.goalx>-1 && info.goaly>-1 && cur.map[info.goalx][info.goaly]!='@') return 0;
	return 1;
}

/* check for 2x2 deadlock with blocks+wall */
static int bad2x2v2() {
	for(int i=0;i<info.x-1;i++) for(int j=0;j<info.y-1;j++) {
		/* no blocks, no deadlock */
		if(cur.map[i][j]!='$' && cur.map[i+1][j]!='$' && cur.map[i][j+1]!='$' && cur.map[i+1][j+1]!='$') continue;
		/* insta-reject trivial case with 4 walls */
		if(info.smap[i][j]=='#' && info.smap[i+1][j]=='#' && info.smap[i][j+1]=='#' && info.smap[i+1][j+1]=='#') continue;
		int badblock=0;
		/* every cell in 2x2 must have block or wall and at least one block not on goal */
		if(info.smap[i][j]=='#');
		else if(cur.map[i][j]=='$') {
			if(info.smap[i][j]!='.') badblock++;
		} else continue;
		if(info.smap[i+1][j]=='#');
		else if(cur.map[i+1][j]=='$') {
			if(info.smap[i+1][j]!='.') badblock++;
		} else continue;
		if(info.smap[i][j+1]=='#');
		else if(cur.map[i][j+1]=='$') {
			if(info.smap[i][j+1]!='.') badblock++;
		} else continue;
		if(info.smap[i+1][j+1]=='#');
		else if(cur.map[i+1][j+1]=='$') {
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
static int badnhor1() {
	for(int i=0;i<info.x-2;i++) for(int j=0;j<info.y-1;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i][j]!='#' || info.smap[i+2][j+1]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur.map[i+1][j]!='$' || cur.map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i+1][j]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

/* check for  $#
             #$
*/
static int badnhor2() {
	for(int i=0;i<info.x-2;i++) for(int j=0;j<info.y-1;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i][j+1]!='#' || info.smap[i+2][j]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur.map[i+1][j]!='$' || cur.map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i+1][j]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

/* check for #
             $$
              #
*/
static int badnver1() {
	for(int i=0;i<info.x-1;i++) for(int j=0;j<info.y-2;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i][j]!='#' || info.smap[i+1][j+2]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur.map[i][j+1]!='$' || cur.map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i][j+1]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

/* check for  #
             $$
             #
*/
static int badnver2() {
	for(int i=0;i<info.x-1;i++) for(int j=0;j<info.y-2;j++) {
		/* walls not in place, deadlock not possible */
		if(info.smap[i+1][j]!='#' || info.smap[i][j+2]!='#') continue;
		/* blocks not in place, deadlock not possible */
		/* if any of there were walls, the block would be on a dead space and
		   the state would be rejected earlier */
		if(cur.map[i][j+1]!='$' || cur.map[i+1][j+1]!='$') continue;
		/* reject if one of the blocks is not on goal */
		if(info.smap[i][j+1]!='.' || info.smap[i+1][j+1]!='.') return 1;
	}
	return 0;
}

static int deadpos2() {
	/* check for 2x2 configurations of wall/block where >=1 block is not on goal */
	if(bad2x2v2()) return 1;
	/* check for N-pattern */
	if(!options.skipndeadlock) {
		if(badnhor1()) return 1;
		if(badnhor2()) return 1;
		if(badnver1()) return 1;
		if(badnver2()) return 1;
	}
	return 0;
}

void visit_neighbours() {
	int cx=0,cy=0,i,j,d,x2,y2,x3,y3,olddir=cur.playerdir,dl,dr;
	int x2a,x2aa,y2a,y2aa;
	/* find man */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur.map[i][j]=='@') cx=i,cy=j;
	for(d=0;d<4;d++) {
		dl=(d+3)&3; dr=(d+1)&3;
		cur.playerdir=d;
		x2=cx+dx[d]; y2=cy+dy[d];
		if(x2<0 || y2<0 || x2>=info.x || y2>=info.y || info.smap[x2][y2]=='#') continue;
		if(cur.map[x2][y2]==' ') {
			/* move man */
			cur.map[cx][cy]=' ';
			cur.map[x2][y2]='@';
			if(!deadpos2()) add_child(encode_state());
			/* block slap left */
			x2a=cx+dx[dl]; y2a=cy+dy[dl];
			x2aa=x2a+dx[dl]; y2aa=y2a+dy[dl];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur.map[x2a][y2a]=='$' && cur.map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur.map[x2a][y2a]=' '; cur.map[x2aa][y2aa]='$';
				if(!deadpos2()) add_child(encode_state());
				cur.map[x2a][y2a]='$'; cur.map[x2aa][y2aa]=' ';
			}
			/* block slap right */
			x2a=cx+dx[dr]; y2a=cy+dy[dr];
			x2aa=x2a+dx[dr]; y2aa=y2a+dy[dr];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur.map[x2a][y2a]=='$' && cur.map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur.map[x2a][y2a]=' '; cur.map[x2aa][y2aa]='$';
				if(!deadpos2()) add_child(encode_state());
				cur.map[x2a][y2a]='$'; cur.map[x2aa][y2aa]=' ';
			}
			cur.map[cx][cy]='@';
			cur.map[x2][y2]=' ';
		} else if(cur.map[x2][y2]=='$') {
			x3=x2+dx[d]; y3=y2+dy[d];
			if(x3<0 || y3<0 || x3>=info.x || y3>=info.y || info.smap[x3][y3]=='#' || info.smap[x3][y3]=='d' || cur.map[x3][y3]!=' ') continue;
			/* push block */
			cur.map[cx][cy]=' ';
			cur.map[x2][y2]='@';
			cur.map[x3][y3]='$';
			if(!deadpos2()) add_child(encode_state());
			/* block slap left */
			x2a=cx+dx[dl]; y2a=cy+dy[dl];
			x2aa=x2a+dx[dl]; y2aa=y2a+dy[dl];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur.map[x2a][y2a]=='$' && cur.map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur.map[x2a][y2a]=' '; cur.map[x2aa][y2aa]='$';
				if(!deadpos2()) add_child(encode_state());
				cur.map[x2a][y2a]='$'; cur.map[x2aa][y2aa]=' ';
			}
			/* block slap right */
			x2a=cx+dx[dr]; y2a=cy+dy[dr];
			x2aa=x2a+dx[dr]; y2aa=y2a+dy[dr];
			if(olddir==d && x2aa>-1 && x2aa<info.x && y2aa>-1 && y2aa<info.y && cur.map[x2a][y2a]=='$' && cur.map[x2aa][y2aa]==' ' && info.smap[x2aa][y2aa]!='d') {
				cur.map[x2a][y2a]=' '; cur.map[x2aa][y2aa]='$';
				if(!deadpos2()) add_child(encode_state());
				cur.map[x2a][y2a]='$'; cur.map[x2aa][y2aa]=' ';
			}
			cur.map[cx][cy]='@';
			cur.map[x2][y2]='$';
			cur.map[x3][y3]=' ';
		}
	}
}
