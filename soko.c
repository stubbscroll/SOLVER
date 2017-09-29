/* soko.c: simple sokoban solver
   copyright (c) 2016-2017 by stubbscroll,
   under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
/* sokoban for small-ish puzzles
   - state must fit in unsigned long long
   - simple version that doesn't check for dead states (though the user can
     define cells as such manually)
   usage:
   - read puzzle from standard input
   file format:
   - size x y: set level size
   - goal x y: set man goal position (use if man goal overlaps with block
     or starting position)
   - map: followed by y lines with map data
     - #: wall
     -  : floor
     - @: man
     - $: block
     - _: cell traversable by man, but not by block
     - .: destination
     - *: block starting on destination
     - +: man starting on destination
     - =: man starting on man-only cell
     - g: man goal
   * there are two ways to define man goal. if it's not defined, the puzzle
     is solved when all blocks are on destinations
   state encoding:
   - base (number of floor cells) number where least significant digit is man
     position and the remaining digits are block positions
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "solver.h"

#define MAX 40

static int dx[]={1,0,-1,0};
static int dy[]={0,1,0,-1};

/* static info about instance */
static struct static_s {
	char smap[MAX][MAX]; /* '#':map, ' ':floor, '_':dead cell */
	int idmap[MAX][MAX]; /* floor id, [0, floor-1] */
	int idx[MAX*MAX];    /* reverse id map */
	int idy[MAX*MAX];
	int x,y;             /* map size */
	int goalx,goaly;     /* man goal */
	int blocks;          /* number of blocks (and elements in id-map) */
	int floor;           /* number of floor */
	unsigned long long dsize; /* domain size (number of states) */
	int slen;            /* number of bytes in state */
} info;

static struct state_s {
	char map[MAX][MAX];  /* '$':block, '@':man, ' ':nothing */
} cur;

static void error(char *s) { puts(s); exit(1); }

/* convert pointer-thing to unsigned long long */
static unsigned long long getval(unsigned char *p) {
	unsigned long long n=0;
	int i;
	for(i=0;i<info.slen;i++) n+=((unsigned long long)p[i])<<(i*8);
	return n;
}

/* convert unsigned long long to pointer-thing */
static unsigned char *getptr(unsigned long long v) {
	static unsigned char p[8];
	int i;
	for(i=0;i<info.slen;i++) p[i]=v&255,v>>=8;
	return p;
}

/* read input and populate info and cur */
void domain_init() {
	char s[1000],t[100],c;
	int i,j,men=0,goals=0;
	double dsize;
	info.x=info.y=0;
	info.goalx=info.goaly=-1;
	memset(info.smap,0,sizeof(info.smap));
	memset(cur.map,0,sizeof(cur.map));
	while(fgets(s,998,stdin)) {
		if(s[0]=='#') continue; /* non-map line starting with #: comment */
		sscanf(s,"%98s",t);
		if(!strcmp(t,"size")) {
			if(2!=sscanf(s,"size %d %d",&info.x,&info.y)) error("wrong parameters for size");
			if(info.x>MAX || info.y>MAX) error("map too large, increase MAX and recompile");
		} else if(!strcmp(t,"goal")) {
			if(2!=sscanf(s,"goal %d %d",&info.goalx,&info.goaly)) error("wrong parameters for goal");
			if(info.goalx<0 || info.goaly<0 || info.goalx>=info.x || info.goaly>=info.y) error("man goal outside of map");
		} else if(!strcmp(t,"map")) {
			for(j=0;j<info.y;j++) {
				if(!fgets(s,998,stdin)) error("map ended unexpectedly");
				for(i=0;i<info.x;i++) {
					c=s[i];
					if(c=='#') info.smap[i][j]='#',cur.map[i][j]='#';
					else if(c==' ') info.smap[i][j]=' ',cur.map[i][j]=' ';
					else if(c=='.') info.smap[i][j]='.',cur.map[i][j]=' ';
					else if(c=='$') info.smap[i][j]=' ',cur.map[i][j]='$';
					else if(c=='_') info.smap[i][j]='_',cur.map[i][j]=' ';
					else if(c=='*') info.smap[i][j]='.',cur.map[i][j]='$';
					else if(c=='@') info.smap[i][j]=' ',cur.map[i][j]='@';
					else if(c=='+') info.smap[i][j]='.',cur.map[i][j]='@';
					else if(c=='=') info.smap[i][j]='_',cur.map[i][j]='@';
					else if(c=='g') info.smap[i][j]=' ',cur.map[i][j]=' ',info.goalx=i,info.goaly=j;
					else error("illegal char");
				}
			}
		}
	}
	/* generate id-map */
	memset(info.idmap,-1,sizeof(info.idmap));
	info.floor=info.blocks=0;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) {
		if(info.smap[i][j]==' ' || info.smap[i][j]=='.' || info.smap[i][j]=='_') {
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
	/* check size */
	info.dsize=dsize=1;
	for(i=0;i<=info.blocks;i++) dsize*=info.floor,info.dsize*=info.floor;
	if(dsize>9223372036854775807LL) error("state space too large");
	for(i=8;i;i--) if(((info.dsize>>((i-1)*8))&255)) { info.slen=i; break; }
	printf("loaded sokoban puzzle, state space "ULONG"\n",info.dsize);
}

unsigned char *domain_size() {
	return getptr(info.dsize-1);
}

int state_size() {
	return info.slen;
}

void print_state() {
	int i,j;
	for(j=0;j<info.y;j++) {
		for(i=0;i<info.x;i++) {
			if(cur.map[i][j]==' ' && info.smap[i][j]=='_') putchar('_');
			else putchar(cur.map[i][j]);
		}
		putchar('\n');
	}
	putchar('\n');
}

unsigned char *encode_state() {
	unsigned long long v=0;
	int i,j;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur.map[i][j]=='$') v=v*info.floor+info.idmap[i][j];
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur.map[i][j]=='@') v=v*info.floor+info.idmap[i][j];
	return getptr(v);
}

void decode_state(unsigned char *p) {
	unsigned long long v=getval(p);
	int i,w;
	/* clear map */
	for(i=0;i<info.floor;i++) cur.map[info.idx[i]][info.idy[i]]=' ';
	/* extract man */
	w=v%info.floor; v/=info.floor;
	cur.map[info.idx[w]][info.idy[w]]='@';
	/* extract blocks */
	for(i=0;i<info.blocks;i++) {
		w=v%info.floor; v/=info.floor;
		cur.map[info.idx[w]][info.idy[w]]='$';
	}
}

int won() {
	int i,j;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(info.smap[i][j]=='.' && cur.map[i][j]!='$') return 0;
	if(info.goalx>-1 && info.goaly>-1 && cur.map[info.goalx][info.goaly]!='@') return 0;
	return 1;
}

void visit_neighbours() {
	int cx=0,cy=0,i,j,d,x2,y2,x3,y3;
	/* find man */
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(cur.map[i][j]=='@') cx=i,cy=j;
	for(d=0;d<4;d++) {
		x2=cx+dx[d]; y2=cy+dy[d];
		if(x2<0 || y2<0 || x2>=info.x || y2>=info.y || info.smap[x2][y2]=='#') continue;
		if(cur.map[x2][y2]==' ') {
			/* move man */
			cur.map[cx][cy]=' ';
			cur.map[x2][y2]='@';
			add_child(encode_state());
			cur.map[cx][cy]='@';
			cur.map[x2][y2]=' ';
		} else if(cur.map[x2][y2]=='$') {
			x3=x2+dx[d]; y3=y2+dy[d];
			if(x3<0 || y3<0 || x3>=info.x || y3>=info.y || info.smap[x3][y3]=='#' || cur.map[x3][y3]!=' ' || info.smap[x3][y3]=='_') continue;
			/* push block */
			cur.map[cx][cy]=' ';
			cur.map[x2][y2]='@';
			cur.map[x3][y3]='$';
			add_child(encode_state());
			cur.map[cx][cy]='@';
			cur.map[x2][y2]='$';
			cur.map[x3][y3]=' ';
		}
	}
}
