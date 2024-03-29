/* plank.c: solve plank puzzles
   copyright (c) 2016 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "solver.h"

#define MAXPL 50  /* max number of planks */
#define MAXST 100 /* max number of stumps */
#define MAX 33    /* max map x,y size */
#define MAXBR MAX*MAX*2 /* max number of bridge spots */

typedef unsigned long long statetype;

int dx[]={1,0,-1,0};
int dy[]={0,1,0,-1};

/* static info about instance */
/* all coordinates are non-doubled! to convert to ascii map, multiply by 2 */
static struct static_s {
	int x,y;             /* map size (NOT doubled) */
	int goalx,goaly;     /* man goal */
	int planks;          /* number of planks */
	int planklen[MAXPL]; /* number of planks by length */
	int stumps;          /* number of stumps */
	int stumpx[MAXST];   /* x-coordinates for stumps */
	int stumpy[MAXST];   /* y-coordinates */
	int stumpix[MAX][MAX]; /* reverse lookup: find stump index, given coordinate */

	/* list of possible stump bridges by length */
	int bridgen[MAX];    /* number of bridges by plank length */
	int bx[MAX][MAXBR];  /* x-coordinate of bridge */
	int by[MAX][MAXBR];  /* y-coordinate of bridge */
	int bd[MAX][MAXBR];  /* direction of bridge (0=right, 1=down) */

	statetype dsize;     /* domain size (number of states) */
	int slen;            /* number of bytes in state */
} info;

/* TODO solver options */

static struct state_s {
	char map[MAX*2-1][MAX*2-1];
	int inventory;       /* length of plank in inventory, 0=nothing */
	int manpos;          /* man position (index into stump array) */
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

/* start of plank puzzle routines */

/* find length of plank starting from stump at x,y, going in direction
   dx,dy. length 0 means no plank there */
static int scanplank(int x,int y,int d,char z,int thr) {
	int len=1;
	x=(x*2+dx[d]);
	y=(y*2+dy[d]);
	while(x<info.x*2-1 && y<info.y*2-1 && cur[thr].map[x][y]==z) {
		x+=dx[d]; y+=dy[d];
		len++;
	}
	return len/2;
}

static int isstump(char c) {
	return c=='*' || c=='S' || c=='T';
}

static int isbridge(char c) {
	return c=='-' || c=='|';
}

/* find length of bridge starting at x,y (not doubled),
   going in direction d (look up in dx,dy) */
/* return -1 if no bridge possible */
static int scanbridge(int x,int y,int d,int thr) {
	int len=1;
	x=(x+dx[d])*2; y=(y+dy[d])*2;
	while(x>=0 && y>=0 && x<info.x*2-1 && y<info.y*2-1) {
		if(isstump(cur[thr].map[x][y])) return len;
		x+=dx[d]*2;
		y+=dy[d]*2;
		len++;
	}
	return -1;
}

/* draw bridge on current state map */
/* return 0 (failed) if this bridge tried to overlap */
static int drawbridge(int x1,int y1,int d,int thr) {
	char c=(d==0?'-':'|');
	int x=x1*2+dx[d],y=y1*2+dy[d];
	/* check if bridge exists) */
	while(!isstump(cur[thr].map[x][y])) {
		if(isbridge(cur[thr].map[x][y])) return 0;
		x+=dx[d]; y+=dy[d];
	}
	x=x1*2+dx[d]; y=y1*2+dy[d];
	while(!isstump(cur[thr].map[x][y])) {
		cur[thr].map[x][y]=c;
		x+=dx[d]; y+=dy[d];
	}
	return 1;
}

void domain_init() {
	char s[1000],t[100];
	int i,j;
	int starts,goals;
	statetype z;
	/* permutation init */
	for(i=0;i<MAXPASCAL;i++) {
		pas[i][0]=pas[i][i]=1;
		for(j=1;j<i;j++) pas[i][j]=pas[i-1][j]+pas[i-1][j-1];
	}
	info.x=info.y=0;
	cur[0].inventory=0;
	while(fgets(s,998,stdin)) {
		if(s[0]=='#') continue; /* non-map line starting with #: comment */
		if(s[0]==13 || s[0]==10) continue; /* blank line */
		sscanf(s,"%98s",t);
		if(!strcmp(t,"size")) {
			if(2!=sscanf(s,"size %d %d",&info.x,&info.y)) error("wrong parameters for size");
			if(info.x>MAX || info.y>MAX) error("map too large, increase MAX and recompile");
		} else if(!strcmp(t,"map")) {
			for(j=0;j<info.y*2-1;j++) {
				if(!fgets(s,998,stdin)) {
					for(;j<info.y*2-1;j++) {
						for(i=0;i<info.x*2-1;i++) cur[0].map[i][j]=' ';
						cur[0].map[i][j]=0;
					}
					goto mapended;
				}
				for(i=0;i<info.x*2-1 && s[i] && s[i]!=13 && s[i]!=10;i++) cur[0].map[i][j]=s[i];
				for(;i<info.x*2-1;i++) cur[0].map[i][j]=' ';
				cur[0].map[i][j]=0;
			}
		} else {
			printf("ignored unknown command %s\n",t);
		}
	}
mapended:
	/* dumb sanity-check map */
	starts=0; goals=0;
	info.goalx=info.goaly=-1;
	for(int i=0;i<info.x;i++) for(int j=0;j<info.y;j++) {
		char c=cur[0].map[i*2][j*2];
		if(c!=' ' && c!='*' && !isstump(c) && c!='-' && c!='|') error("illegal stump");
		if(c=='S') starts++;
		if(c=='T') {
			info.goalx=i;
			info.goaly=j;
			goals++;
		}
	}
	if(starts!=1) error("there must be exactly 1 start position");
	if(goals!=1) error("there must be exactly 1 goal");
	/* count planks of each length */
	for(int i=0;i<info.x;i++) for(int j=0;j<info.y;j++) info.stumpix[i][j]=-1;
	for(i=0;i<MAX;i++) info.planklen[i]=0;
	info.stumps=0;
	for(i=0;i<info.x;i++) for(int j=0;j<info.y;j++) {
		if(isstump(cur[0].map[i*2][j*2])) {
			/* preserve man pos */
			if(cur[0].map[i*2][j*2]=='S') cur[0].manpos=info.stumps;
			/* convert start and end stumps to generic ones */
			cur[0].map[i*2][j*2]='*';
			info.stumpx[info.stumps]=i;
			info.stumpy[info.stumps]=j;
			info.stumpix[i][j]=info.stumps++;
			info.planklen[scanplank(i,j,0,'-',0)]++;
			info.planklen[scanplank(i,j,1,'|',0)]++;
		}
	}
	/* find all possible bridges */
	for(i=0;i<MAX;i++) info.bridgen[i]=0;
	for(i=0;i<info.x;i++) for(j=0;j<info.y;j++) if(isstump(cur[0].map[i*2][j*2])) for(int d=0;d<2;d++) {
		/* follow bridge and find length */
		int len=scanbridge(i,j,d,0);
		if(len>-1) {
			info.bx[len][info.bridgen[len]]=i;
			info.by[len][info.bridgen[len]]=j;
			info.bd[len][info.bridgen[len]++]=d;
		}
	}
	print_state(0);
	/* calculate state space size */
	/* for each bridge size: there are (n choose k) ways to place k bridges,
	   where n is the number of bridge spots + 1 for inventory.
	   man can be on any stump */
	double dsize=info.stumps;
	info.dsize=info.stumps;
//	printf("stumps %d\n",info.stumps);
	for(i=1;i<MAXPL;i++) if(info.planklen[i]>0) {
		if(info.bridgen[i]<info.planklen[i]) error("sanity error, too few bridge spots");
		dsize*=doublenck(info.bridgen[i]+1,info.planklen[i]);
		info.dsize*=pas[info.bridgen[i]+1][info.planklen[i]];
//		printf("combinations for len %d: (%d choose %d) = %I64d\n",i,info.bridgen[i]+1,info.planklen[i],pas[info.bridgen[i]+1][info.planklen[i]]);
	}
	if(fabs(dsize-info.dsize)/dsize>0.001) error("state space too large");
	for(info.slen=0,z=info.dsize;z;info.slen++,z>>=8);
}

unsigned char *domain_size() {
	return getptr(info.dsize-1,0);
}

int state_size() {
	return info.slen;
}

void print_state(int thr) {
	int i,j;
	for(j=0;j<info.y*2-1;j++) {
		for(i=0;i<info.x*2-1;i++) {
			if(i==info.stumpx[cur[thr].manpos]*2 && j==info.stumpy[cur[thr].manpos]*2) putchar('@');
			else putchar(cur[thr].map[i][j]);
		}
		putchar('\n');
	}
	printf("inventory: ");
	if(cur[thr].inventory) printf("length %d plank\n",cur[thr].inventory);
	else puts("nothing");
	putchar('\n');
}

unsigned char *encode_state(int thr) {
	statetype v=0;
	/* encode planks */
	for(int i=1;i<MAXPL;i++) if(info.planklen[i]>0) {
		counts[thr][0]=counts[thr][1]=plen[thr]=0;
		for(int j=0;j<info.bridgen[i];j++) {
			if(isbridge(cur[thr].map[info.bx[i][j]*2+dx[info.bd[i][j]]][info.by[i][j]*2+dy[info.bd[i][j]]])) {
				multiset[thr][plen[thr]++]=1;
				counts[thr][1]++;
			} else {
				multiset[thr][plen[thr]++]=0;
				counts[thr][0]++;
			}
		}
		if(i==cur[thr].inventory) {
			multiset[thr][plen[thr]++]=1;
			counts[thr][1]++;
		} else {
			multiset[thr][plen[thr]++]=0;
			counts[thr][0]++;
		}
		v*=pas[plen[thr]][counts[thr][1]]; v+=permrank(thr);
	}
	/* man position */
	/* TODO normalize man position with bfs/dfs (will reduce iteration size) */
	/* TODO prioritize goal position when reachable (or won() won't work) */
	v*=info.stumps; v+=cur[thr].manpos;
	if(v>=info.dsize) printf("sanity error, state value exceeds state space size\n");
	return getptr(v,thr);
}

void decode_state(unsigned char *p,int thr) {
	statetype v=getval(p);
	cur[thr].inventory=0;
	/* erase all planks from ascii map */
	for(int i=0;i<info.x*2-1;i++) for(int j=0;j<info.y*2-1;j++) {
		char c=cur[thr].map[i][j];
		if(c=='|' || c=='-') cur[thr].map[i][j]=' ';
	}
	/* man pos */
	cur[thr].manpos=v%info.stumps; v/=info.stumps;
	/* decode planks */
	for(int i=MAXPL-1;i;i--) if(info.planklen[i]>0) {
		counts[thr][0]=info.bridgen[i]+1-info.planklen[i];
		counts[thr][1]=info.planklen[i];
		plen[thr]=counts[thr][0]+counts[thr][1];
		permunrank(v%pas[plen[thr]][counts[thr][1]],thr); v/=pas[plen[thr]][counts[thr][1]];
		for(int j=0;j<info.bridgen[i];j++) if(multiset[thr][j]) {
			/* draw ascii bridge */
			if(!drawbridge(info.bx[i][j],info.by[i][j],info.bd[i][j],thr)) puts("sanity error, overlapping bridge");
		}
		if(multiset[thr][plen[thr]-1]) cur[thr].inventory=i;
	}
}

int won(int thr) {
	return info.goalx==info.stumpx[cur[thr].manpos] && info.goaly==info.stumpy[cur[thr].manpos];
}

static char vis[MAX][MAX];
static int q[MAX*MAX];
static int qs,qe;

void visit_neighbours(int thr) {
	/* try all man moves with bfs */
	memset(vis,0,sizeof(vis));
	qs=qe=0;
	/* push man pos */
	q[qe++]=cur[thr].manpos;
	vis[info.stumpx[cur[thr].manpos]][info.stumpy[cur[thr].manpos]]=1;
	while(qs<qe) {
		cur[thr].manpos=q[qs++];
		int curx=info.stumpx[cur[thr].manpos];
		int cury=info.stumpy[cur[thr].manpos];
		if(cur[thr].inventory) {
			/* try all ways of dropping held bridge */
			for(int d=0;d<4;d++) {
				int x2=curx*2+dx[d];
				int y2=cury*2+dy[d];
				if(x2<0 || y2<0 || x2>=info.x*2-1 || y2>=info.y*2-1) continue;
				if(isbridge(cur[thr].map[x2][y2]),thr) continue;
				/* scan for stump and check if length equals bridge length */
				x2=curx+dx[d];
				y2=cury+dy[d];
				int len=1;
				while(x2>=0 && y2>=0 && x2<info.x && y2<info.y && !isstump(cur[thr].map[x2*2][y2*2])) {
					x2+=dx[d];
					y2+=dy[d];
					len++;
				}
				if(x2<0 || y2<0 || x2>=info.x || y2>=info.y) continue;
//				printf("at %d %d dir %d, found bridge of length %d\n",curx,cury,d,len);
				if(len!=cur[thr].inventory) continue;
				/* bridge is ok */
				struct state_s bak=cur[thr];
				cur[thr].inventory=0;
				if(drawbridge(curx,cury,d,thr)) {
//					puts("dropped bridge");
//					print_state();
					add_child(encode_state(thr),thr);
				}
				cur[thr]=bak;
			}
		} else {
			/* try all ways of picking up a bridge next to player */
			for(int d=0;d<4;d++) {
				int x2=curx*2+dx[d];
				int y2=cury*2+dy[d];
				if(x2<0 || y2<0 || x2>=info.x*2-1 || y2>=info.y*2-1) continue;
				if(!isbridge(cur[thr].map[x2][y2])) continue;
				int len=scanbridge(curx,cury,d,thr);
				if(len<0) printf("sanity error\n");
				struct state_s bak=cur[thr];
				/* remove bridge from ascii and put it in inventory */
				cur[thr].inventory=len;
				while(isbridge(cur[thr].map[x2][y2])) {
					cur[thr].map[x2][y2]=' ';
					x2+=dx[d];
					y2+=dy[d];
					if(x2<0 || y2<0 || x2>=info.x*2-1 || y2>=info.y*2-1) puts("sanity error while removing bridge");
				}
				if(!isstump(cur[thr].map[x2][y2])) puts("sanity error, remove bridge didn't end up at stump");
//				puts("picked up bridge");
//				print_state();
				add_child(encode_state(thr),thr);
				cur[thr]=bak;
			}
		}
		/* move over bridges to nearby stumps */
		for(int d=0;d<4;d++) {
			int x2=curx*2+dx[d];
			int y2=cury*2+dy[d];
			if(x2<0 || y2<0 || x2>=info.x*2-1 || y2>=info.y*2-1) continue;
			if(!isbridge(cur[thr].map[x2][y2])) continue;
			/* find endpoint of bridge */
			int len=scanbridge(curx,cury,d,thr);
			if(len<0) printf("sanity error\n");
			x2=curx+dx[d]*len;
			y2=cury+dy[d]*len;
			if(!isstump(cur[thr].map[x2*2][y2*2])) printf("no stump\n");
			if(vis[x2][y2]) continue;
			vis[x2][y2]=1;
			int next=info.stumpix[x2][y2];
			if(next<0) puts("sanity error, illegal destination across bridge");
			q[qe++]=next;
		}
	}
}
