/* improved version of bfs.c
   - supports directed graphs
   - store list of visited states instead of marking them in array. we need to
     store all visited nodes since graph is directed
   - delayed duplicate detection: check for duplicates in batches - after we
     generate all moves from an iteration or we run out of memory. more efficient
     since we only need one linear scan of previously visited states per batch
   - store states explicitly, list of visited states is sorted
   - no size restriction on state size
   - search gives up when the two previous iterations + iteration under
     generation cannot all fit in memory
   * implement in later versions: disk swapping, vbyte compression
*/

#include <stdio.h>
#include <stdlib.h>
#include "solver.h"

static struct bfs_s {
	unsigned char *b;             /* memory area */
	long long blen;               /* length of memory area in bytes */
	long long bblen;              /* length of memory area in number of states */

	int slen;                     /* length of state in bytes */
} bfs;

static void error(char *s) { puts(s); exit(1); }

void solver_init() {
	bfs.slen=state_size();
}

void add_child(unsigned char *p) {
}

void solver_bfs() {
}

int main(int argc,char **argv) {
	domain_init();
	solver_init();
	solver_bfs();
	return 0;
}
