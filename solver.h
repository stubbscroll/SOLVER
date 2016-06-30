#ifndef _SOLVER_H
#define _SOLVER_H

#ifdef __MINGW64__
	#define LONG "%I64d"
	#define ULONG "%I64u"
#elif defined (_MSC_VER)
	#define LONG "%I64d"
	#define ULONG "%I64u"
#else
	#define LONG "%lld"
	#define ULONG "%llu"
#endif

/* contract
   - never assume that the pointers to encoded states are valid after new calls
     to anywhere! make a local copy if needed
*/

/* domain functions **********************************************************/

/* obtain instance to be searched, do necessary initialization and set as
   current state */
void domain_init();

/* return state space size
   byte 0 to n-1: number in little endian format (which is what my old vbyte
     solvers use)
   n is state_size() for the given instance */
unsigned char *domain_size();

/* return size in bytes of encoded state */
int state_size();

/* return encoded version of current state */
unsigned char *encode_state();

/* decode given state and set as current state */
void decode_state(unsigned char *);

/* print current state */
void print_state();

/* visit all neighbouring states from current state */
/* it must call add_child(ptr) for each generated neighbour where ptr is the
   encoded state */
void visit_neighbours();

/* return 1 if current state is a win state, 0 otherwise */
int won();

/* TODO
   - a* heuristic (calculate distance to goal (no overestimate))
*/

/* solver functions **********************************************************/

void add_child(unsigned char *);

#endif
