/* solver.h: header file for graph search framework
   copyright (c) 2016 by stubbscroll, under the GNU general public license v3.
   no warranty. see LICENSE.txt for details.
*/
#ifndef _SOLVER_H
#define _SOLVER_H

#define MAXTHR 1000 // max number of threads

/* contract
   - never assume that the pointers to encoded states are valid after new calls
     to anywhere! make a local copy if needed
*/

/* domain functions **********************************************************/

/* obtain instance to be searched, do necessary initialization and set as
   current state */
void domain_init(void);

/* return state space size-1
   the reason for -1 to be able to return state space sizes of 2^k
   byte 0 to n-1: number in little endian format (which is what my old vbyte
     solvers use)
   n is state_size() for the given instance */
unsigned char *domain_size(void);

/* return size in bytes of encoded state */
int state_size(void);

/* return encoded version of current state */
unsigned char *encode_state(int);

/* decode given state and set as current state */
void decode_state(unsigned char *,int);

/* print current state */
void print_state(int);

/* visit all neighbouring states from current state */
/* it must call add_child(ptr) for each generated neighbour where ptr is the
   encoded state */
void visit_neighbours(int);

/* return 1 if current state is a win state, 0 otherwise */
int won(int);

/* TODO
   - a* heuristic (calculate distance to goal (no overestimate))
*/

/* solver functions **********************************************************/

void add_child(unsigned char *,int);

#endif
