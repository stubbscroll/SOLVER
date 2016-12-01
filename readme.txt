a framework for state space graph search

the goal is to provide state-of-the-art implementations of search algorithms
that can search in huge graphs while using little memory per node. the point of
the framework is to separate the search algorithm from the domain specific move
generator and make it easier to try different algorithms on different domains.

algorithms implemented:
- bfs - simple breadth-first search (state space must fit in memory)
- bfsd - bfs with delayed duplicate detection (in progress)
- bfsdu - bfs (for undirected graphs) with delayed duplicate detection

domains implemented:
- npuzzle (undirected, bipartite) - (mn-1)-puzzle (aka 15-puzzle)
- soko - simple sokoban, no checking for dead states etc
- soko2 - sokoban, checks for simple deadlocks, better encoding
- soko3 - sokoban, same as soko2 but with block slapping (feature in chip's
  challenge for lynx and steam)

puzzle instances:
- npuzzle/ - puzzles for n-puzzle
- soko/ - puzzles for soko, soko2, soko3

to come later:
- improved bfs: vbyte compression, disk swapping
- a* (including sophisticated variants)
- solution output for bfsd and bfsdu
- more domains (eligible games are typically pspace-complete and usually
  involves finding a sequence of moves leading to a goal state)
- maybe i'll write something, i think the combination of state space search,
  tight state encoding and delta compression is rather novel

future work:
- bfsd is rather slow, as it uses improvements created specifically for bfsdu,
  and they are not a good fit for the case where we need to store all visited
  positions. find new improvements that are good for directed graphs. maybe
  delay the delayed duplicate detection for several generations when the size
  of the current generation is low compared to the number of all visited
  positions?

to compile (in windows):

make.bat

to compile (in linux/macintosh etc):

run the contents of make.bat
