a modular framework for state space graph search

the goal is to provide state-of-the-art implementations of search algorithms
that can search in huge graphs while using little memory per node. the point of
the framework is to separate the search algorithm from the domain specific move
generator and make it easier to try different algorithms on different domains.

algorithms implemented:
- bfs - simple breadth-first search (state space must fit in memory)
- bfsd - bfs with delayed duplicate detection (in progress)
- bfsdu - bfs (for undirected graphs) with delayed duplicate detection
- bfs2 - breadth-first search with disk swapping (requires bit array of state
  space in memory, but it's divided into many parts and allocated lazily)
- bfs2p - multithreaded version of bfs2 (speedup is not so good currently,
  around 3-5 threads is fastest, more than that is slower)

domains implemented:
- npuzzle (undirected, bipartite) - (mn-1)-puzzle (aka 15-puzzle)
- chip1 - sokoban with popup walls and force floors
- soko (bipartite) - simple sokoban, no checking for dead states etc
- soko2 (bipartite) - sokoban, checks for simple deadlocks, better encoding
- soko-lx (bipartite) - sokoban, same as soko2 but with block slapping
  (feature in chip's challenge for lynx and steam)
- plank (undirected) - plank puzzle

puzzle instances:
- npuzzle/ - puzzles for n-puzzle
- chip/ - puzzles for chip1
- soko/ - puzzles for soko, soko2, soko-lx
- plank/ - puzzles for plank

to come later:
- improved bfs: vbyte compression, search from both directions (requires
  backwards move generator and domains with few goal states)
- a* (including sophisticated variants, see a certain paper on solving atomix)
- solution output for bfsd and bfsdu
- more domains (eligible games are typically pspace-complete and usually
  involves finding a sequence of moves leading to a goal state)
- maybe i'll write something, i think the combination of state space search,
  tight state encoding and delta compression is rather novel
- bfs2p: the routine that finds neighbouring nodes sucks for parallelization,
  rethink it
- bfs2p: i should really do profiling to find out where the parallelization sucks

future work:
- bfsd is rather slow, as it uses improvements created specifically for bfsdu,
  and they are not a good fit for the case where we need to store all visited
  positions. find new improvements that are good for directed graphs. maybe
  delay the delayed duplicate detection for several generations when the size
  of the current generation is low compared to the number of all visited
  positions?
- bfs2 is much better than bfsd, but the memory requirements are pretty hefty.
  find further improvements, that would allow us to search farther in graphs
  where most states are unreachable

inspiration:
- if you want to improve your single-agent search algorithm skills,
  read the papers on the 15-puzzle written by Richard Korf and Jonathan
  Schaeffer. they are a treasure trove. also, work on other interesting
  projects and discover surprising synergies.

to compile (in windows):

make.bat

to compile (in linux/macintosh etc):

run the contents of make.bat
