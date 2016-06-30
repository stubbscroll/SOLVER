a framework for state space graph search

the goal is to provide state-of-the-art implementations of search algorithms
that can search in huge graphs while using little memory per node. the point of
the framework is to separate the search algorithm from the domain specific move
generator and make it easier to try different algorithms on different domains.

algorithms implemented:
- bfs - simple breadth-first search
- bfsd - bfs with delayed duplicate detection (TODO)
- bfsdu - bfs (for undirected graphs) with delayed duplicate detection (in
          progress)

domains implemented:
- npuzzle - (mn-1)-puzzle (aka 15-puzzle)
- soko - simple sokoban, no checking for dead states etc
- soko2 - sokoban, checks for simple deadlocks, better encoding

to come later:
- more sophisticated versions of bfs, with delayed duplicate detection, vbyte
  compression, disk swapping, special versions for undirected graphs
- a* (including sophisticated variants)
- more domains, like 15-puzzle and maybe other pspace-complete games
- maybe i'll write something, i think the combination of state space search and
  vbyte compression is rather novel

to compile (in windows):

make.bat

to compile (in linux/macintosh etc):

run the contents of make.bat
