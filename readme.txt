a framework for state space graph search

the goal is to provide state-of-the-art implementations of search algorithms
that can search in huge graphs while using little memory per node.

algorithms implemented:
- bfs - simple breadth-first search

domains implemented:
- soko - simple sokoban, no checking for dead states etc

to come later:
- more sophisticated versions of bfs, with delayed duplicate detection, vbyte
  compression, disk swapping
- a* (including sophisticated variants)

to compile (in windows):

make.bat

to compile (in linux/macintosh etc):

run the contents of make.bat
