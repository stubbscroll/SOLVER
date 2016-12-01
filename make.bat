@rem make all eligible combinations
gcc -o soko-bfs.exe bfs.c soko.c -O3 -Wall -std=c99
gcc -o soko-bfsd.exe bfsd.c soko.c -O3 -Wall -std=c99
gcc -o soko2-bfs.exe bfs.c soko2.c -O3 -Wall -std=c99
gcc -o soko2-bfsd.exe bfsd.c soko2.c -O3 -Wall -std=c99
gcc -o soko3-bfs.exe bfs.c soko3.c -O3 -Wall -std=c99
gcc -o soko3-bfsd.exe bfsd.c soko3.c -O3 -Wall -std=c99
gcc -o npuzzle-bfs.exe bfs.c npuzzle.c -O3 -Wall -std=c99
gcc -o npuzzle-bfsd.exe bfsd.c npuzzle.c -O3 -Wall -std=c99
gcc -o npuzzle-bfsdu.exe bfsdu.c npuzzle.c -O3 -Wall -std=c99
