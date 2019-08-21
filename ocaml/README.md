# Closest Pair of Points

This project contains three implementations of the Closest Pair of Points algorithm.

* mutable: an imperative implementation
* immutable: a functional implementation
* verified: the exported and verified code of Isabelle

Run the benchmarks with ```make iterations to_file from to by```. E.g. ```make 10 false 1000 10000 1000``` runs the benchmarks 10 times for input sizes starting at 1000 points, increasing by steps of 1000 points to 10000 points and prints the averaged output to stdout.