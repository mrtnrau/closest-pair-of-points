# ToDo

## Misc:

## Section: Introduction

* Add subsecton describing used Isabelle notation (reference Braun paper)
* Create AFP entry with both verified versions
* Add link to AFP entry

## Section: Closest Pair Algorithm

## Section: Implementation and Functional Correctness

## Section: Time Complexity Proof

* Mention additional work: length, filter, split_at, merge, msort, closest_pair_bf, find_closest_pair, combine
* Describe t_closest_pair_rec
* In principle recurrence solvable with master theorem
* This is also possible in Isabelle: Master Theorem and Landau Notation by Manuel Eberl
  --> automatic closest_pair_rec_recurrence
* Connect timing function with recurrence relation
    1. bigo_measure_trans
    2. t_closest_pair_rec_conv_closest_pair_rec_cost
    3. t_closest_pair_rec_bigo
    4. t_closest_pair_bigo

## Section: Alternative Implementations
* Add explanation of Cormen et al. original approach instead of merging along the way
* Introduce hardcoded approach from Algorihm Design textbook (basis of BA)
* Introduce alternative two list implementation by Bentley and Shamos
* AFP entry provides both formalizations
* (Mention Qi Ge et al. paper which reduces #points (not needed for current approach))

## Section: Executable Code

* Introduce the problems with current of exported code
    1. Distance computations not minimized (Refinement Framework ...)
    2. Code equations for dist and float (Section 2 footnote)
    3. Stackoverflow,
* Isabelle code_unfold for stackoverflow with auxiliary lemmas for length, filter, rev, split_at and merge
* Squared Euclidean distance
* Show final find_closest_code
* Combine_code excert with more efficient filter
* Present empirical test data as complement to theoretical running time
  and point out overhead to handwritten implementations

## Section: Conclusion
* Acknowledgements?
