# HowTo

document:
  Contains all the latex files. The main file needs to be called root.tex.
  Curently the style files are for Springer LNCS proceedings.

mk:
 runs Isabelle to produce the tex file(s).
 Isabelle also triggers the latex run.
 The -v option causes the location of the generated pdf file to be output
 It executs 'isabelle' which should be the one of Isabelle 2019.

ROOT:
  Two sessions: Proofs directory contains the proofs, Paper the text.
  The two sessions speed things up if the proofs have not changed.
  All the files needed to produce the document (typically all the files in
  directory document) need to be listed under document_files.

For more information also read "LaTeX sugar for Isabelle Documents"
from the Isabelle Documentation panel in jedit.

Running isabelle on the thy files:

isabelle jedit -d . <thy file name(s)>

# ToDo

## Misc:
* Local copies of LateXsugar and OptionalSugar result in ambiguous parse trees ???
* General formatting (log, set conversions)
* Quote indentation?

## Section: Introduction

* Add subsecton describing used Isabelle notation (reference Braun paper)
* Create AFP entry with both verified versions (extract common code!)
* Add link to AFP entry

## Section: Closest Pair Algorithm

## Section: Proving Functional Correctness

* Extension 1: Add set_band_filter lemma
* Extension 2: Add explanation of Cormen et al. original approach instead of merging along the way
* Extension 3: Add closest_pair_c0_c1 theorem for completeness

## Section: Proving Running Time

* Refer back to Section 2 and the original time complexity claim
* Explain how everything hinges on the constant running time of find_closest
* State the informal proof using an additional figure which relies on human
  geometrical intuition
* Introduce the approach to verify running time in Isabelle (Braun paper)
  using t_find_closest as an example and show t_find_closest_cnt lemma
* Lead the reader through the Isabelle formalization of the core proof by Cormen et al.
    1. Isabelle basics cbox, cbox_2D lemma
    2. Lemma max_points_is_7 as target lemma
        - max_points_square
        - pigeonhole
        - cbox_max_dist
    3. cost function and bigo_measure_trans and landau notation in Isabelle
    4. obtain the final proof in landau notation
* Mention additional work: length, filter(!), split_at, merge, msort, 
  closest_pair_bf, find_closest_pair, combine (and respective cost definitions)
* Introduce closest_pair_rec_cost definition
    1. Master Theorem by Manuel Eberl --> automatic closest_pair_rec_cost
    2. t_closest_pair_rec_conv_closest_pair_rec_cost
    3. t_closest_pair_rec_bigo
    4. t_closest_pair_bigo
* Wrap up section

## Section: Alternative Implementations and Related Work
* Introduce alternative two list implementation by Bentley and Shamos
* Introduce hardcoded approach from Algorihm Design textbook (basis of BA)
* AFP entry provides both formalizations
* Mention Qi Ge et al. paper which reduces #points (not needed for current approach)
* Other verified geometric algorithms

## Section: Executable Code

* Introduce the problems with current of exported code
    1. Distance computations not minimized (Refinement Framework ...)
    2. Code equations for dist and float (Section 2 footnote)
    3. Stackoverflow,
* Isabelle code_unfold for stackoverflow with auxiliary lemmas for
  length, filter, rev, split_at and merge
* Squared Euclidean distance
* Show final find_closest_code
* Combine_code excert with more efficient filter
* Update ocaml code
* Rerun benchmarks and generate Matlab figure
* Present empirical test data as complement to theoretical running time
  and point out overhead to handwritten implementations

## Section: Conclusion
* Acknowledgements?
