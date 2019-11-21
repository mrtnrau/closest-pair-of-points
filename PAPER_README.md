document:
  Contains all the latex files. The main file needs to be called root.tex.
  Curently the style files are for Springer LNCS proceedings.

mk:
 runs Isabelle to produce the tex file(s).
 Isabelle also triggers the latex run.
 The -v option causes the location of the generated pdf file to be output
 It executs 'isabelle' which should be the one of Isabelle 2019.

ROOT:
  Two sessions: Paper_Base contains the proofs, Paper the text.
  The two sessions speed things up if the proofs have not changed.
  All the files needed to produce the document (typically all the files in
  directory document) need to be listed under document_files.

For more information also read "LaTeX sugar for Isabelle Documents"
from the Isabelle Documentation panel in jedit.

Running isabelle on the thy files:

isabelle jedit -d . <thy file name(s)>
