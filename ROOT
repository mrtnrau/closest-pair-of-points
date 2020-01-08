session Proofs in Proofs = Akra_Bazzi +
  theories
    "Closest_Pair"
    "Closest_Pair_Alternative"
  document_files
    "root.tex"
    "root.bib"

session Paper = Proofs +
  options [document = pdf, show_question_marks = false, names_short = true,
    document_output = "generated"]
   (* All the tex files are dumped into directory "generated" and can be
      processed separately if needed. *)
  theories [document = false]
    (* Alternatively you can take a local copy of LaTeXsugar and modify it: *)
    "OptionalSugarLocal"
  theories
    Paper
  document_files
    "root.tex"
    "root.bib"
    (* Additional files needed to produce the document, typically latex style files: *)
    "llncs.cls"
    "splncs04.bst"
