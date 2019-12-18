session Proofs = "HOL-Analysis" +
  sessions
    "Landau_Symbols"
    "Akra_Bazzi"
  theories
    (* Alternatively you can take a local copy of LaTeXsugar and modify it: *)
    "OptionalSugarLocal"
    "Proofs/Closest_Pair"
    "Proofs/Closest_Pair_Time"
    "Proofs/Closest_Pair_Code"

session Paper = Proofs +
  options [document = pdf, show_question_marks = false, names_short = true,
    document_output = "generated"]
   (* All the tex files are dumped into directory "generated" and can be
      processed separately if needed. *)
  theories
    Paper
  document_files
    "root.tex"
    "root.bib"
    (* Additional files needed to produce the document, typically latex style files: *)
    "llncs.cls"
    "splncs04.bst"
