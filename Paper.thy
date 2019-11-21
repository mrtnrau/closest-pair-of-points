(*<*)
theory Paper
imports
  "Proofs.Proofs"
  "Proofs.Closest_Pair"
  "Proofs.Closest_Pair_Code"
  "Proofs.Closest_Pair_Time"
  "HOL-Library.LaTeXsugar"
  "HOL-Library.OptionalSugar"
begin

lemma find_closest_\<delta>_simp:
  "ps \<noteq> [] \<Longrightarrow> find_closest_\<delta> p \<delta> (p\<^sub>0 # ps) = (
    if \<delta> \<le> snd p\<^sub>0 - snd p then
      p\<^sub>0
    else
      let p\<^sub>1 = find_closest_\<delta> p (min \<delta> (dist p p\<^sub>0)) ps in
      if dist p p\<^sub>0 \<le> dist p p\<^sub>1 then
        p\<^sub>0
      else
        p\<^sub>1
  )"
  apply (cases ps)
   apply (auto simp add: find_closest_\<delta>.simps)
  done

translations
 "p" <= "(case p of (x, y) \<Rightarrow> (u, v))"

thm "find_closest.simps"

(*>*)

text\<open>
\section{Closest Pair}

\begin{quote}
@{term [source] "find_closest_\<delta> :: point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point"}
@{thm [display] (concl) find_closest_\<delta>.simps(1,2)[of DUMMY DUMMY] find_closest_\<delta>_simp}

\end{quote}

\begin{quote}
@{const_typ closest_pair_combine}
@{thm [display] (dummy_pats,sub) closest_pair_combine.simps}
\end{quote}

@{thm bigo_measure_trans}

\section{The Core}

The main function:

\begin{quote}%quote is just one possible way to display function definitions
@{const_typ f}\\
@{thm f.simps} 
\end{quote}

\begin{lemma}
This can be proved by induction: @{thm f0}
\end{lemma}

This is a long tautology:
\begin{quote}
@{thm [break,margin=60] long} %break causes automatic line breaks
\end{quote}

Of course you can also inline terms or formulas: @{term "f(f 0)"}. And types: @{typ "'a list"}
\<close>
(*<*)
end
(*>*)
