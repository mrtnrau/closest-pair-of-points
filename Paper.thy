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
  by (cases ps) auto

lemma closest_pair_combine_simp:
  "ps \<noteq> [] \<Longrightarrow> ps \<noteq> [p] \<Longrightarrow> closest_pair_combine (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest_\<delta> p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      closest_pair_combine (c\<^sub>0, c\<^sub>1) ps
    else
      closest_pair_combine (p\<^sub>0, p\<^sub>1) ps
  )"
  by (cases ps) auto

translations
  "p" <= "(case p of (x, y) \<Rightarrow> (u, v))"

(*>*)

text\<open>

\section{Closest Pair Algorithm}

\begin{quote}
% @{term [source] "find_closest_\<delta> :: point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point"}
@{thm [display] (concl) find_closest_\<delta>.simps(1,2)[of DUMMY DUMMY] find_closest_\<delta>_simp}
\end{quote}

\begin{quote}
@{thm [display] (concl) closest_pair_combine.simps(1) closest_pair_combine.simps(2)[of _ _ DUMMY] closest_pair_combine_simp}
\end{quote}

\begin{quote}
@{thm [display] combine.simps}
\end{quote}

\begin{quote}
@{thm [display] closest_pair_rec.simps}
\end{quote}

\begin{quote}
@{thm [display] closest_pair.simps}
\end{quote}




\section{Proving Functional Correctness}




\section{Proving Running Time}




\section{Executable Code}








\section{Closest Pair}





\section{Templates}

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
