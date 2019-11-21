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

lemma find_closest_simp:
  "ps \<noteq> [] \<Longrightarrow> find_closest p \<delta> (p\<^sub>0 # ps) = (
    if \<delta> \<le> snd p\<^sub>0 - snd p then
      p\<^sub>0
    else
      let p\<^sub>1 = find_closest p (min \<delta> (dist p p\<^sub>0)) ps in
      if dist p p\<^sub>0 \<le> dist p p\<^sub>1 then
        p\<^sub>0
      else
        p\<^sub>1
  )"
  by (cases ps) auto

lemma find_closest_pair_simp:
  "ps \<noteq> [] \<Longrightarrow> ps \<noteq> [p] \<Longrightarrow> find_closest_pair (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      find_closest_pair (c\<^sub>0, c\<^sub>1) ps
    else
      find_closest_pair (p\<^sub>0, p\<^sub>1) ps
  )"
  by (cases ps) auto

lemma combine_simp:
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    find_closest_pair (c\<^sub>0, c\<^sub>1) (filter (\<lambda>p. dist p (l, snd p) < dist c\<^sub>0 c\<^sub>1) ps)
  )"
  by simp

lemma closest_pair_rec_simp:
  "closest_pair_rec xs = (
    let n = length xs in
    if n \<le> 3 then
      (sortY xs, closest_pair_bf xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec xs\<^sub>R in
      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine p\<^sub>L p\<^sub>R (fst (hd xs\<^sub>R)) ys)
  )"
  by (auto simp: closest_pair_rec.simps Let_def)

lemma closest_pair_simp:
  "ps = p # q # ps' \<Longrightarrow> closest_pair ps = (let (ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec (sortX ps) in (c\<^sub>0, c\<^sub>1))"
  by simp

translations
  "p" <= "(case p of (x, y) \<Rightarrow> (u, v))"

(*>*)

text\<open>

\section{Closest Pair Algorithm}




\section{Proving Functional Correctness}

\begin{quote}
% @{term [source] "find_closest :: point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point"}
@{thm [display] (concl) find_closest_simp}
\end{quote}

\begin{quote}
@{thm [display] (concl) find_closest_pair_simp}
\end{quote}

\begin{quote}
@{thm [display] combine_simp}
\end{quote}

\begin{quote}
@{thm [display] closest_pair_rec_simp}
\end{quote}

\begin{quote}
@{thm [display] (concl) closest_pair_simp}
\end{quote}




\section{Proving Running Time}




\section{Executable Code}




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
