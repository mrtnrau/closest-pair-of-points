(*<*)
theory Paper
  imports
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

lemma t_find_closest_simp:
  "ps \<noteq> [] \<Longrightarrow> ps \<noteq> [p] \<Longrightarrow> t_find_closest p \<delta> (p\<^sub>0 # ps) = 1 + (
    if \<delta> \<le> snd p\<^sub>0 - snd p then
      0
    else
      let p\<^sub>1 = find_closest p (min \<delta> (dist p p\<^sub>0)) ps in
      t_find_closest p (min \<delta> (dist p p\<^sub>0)) ps + (
      if dist p p\<^sub>0 \<le> dist p p\<^sub>1 then 0 else 0
    )
  )"
  by (cases ps) auto

lemma t_closest_pair_rec_simp:
  "t_closest_pair_rec xs = 1 + (
    let n = length xs in
    t_length xs + (
    if n \<le> 3 then
      t_sortY xs + t_closest_pair_bf xs
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      t_split_at (n div 2) xs + (
      let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec xs\<^sub>L in
      t_closest_pair_rec xs\<^sub>L + (
      let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec xs\<^sub>R in
      t_closest_pair_rec xs\<^sub>R + (
      let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
      t_merge (\<lambda>p. snd p) (ys\<^sub>L, ys\<^sub>R) + t_combine p\<^sub>L p\<^sub>R (fst (hd xs\<^sub>R)) ys
    ))))
  )" by (auto simp: t_closest_pair_rec.simps)

translations
  "p" <= "(case p of (x, y) \<Rightarrow> (u, v))"

(*>*)

text\<open>

\section{Closest Pair Algorithm} \label{section:closest_pair_algorithm}

In this section we provide a high-level overview of the \textit{Closest Pair} algorithm and give
the reader a first intuition without delving into implementation details and functional correctness 
and running time proofs.

Let $P$ denote a set of $n \ge 2$ points. If $n \le 3$ we solve the problem 
naively using the brute force approach of examining all $n \choose 2$ possible closest pair 
combinations. Otherwise we apply the divide-and-conquer tactic.

We \textit{divide} $P$ into two sets $P_L$ and $P_R$ along a vertical 
line $l$ such that the sizes of $P_L$ and $P_R$ differ by at most $1$ and the
$y$-coordinate of all points $p_L \in P_L\,(p_R \in P_R)$ is less
(greater) than or equal to $l$.

We then \textit{conquer} the left and right subproblems by applying the algorithm recursively, 
obtaining $(p_{L0},\;p_{L1})$ and $(p_{R0},\;p_{R1})$, the closest pairs of $P_L$ and 
$P_R$, respectively. Let $\delta$ denote the minimum of the distances of the left and
right closest pair. At this point the closest pair of $P$ is either $(p_{L0},\; p_{L1})$, 
$(p_{R0},\,p_{R1})$ or a pair of points $p_0 \in P_L$ and $p_1 \in P_R$
with a distance strictly less than $\delta$. If the former is the case we have already found our closest pair.

Now we assume the latter and have reached the most interesting part of divide-and-conquer algorithms,
the \textit{combine} step. It is straightforward to see that both points of the closest pair 
must be within a $2\delta$ wide vertical strip centered around $l$. Let $\mathit{ys}$ now denote a 
list of points, sorted in ascending order by $y$-coordinate, of all points $p \in P$ 
that are also contained within this $2\delta$ wide strip. We can find our closest pair by iterating over
$\mathit{ys}$ and computing for each point its closest neighbor. Note that, in the worst case, $\mathit{ys}$ 
contains all points of $P$ and we might think our only option is to again check all 
$n \choose 2$ point combinations. This is not the case. For each point $p_0 \in \mathit{set\ ys}$
we know that, if $p_0$ is one of the points of the closest pair, then the distance to its closest
neighbor is strictly less than $\delta$ and we only have to check all points $p_1 \in \mathit{set\ ys}$
that are contained within a $2\delta$ wide horizontal strip centered around the $y$-coordinate of $p_0$.

In Section \ref{section:proving_running_time} we prove that, for each $p \in \mathit{set\ ys}$, it suffices to check 
only a constant number of closest point candidates. This fact allows for an implementation of 
the combine step that runs in linear time and ultimately lets us achieve the familiar recurrence 
relation of $T(n) = T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + \mathcal{O}(n)$, 
which results in the optimal running time.

We glossed over some implementation detail to achieve the optimal running time of 
$\mathcal{O}(n\ \mathit{log}\;n)$. In particular we also need to obtain $P_L$ and 
$P_R$ and the sorted list $\mathit{ys}$ in linear time. 
In Section \ref{section:proving_functional_correctness} we use \textit{Presorting} and an integrated
version of \textit{Mergesort} to achieve the necessary linear time of the divide step and the complete combine step. 
We refer the reader to Section \ref{section:proving_running_time} for a formal prove of the running time.
\<close>


text\<open>
\section{Proving Functional Correctness} \label{section:proving_functional_correctness}

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
\<close>


text\<open>
\section{Proving Running Time} \label{section:proving_running_time}

\begin{quote}
@{thm [display] (concl) t_find_closest_simp}
\end{quote}

\begin{quote}
@{thm [display] (concl) t_closest_pair_rec_simp}
\end{quote}

\begin{quote}
@{thm [display] closest_pair_rec_cost.simps}
\end{quote}
\<close>


text\<open>
\section{Executable Code} \label{section:executable_code}
\<close>
(*<*)
end
(*>*)
