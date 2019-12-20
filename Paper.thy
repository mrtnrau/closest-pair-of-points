(*<*)
theory Paper
  imports
  "Proofs.Closest_Pair"
  "Proofs.Closest_Pair_Code"
  "Proofs.Closest_Pair_Time"
  "Proofs.OptionalSugarLocal"
begin

(* Alternative simps for display *)

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
      (msort snd xs, closest_pair_bf xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec xs\<^sub>R in
      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine p\<^sub>L p\<^sub>R (fst (hd xs\<^sub>R)) ys)
  )"
  by (auto simp: closest_pair_rec.simps Let_def sortY_def)

lemma closest_pair_simp:
  "ps = p # q # ps' \<Longrightarrow> closest_pair ps = (let (ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec (msort fst ps) in (c\<^sub>0, c\<^sub>1))"
  by (simp add: sortX_def)

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

(* Styling *)

translations
  "p" <= "(case p of (x, y) \<Rightarrow> (u, v))"

(*>*)

text\<open>
\section{Introduction}

The \textit{Closest Pair of Points} or \textit{Closest Pair} problem is one of the fundamental
problems in Computational Geometry: Given a set $P$ of $n \geq 2$ points in $\mathbb{R}^d$,
find the closest pair of $P$, i.e. two points $p_0 \in P$ and $p_1 \in P$ ($p_0 \ne p_1$) such that 
the distance between $p_0$ and $p_1$ is less than or equal to the distance of any distinct pair 
of points of $P$.

Shamos and Hoey \cite{Closest-Point-Problems:1975} are one of the first to mention this problem and
introduce an algorithm based on \textit{Voronoi} diagrams for the planar case, improving the running 
time of the best known algorithms at the time from $\mathcal{O}(n^2)$ to
$\mathcal{O}(n \log n)$. They also prove that this running time is optimal for a
deterministic computation model. One year later, in 1976, Bentley and Shamos
\cite{Divide-And-Conquer-In-Multidimensional-Space:1976} publish a, also optimal, divide-and-conquer
algorithm to solve the Closest Pair problem that can be non-trivially extended to work on
spaces of arbitrary dimension. Since then the problem has been the focus of extensive research and
a multitude of optimal algorithms have been published. Smid \cite{Handbook-Computational-Geometry:2000}
provides a comprehensive overview over the available algorithms, including randomized approaches which
improve the running time even further to $\mathcal{O}(n)$.

The main contribution of this paper is the first verification of two related functional implementations of a
divide-and-conquer algorithm solving the Closest Pair problem for the two-dimensional Euclidean plane
with the optimal running time of $\mathcal{O}(n \log n)$. We use the interactive theorem 
prover Isabelle/HOL \cite{LNCS2283,Concrete} to prove functional correctness as well as the 
running time of the algorithms. Empirical testing also shows that our verified algorithms are 
competitive with handwritten reference implementations. Our formalizations are available online 
(TODO LINK) in the Archive of Formal Proofs.

This paper is structured as follows:
Section \ref{section:closest_pair_algorithm} familiarizes the reader with the algorithm by presenting a
high-level description that covers both implementations. Section \ref{section:proving_functional_correctness} presents the first
implementation and functional correctness proof. Section \ref{section:proving_running_time} proves
the running time of $\mathcal{O}(n \log n)$ of the implementation of the previous section.
Section \ref{section:alt_impl} describes our second implementation and illustrates how the proofs of
Sections \ref{section:proving_functional_correctness} and \ref{section:proving_running_time} need to be adjusted
to this implementation. We then shortly give an overview over further implementation and proof approaches.
Section \ref{section:executable_code} describes final adjustments to obtain executable versions of the algorithms in target languages
such as OCaml and SML and evaluates them against handwritten imperative and functional implementations. 
Section \ref{section:conclusion} concludes.

\subsection{Related Verification Work}

Computational geometry is a vast area but only a few algorithms and theorems seem to have been
verified formally. We are aware of a number of verifications of convex hull algorithms
\cite{DBLP:conf/tphol/PichardieB01,DBLP:conf/adg/MeikleF04,DBLP:journals/comgeo/BrunDM12}
(incl.\ and a similar algorithm for the intersection of zonotopes \cite{Immler:2015})
and algorithms for triangulation \cite{DBLP:conf/itp/DufourdB10,DBLP:conf/ictac/Bertot18}.
Geometric models based on maps and hypermaps
\cite{DBLP:journals/tcs/PuitgD00,DBLP:journals/jar/Dufourd09} are frequently used.

Work on theorem proving in geometry (see \cite{narboux:hal-01779452} for an overview)
is also related but considers fixed geometric constructions rather than algorithms.

\subsection{Isabelle/HOL and Notation}

TODO


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
$P_R$, respectively. Let $\delta_L$ and $\delta_R$ denote the distance of the left and right closest
pairs and let $\delta = \mathit{min} \{\delta_L,\;\delta_R\}$. 
At this point the closest pair of $P$ is either $(p_{L0},\; p_{L1})$, 
$(p_{R0},\,p_{R1})$ or a pair of points $p_0 \in P_L$ and $p_1 \in P_R$
with a distance strictly less than $\delta$. If the former is the case we have already found our closest pair.

Now we assume the latter and have reached the most interesting part of divide-and-conquer algorithms,
the \textit{combine} step. It is not hard to see that both points of the closest pair 
must be within a $2\delta$ wide vertical strip centered around $l$. Let $\mathit{ys}$ now denote a 
list of points, sorted in ascending order by $y$-coordinate, of all points $p \in P$ 
that are also contained within this $2\delta$ wide strip. We can find our closest pair by iterating over
$\mathit{ys}$ and computing for each point its closest neighbor. Note that, in the worst case, $\mathit{ys}$ 
contains all points of $P$, if the distribution of the points is dense horizontally and sparse vertically, 
and we might think our only option is to again check all $n \choose 2$ point combinations. 
This is not the case. Let $p_0$ denote an arbitrary point of $\mathit{ys}$ as illustrated in Figure \ref{fig:Combine}.
%
\begin{figure}[htpb]
\centering
\includegraphics[width=0.5\textwidth]{./../../img/Combine.png}
\caption[]{The \textit{combine} step If the red point has a closest neighbor within a distance of $\le\delta$
             in the marked $2\delta$ wide vertical strip, then this neighbor must be located in
             the grey $2\delta$ sized square.}
\label{fig:Combine}
\end{figure}
%
If $p_0$ is one of the points of the closest pair, then the distance to its closest
neighbor is strictly less than $\delta$ and we only have to check all points $p_1 \in \mathit{set\ ys}$
that are contained within the $2\delta$ wide horizontal strip centered around the $y$-coordinate of $p_0$.

In Section \ref{section:proving_running_time} we prove that, for each $p \in \mathit{set\ ys}$, it suffices to check 
only a constant number of closest point candidates. This fact allows for an implementation of 
the combine step that runs in linear time and ultimately lets us achieve the familiar recurrence 
relation of $T(n) = T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + \mathcal{O}(n)$, 
which results in the optimal running time of $\mathcal{O}(n \log n)$.

We glossed over some implementation details to achieve this theoretical time complexity.
In Section \ref{section:proving_functional_correctness} we refine the algorithm and
in Section \ref{section:proving_running_time} we prove the $\mathcal{O}(n \log n)$ running time.


\section{Implementation and Functional Correctness Proof}
\label{section:proving_functional_correctness}

We present the implementation of the divide-and-conquer algorithm and the corresponding correctness proofs
using a bottom-up approach, starting with the combine step. But first we need to introduce some definitional
preliminaries of two-dimensional geometry and formalize the closest pair problem.

A point in the two-dimensional Euclidean plane is represented as a pair of (arbitrary-precision) integers
\footnote{We choose this representation over a pair of real numbers because we cannot generate code
for mathematical reals. See Section \ref{section:executable_code}.}.
The library \textit{HOL-Analysis} provides a generic distance function applicable to our point definition.
For our purposes the definition of this \textit{dist} function corresponds to the familiar Euclidean distance measure.

$$\mathit{dist\ (x_0,\;y_0)\ (x_1,\;y_1)} = \sqrt{(x_0 - x_1)^2 + (y_0 - y_1)^2}$$

The closest pair problem can then be stated formally as follows: A set of points $P$ is $\delta$-sparse iff 
$\delta$ is a lower bound for the distance of all distinct pairs of points of $P$.

\begin{quote}
@{thm [display] min_dist_def[of \<delta> P]}
\end{quote}

A pair of points $(p_0,\;p_1)$ is then the \textit{closest pair} of $P$ iff additionally $p_0 \in P$,
$p_1 \in P$ holds and the points $p_0$ and $p_1$ are distinct.

In the following we focus on proving the sparsity property of our implementation. The additional
set membership and distinctness properties of a closest pair can be proven relatively straightforward
by adhering to a similar proof structure.

\subsection{Combine step}

The essence of the combine step deals with the following scenario: We are given an initial pair of points
with a distance of $\delta$ and and a list $\mathit{ys}$ of points, sorted ascendingly by $y$-coordinate, 
which are contained in the $2\delta$-wide vertical strip centered around $l$ (see Figure \ref{fig:Combine}). Our task is to
efficiently compute a pair of points with a distance $\delta'\ (\delta' \le \delta)$ such that $\mathit{ys}$ is $\delta'$-sparse.
The recursive function \textit{find\_closest\_pair} achieves this by iterating over $\mathit{ys}$, computing
for each point its closest neighbor by calling the recursive function \textit{find\_closest}, which
considers only the points within the $2\delta$ sized square of Figure \ref{fig:Combine}, and updating the
current pair of points accordingly. We omit the implementation of the trivial base cases.

\begin{quote}
@{term [source, break] "find_closest_pair :: point \<times> point \<Rightarrow> point list \<Rightarrow> point \<times> point"}

@{thm [break] (concl) find_closest_pair_simp}
\end{quote}

\begin{quote}
@{term [source, break] "find_closest :: point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point"}

@{thm [break] (concl) find_closest_simp}
\end{quote}

There are several noteworthy aspects of this implementation. The recursive search for the closest neighbor
of a given point $p$ of \textit{find\_closest} starts at the first point above $p$, continues upwards and 
is stopped early at the first point whose vertical distance to $p$ exceeds the given $\delta$. Thus the function
considers, in contrast to Figure \ref{fig:Combine}, only the upper half of the $2\delta$ sized square during this search. 
This is sufficient for the computation of a closest pair because for each possible point $q$ preceding $p$ in 
$\mathit{ys}$ we already considered the pair $(q,\,p)$, if needed, and do not have to re-check $(p,\,q)$ due to the
commutative property of our closest pair definition. Note also that $\delta$ is updated, if possible, 
during the computation and consequently the search space for each point is limited to a $2\delta \times \delta'$
rectangle with $\delta' \le \delta$.
Lastly we intentionally do not minimize the number of distance computations.
% One could easily do so by annotating the returned
%closest neighbor of \textit{find\_closest} with its distance to $p$ and memoizing relevant distance 
%computations of both functions through let bindings. At this point, we refrain from doing so because it does not change 
%the overall theoretical running time of the algorithm and simplifies the proofs slightly.
In Section \ref{section:executable_code} we make this optimization for the final executable code.

We then prove by induction on the computation of the respective function
the following lemma, capturing the desired sparsity property of our implementation of the combine step so far. 

\begin{lemma} \label{lemma:find_closest_pair_dist}
@{text [source, break] "sortedY ps \<and> distinct ps \<and>"}

@{text [source, break] "(p\<^sub>0, p\<^sub>1) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps \<and>"}

@{text [source, break] "(\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ps \<and> p\<^sub>1 \<in> set ps \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1)"}

@{text [source, break] "\<Longrightarrow> min_dist (dist p\<^sub>0 p\<^sub>1) (set ps)"}
\end{lemma}

We wrap up the combine step by limiting our search for the closest pair to only the points contained within the mentioned
$2\delta$ wide vertical strip and choosing as argument for the initial pair of points of \textit{find\_closest\_pair}
the closest pair of the two recursive invocations of our divide-and-conquer algorithm with the smaller distance $\delta$.
\begin{quote}
@{term [source, break] "combine :: point \<times> point \<Rightarrow> point \<times> point \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> point \<times> point"}

@{thm [break] combine_simp}
\end{quote}
Using Lemma \ref{lemma:find_closest_pair_dist} we prove that @{const combine} computes indeed a pair
of points @{term "(p\<^sub>0,p\<^sub>1)"} such that our given list of points \<open>ps\<close> is (@{term "dist p\<^sub>0 p\<^sub>1"})-sparse.

\begin{lemma} \label{lemma:combine_dist}
@{text [source, break] "distinct ps \<and> sortedY ps \<and> set ps = ps\<^sub>L \<union> ps\<^sub>R \<and>"}

@{text [source, break] "(\<forall>p \<in> ps\<^sub>L. fst p \<le> l) \<and> min_dist (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ps\<^sub>L \<and> p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L \<and>"}

@{text [source, break] "(\<forall>p \<in> ps\<^sub>R. l \<le> fst p) \<and> min_dist (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ps\<^sub>R \<and> p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R \<and>"}

@{text [source, break] "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps "}

@{text [source, break] "\<Longrightarrow> min_dist (dist p\<^sub>0 p\<^sub>1) (set ps)"}
\end{lemma}

One can show that $(p_0,\;p_1)$ is also the \textit{closest pair} of $\mathit{ps}$ if $(p_{0L},\;p_{1L})$
and $(p_{0R},\;p_{1R})$ are the closest pairs of $\mathit{ps_L}$ and $\mathit{ps_R}$, respectively.

\subsection{Divide \& Conquer Algorithm}

In Section \ref{section:closest_pair_algorithm} we glossed over some implementation detail which
is necessary to achieve to optimal running time of $\mathcal{O}(n \log n)$. In particular
we need to partition the given list of points $\mathit{ps}$\footnote{Our implementation deals with
concrete lists in contrast to the abstract sets used in Section \ref{section:closest_pair_algorithm}.}
along a vertical line $l$ into two lists of nearly equal length during the divide step and obtain
a list $\mathit{ys}$ of the same points, sorted ascendingly by $y$-coordinate, for the combine
step in linear time at each level of recursion.

Concerning the partitioning of the list we can \textit{presort} $\mathit{ps}$ by $x$-coordinate, obtaining $\mathit{xs}$, 
split $\mathit{xs}$ at $\mathit{length\ xs\ div\ 2}$ into two
still sorted lists $\mathit{xs_L}$ and $\mathit{xs_R}$ and choose $l$ as either the $x$-coordinate of
the last element of $\mathit{xs_L}$ of the $x$-coordinate of the first element of $\mathit{xs_R}$.

For this presorting step we use an implementation of \textit{mergesort} which sorts a list of points
depending on a given projection function, \textit{fst} for `by $x$-coordinate' and \textit{snd} for 
`by $y$-coordinate'. Splitting of the list is achieved by the function \textit{split\_at} with a 
simple linear pass through $\mathit{xs}$.

Next we need to efficiently obtain $\mathit{ys}$. Looking at the overall structure of our algorithm
so far we recognize that it closely resembles the structure of a standard mergesort implementation and
that we only need $\mathit{ys}$ for the combine step after the two recursive function invocations. 
Consequently we can obtain $\mathit{ys}$ by sorting and merging `along the way'. In the base case we
sort $\mathit{xs}$ by $y$-coordinate and compute the closest pair using the brute-force approach.
The recursive call of the algorithm on $\mathit{xs_L}$, the left half of $\mathit{xs}$, 
returns in addition the the left closest pair the list $\mathit{ys_L}$, containing all points of
$\mathit{xs_L}$ sorted by $y$-coordinate. Analogously for $\mathit{xs_R}$ and $\mathit{ys_R}$. We then
reuse the \textit{merge} step of our mergesort implementation to obtain $\mathit{ys}$ from
$\mathit{ys_L}$ and $\mathit{ys_R}$ in linear time at each level of recursion, resulting in the
following implementation:

\begin{quote}
@{term [source, break] "closest_pair_rec :: point list \<Rightarrow> point list \<times> point \<times> point"}

@{thm [break, margin=50] closest_pair_rec_simp}
\end{quote}

\begin{quote}
@{term [source, break] "closest_pair :: point list \<Rightarrow> point \<times> point"}

@{thm [break] (concl) closest_pair_simp}
\end{quote}

Using Lemma \ref{lemma:combine_dist}, the functional correctness proofs of our mergesort implementation
and several auxiliary lemmas proving that \textit{closest\_pair\_rec} also sorts the points by $y$-coordinate,
we arrive at the following two theorems, proving the desired sparsity property of the algorithm.

\begin{theorem}
@{text [source, break] "1 < length xs \<and> distinct xs \<and> sortedX xs \<and>"}

@{text [source, break] "(ys, p\<^sub>0, p\<^sub>1) = closest_pair_rec xs \<Longrightarrow> min_dist (dist p\<^sub>0 p\<^sub>1) xs"}
\end{theorem}

\begin{theorem}
@{text [source, break] "1 < length ps \<and> distinct ps \<and>"}

@{text [source, break] "(p\<^sub>0, p\<^sub>1) = closest_pair ps \<Longrightarrow> min_dist (dist p\<^sub>0 p\<^sub>1) ps"}
\end{theorem}


\section{Proving Running Time} \label{section:proving_running_time}

In Section \ref{section:closest_pair_algorithm} we claimed that the running time of the algorithm is
described by the recurrence relation @{text "T(n) = T(\<lceil>n/2\<rceil>) + T(\<lfloor>n/2\<rfloor>) + O(n)"},
where @{term n} is the length of the given list of points. In principle, we can determine the solution, 
$\mathcal{O}(n \log n)$, for this relation using the `master theorem' \cite{Introduction-to-Algorithms:2009}.
The claim implies an at most linear overhead at each level of recursion. Splitting of the list @{term xs},
merging @{term ys\<^sub>L} and @{term ys\<^sub>R} and the filtering operation of the combine step obviously run in
linear time. But it is non-trivial that the function @{const find_closest_pair} also exhibits a linear
time complexity. The function is applied to an argument list of, in the worst case, length @{term n}, iterates
once through the list and calls @{const find_closest} for each element. Consequently our proof obligation
is the constant running time of @{const find_closest}.

\subsection{Informal Proof}

We sketch the informal proof from Cormen et al. \cite{Introduction-to-Algorithms:2009}, slightly adjusted
to our functional implementation. We can assume for each invocation of @{term "find_closest p \<delta> ps"}
the list @{text "p # ps"} to be sorted ascendingly by @{term y}-coordinate. The function then terminates, in the
worst case, as soon as it encounters the first point of @{term ps} with a vertical distance to @{term p}
that exceeds @{term \<delta>} since for every recursive call @{term "find_closest p \<delta>' ps'"} we know @{term "\<delta>' \<le> \<delta>"}.
We additionally assume that all points of @{text "p # ps"} are contained within the @{text "2\<delta>"} wide
vertical strip centered around the vertical dividing line @{term l}. Subsequently the running time of
@{const find_closest} is bounded by the number of points within the @{text "2\<delta> \<times> \<delta>"} rectangle @{term R}
defined by its left lower corner @{term "(l - \<delta>, snd p)"} and right upper corner @{term "(l + \<delta>, snd p + \<delta>)"}.
But there can be at most @{text 8} points in @{term R}, as illustrated in Figure \ref{fig:Constant}.
Consider the number of points in the left half of @{term R}, a square @{term S} of side length @{term \<delta>}.
From the conquer step of the algorithm we know that @{term S} is @{term \<delta>}-sparse, or every distinct pair
of points is at least @{term \<delta>} far apart, since @{term S} is a subset of all points which lie to the left 
of or on the line @{term l}. Thus we can fit at most @{text 4} points into @{term S}. The same argument
holds for the right half of @{term R}. If we count the coincident points on @{term l}, we conclude
that @{term R} contains a maximum of @{text 8} points and @{const find_closest} runs in constant time.

\begin{figure}[htpb]
  \centering
  \includegraphics[width=0.5\textwidth]{./../../img/Constant_Short.png}
  \caption[]{The @{text "2\<delta> \<times> \<delta>"} rectangle @{term R}, highlighted in grey, contains a maximum of @{text 8} points, if
             all points of @{term ps\<^sub>L} and @{term ps\<^sub>R} are respectively @{term \<delta>}-sparse and the points
             shown on the vertical line @{term l} are pairs of coincident points.} \label{fig:Constant}
\end{figure}

\subsection{Running Time Verification in Isabelle}

To formally verify the running time we follow the approach in \cite{Nipkow-APLAS17}. For each function @{text f}
we define a function @{text "t_f"} that takes the same arguments as @{text f} but computes the number of function
calls the computation of @{text f} needs, the `time'. Function @{text "t_f"} follows the same recursion
structure as @{text f} and can be seen as an abstract interpretation of @{text f}. For simplicity of presentation
we define @{text f} and @{text "t_f"} directly rather than deriving them from a monadic function that computes
both the value and the time. We also simplify matters a bit: we count only expensive operations that scale
with the size of the input and ignore other small additive constants. This also includes setting the time
to execute @{const dist} computations to @{text 0}. Note that it might be of interest to define a similar
approach to count the number of @{const dist} computations of the algorithm and proof that an implementation
minimizes this number. Since we chose not to minimize the number of @{const dist} computations,
except for the final executable code in Section \ref{section:executable_code} we omit such an analysis.

To illustrate our approach we show the timing function for @{const find_closest} as an example.

\begin{quote}
@{thm [display] (concl) t_find_closest_simp}
\end{quote}

We can then prove an upper bound for @{term "t_find_closest p \<delta> ps"} dependent on the number of points
that are effectively within @{term R}. The function @{term "count f"} is an abbreviation for @{term "(length \<circ> filter f)"}. 

\begin{lemma}
@{thm [display] t_find_closest_cnt}
\end{lemma}


\subsection{Formal Proof}

\begin{lemma}
@{thm [display] cbox_2D}
\end{lemma}

\begin{lemma}
@{thm [display] max_points_is_7}
\end{lemma}

\begin{lemma}
@{thm [display] max_points_square}
\end{lemma}

\begin{lemma}
@{thm [display] pigeonhole}
\end{lemma}

\begin{lemma}
@{thm [display] cbox_max_dist}
\end{lemma}

\begin{lemma}
@{thm [display] bigo_measure_trans}
\end{lemma}

\begin{quote}
@{thm [display] closest_pair_rec_cost.simps}
\end{quote}

\begin{lemma}
@{thm [display] closest_pair_rec_cost}
\end{lemma}

\begin{lemma}
@{thm [display] t_closest_pair_rec_bigo}
\end{lemma}

\begin{lemma}
@{thm [display] t_closest_pair_bigo}
\end{lemma}

\section{Alternative Implementations} \label{section:alt_impl}

The basis for our implementation is the algorithm presented by Cormen et al. \cite{Introduction-to-Algorithms:2009}.

\section{Executable Code} \label{section:executable_code}

\section{Conclusion} \label{section:conclusion}

\paragraph{Acknowledgements}
\<close>

(*<*)
end
(*>*)
