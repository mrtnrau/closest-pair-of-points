(*<*)
theory Paper
imports
  Closest_Pair_Points.Closest_Pair
  "OptionalSugarLocal"
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
      (mergesort snd xs, closest_pair_bf xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let (ys\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) (fst (hd xs\<^sub>R)) ys)
  )"
  by (auto simp: closest_pair_rec.simps Let_def)

lemma closest_pair_simp:
  "ps = p # q # ps' \<Longrightarrow> closest_pair ps = (let (ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec (mergesort fst ps) in (c\<^sub>0, c\<^sub>1))"
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

lemma closest_pair_rec_recurrence_simps:
  "closest_pair_recurrence n = (
    if n \<le> 3 then
      n + mergesort_recurrence n + n * n
    else
      13 * n + closest_pair_recurrence (nat \<lfloor>real n / 2\<rfloor>) + closest_pair_recurrence (nat \<lceil>real n / 2\<rceil>)
  )" by (auto)

(* Styling *)

translations
  "p" <= "(case p of (x, y) \<Rightarrow> (u, v))"

(*>*)

text\<open>
\section{Introduction}

The \textit{Closest Pair of Points} or \textit{Closest Pair} problem is one of the fundamental
problems in Computational Geometry: Given a set \<open>P\<close> of \<open>n \<ge> 2\<close> points in $\mathbb{R}^d$,
find the closest pair of $P$, i.e. two points $p_0 \in P$ and $p_1 \in P$ ($p_0 \ne p_1$) such that 
the distance between $p_0$ and $p_1$ is less than or equal to the distance of any distinct pair 
of points of $P$.

Shamos and Hoey \cite{Closest-Point-Problems:1975} are one of the first to mention this problem and
introduce an algorithm based on \textit{Voronoi} diagrams for the planar case, improving the running 
time of the best known algorithms at the time from $\mathcal{O}(n^2)$ to
$\mathcal{O}(n \log n)$. They also prove that this running time is optimal for a
deterministic computation model. One year later, in 1976, Bentley and Shamos
\cite{Divide-And-Conquer-In-Multidimensional-Space:1976} publish a, also optimal, divide-and-conquer
algorithm to solve the Closest Pair problem that can be non-trivially extended to work in arbitrary dimensions. Since then the problem has been the focus of extensive research and
a multitude of optimal algorithms have been published. Smid \cite{Handbook-Computational-Geometry:2000}
provides a comprehensive overview over the available algorithms, including randomized approaches which
improve the running time even further to $\mathcal{O}(n)$.

The main contribution of this paper is the first verification of two related functional implementations of the
divide-and-conquer algorithm solving the Closest Pair problem for the two-dimensional Euclidean plane
with the optimal running time of $\mathcal{O}(n \log n)$. We use the interactive theorem 
prover Isabelle/HOL \cite{LNCS2283,Concrete} to prove functional correctness as well as the 
running time of the algorithms. In contrast to many publications and implementations we do not assume 
all points of \<open>P\<close> to have unique \<open>x\<close>-coordinates which causes some tricky complications. Empirical 
testing shows that our verified algorithms are competitive with handwritten reference 
implementations. Our formalizations are available online @{cite "Closest_Pair_Points-AFP"} in the 
Archive of Formal Proofs.

This paper is structured as follows:
Section \ref{section:closest_pair_algorithm} familiarizes the reader with the algorithm by presenting a
high-level description that covers both implementations. Section \ref{section:proving_functional_correctness} presents the first
implementation and its functional correctness proof. Section \ref{section:proving_running_time} proves
the running time of $\mathcal{O}(n \log n)$ of the implementation of the previous section.
Section \ref{section:alt_impl} describes our second implementation and illustrates how the proofs of
Sections \ref{section:proving_functional_correctness} and \ref{section:proving_running_time} need to be adjusted. 
We also give an overview over further implementation approaches.
Section \ref{section:executable_code} describes final adjustments to obtain executable versions of the algorithms in target languages
such as OCaml and SML and evaluates them against handwritten imperative and functional implementations. 
Section \ref{section:conclusion} concludes.


\subsection{Related Verification Work}

Computational geometry is a vast area but only a few algorithms and theorems seem to have been
verified formally. We are aware of a number of verifications of convex hull algorithms
\cite{DBLP:conf/tphol/PichardieB01,DBLP:conf/adg/MeikleF04,DBLP:journals/comgeo/BrunDM12}
(and a similar algorithm for the intersection of zonotopes \cite{Immler:2015})
and algorithms for triangulation \cite{DBLP:conf/itp/DufourdB10,DBLP:conf/ictac/Bertot18}.
Geometric models based on maps and hypermaps
\cite{DBLP:journals/tcs/PuitgD00,DBLP:journals/jar/Dufourd09} are frequently used.

Work on theorem proving in geometry (see \cite{narboux:hal-01779452} for an overview)
is also related but considers fixed geometric constructions rather than algorithms.

\subsection{Isabelle/HOL and Notation}

The notation \<open>t :: \<tau>\<close> means that term \<open>t\<close> has type \<open>\<tau>\<close>.
Basic types include @{type bool}, @{type nat}, @{type int} and @{type real}; type variables are written @{typ 'a}, @{typ 'b} etc; the function space arrow is \<open>\<Rightarrow>\<close>. Functions @{const fst} and @{const snd} return
the first and second component of a pair.

We suppress numeric conversion functions, e.g.\ @{text "real :: nat \<Rightarrow> real"}, except where that would result in ambiguities for the reader.

Most type constructors are written postfix, e.g. @{typ "'a set"} and @{typ "'a list"}.
Sets follow standard mathematical notation.
Lists are constructed from the empty list \<open>[]\<close> via the infix cons-operator \<open>(#)\<close>. Functions @{const hd} and @{const tl} return head and tail, function @{const set}
converts a list into a set.


\section{Closest Pair Algorithm} \label{section:closest_pair_algorithm}

In this section we provide a high-level overview of the \textit{Closest Pair} algorithm and give
the reader a first intuition without delving into implementation details, functional correctness 
or running time proofs.

Let $P$ denote a set of $n \ge 2$ points. If $n \le 3$ we solve the problem 
naively using the brute force approach of examining all $n \choose 2$ possible closest pair 
combinations. Otherwise we apply the divide-and-conquer tactic.

We divide $P$ into two sets $P_L$ and $P_R$ along a vertical 
line $l$ such that the sizes of $P_L$ and $P_R$ differ by at most $1$ and the
$y$-coordinate of all points \mbox{$p_L \in P_L\,(p_R \in P_R)$} is \<open>\<le> l\<close>
(\<open>\<ge> l\<close>).

We then conquer the left and right subproblems by applying the algorithm recursively, 
obtaining $(p_{L0},\;p_{L1})$ and $(p_{R0},\;p_{R1})$, the respective closest pairs of $P_L$ and 
$P_R$. Let $\delta_L$ and $\delta_R$ denote the distance of the left and right closest
pairs and let $\delta = \mathit{min}\;\delta_L\;\delta_R$. 
At this point the closest pair of $P$ is either $(p_{L0},\; p_{L1})$, 
$(p_{R0},\,p_{R1})$ or a pair of points $p_0 \in P_L$ and $p_1 \in P_R$
with a distance strictly less than $\delta$. In the first two cases we have already found our closest pair.

Now we assume the third case and have reached the most interesting part of divide-and-conquer algorithms,
the @{const combine} step. It is not hard to see that both points of the closest pair 
must be within a $2\delta$ wide vertical strip centered around $l$. Let $\mathit{ps}$ be a list of all points in $P$ that are contained within this $2\delta$ wide strip, sorted in ascending order by $y$-coordinate. We can find our closest pair by iterating over
$\mathit{ps}$ and computing for each point its closest neighbor. But in the worst case $\mathit{ps}$ contains all points of $P$, 
and we might think our only option is to again check all $n \choose 2$ point combinations. 
This is not the case. Let @{term p} denote an arbitrary point of $\mathit{ps}$, depicted as the square
point in Figure \ref{fig:Combine}.
%
\begin{figure}[htpb]
\centering
\includegraphics[width=0.5\textwidth,height=0.35\textheight]{./../../img/Combine.png}
\caption[]{The @{const combine} step}
\label{fig:Combine}
\end{figure}
%
If @{term p} is one of the points of the closest pair, then the distance to its closest
neighbor is strictly less than $\delta$ and we only have to check all points $q \in \mathit{set\ ps}$
that are contained within the $2\delta$ wide horizontal strip centered around the $y$-coordinate of @{term p}.

In Section \ref{section:proving_running_time} we prove that, for each $p \in \mathit{set\ ps}$, it suffices to check 
only a constant number of closest point candidates. This fact allows for an implementation of 
the @{const combine} step that runs in linear time and ultimately lets us achieve the familiar recurrence 
of $T(n) = T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + \mathcal{O}(n)$, 
which results in the running time of $\mathcal{O}(n \log n)$.

We glossed over some implementation details to achieve this time complexity.
In Section \ref{section:proving_functional_correctness} we refine the algorithm and
in Section \ref{section:proving_running_time} we prove the $\mathcal{O}(n \log n)$ running time.


\section{Implementation and Functional Correctness Proof}
\label{section:proving_functional_correctness}

We present the implementation of the divide-and-conquer algorithm and the corresponding correctness proofs
using a bottom-up approach, starting with the @{const combine} step. The basis for both implementation and proof is the version
presented by Cormen \emph{et al.} \cite{Introduction-to-Algorithms:2009}. But first we need to define the closest pair problem formally.

A point in the two-dimensional Euclidean plane is represented as a pair of (unbounded)
integers\footnote{We choose integers over reals because be we cannot implement
mathematical reals. See Section \ref{section:executable_code}. Alternatively we could have chosen rationals.}.
The library HOL-Analysis provides a generic distance function @{const dist} applicable to our point definition.
The definition of this specific @{const dist} instance corresponds to the familiar Euclidean distance measure.

The closest pair problem can be stated formally as follows: A set of points $P$ is $\mathbf{\delta}$\textbf{-sparse} iff 
$\delta$ is a lower bound for the distance of all distinct pairs of points of $P$.

\begin{quote}
@{text [display] "sparse \<delta> P = (\<forall>p\<^sub>0 \<in> P. \<forall>p\<^sub>1 \<in> P. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1)"}
\end{quote}
We can now state easily when two points \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> are a \textit{closest pair} of $P$: \mbox{@{prop "p\<^sub>0 \<in> P"}}, @{prop "p\<^sub>1 \<in> P"}, @{prop "p\<^sub>0 \<noteq> p\<^sub>1"}
and (most importantly) @{prop "sparse (dist p\<^sub>0 p\<^sub>1) P"}.

In the following we focus on outlining the proof of the sparsity property of our implementation,
without going into the details. The additional
set membership and distinctness properties of a closest pair can be proved relatively straightforwardly
by adhering to a similar proof structure.

\subsection{The Combine Step}

The essence of the @{const combine} step deals with the following scenario: We are given an initial pair of points
with a distance of $\delta$ and a list $\mathit{ps}$ of points, sorted in ascending order by $y$-coordinate,
that are contained in the $2\delta$ wide vertical strip centered around $l$ (see Figure \ref{fig:Combine}). Our task is to
efficiently compute a pair of points with a distance $\delta' \le \delta$ such that $\mathit{ps}$ is $\delta'$-sparse.
The recursive function @{const find_closest_pair} achieves this by iterating over $\mathit{ps}$, computing
for each point its closest neighbor by calling the recursive function \textit{find\_closest} that
considers only the points within the shaded square of Figure \ref{fig:Combine}, and updating the
current pair of closest points if the newly found pair is closer together. We omit the implementation of the trivial base cases.

\begin{quote}
@{term [source, break] "find_closest_pair :: point \<times> point \<Rightarrow> point list \<Rightarrow> point \<times> point"} \vskip 0pt
@{thm [break] (concl) find_closest_pair_simp}
\end{quote}

\begin{quote}
@{term [source, break] "find_closest :: point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point"} \vskip 0pt
@{thm [break] (concl) find_closest_simp}
\end{quote}

There are several noteworthy aspects of this implementation. The recursive search for the closest neighbor
of a given point $p$ of @{const find_closest} starts at the first point spatially above $p$, continues upwards and 
is stopped early at the first point whose vertical distance to $p$ is equal to or exceeds the given $\delta$. Thus the function
considers, in contrast to Figure \ref{fig:Combine}, only the upper half of the shaded square during this search. 
This is sufficient for the computation of a closest pair because for each possible point $q$ preceding $p$ in 
$\mathit{ps}$ we already considered the pair $(q,\,p)$, if needed, and do not have to re-check $(p,\,q)$ due to the
commutative property of our closest pair definition. Note also that $\delta$ is updated, if possible, 
during the computation and consequently the search space for each point is limited to a $2\delta \times \delta'$
rectangle with $\delta' \le \delta$. Lastly we intentionally do not minimize the number of distance computations.
In Section \ref{section:executable_code} we make this optimization for the final executable code.

The following lemma captures the desired sparsity property of our implementation of the @{const combine} step so far. It is proved by induction on the computation.

\begin{lemma} \label{lemma:find_closest_pair_dist}
@{text [source, break] "sorted_snd ps \<and> (p\<^sub>0, p\<^sub>1) = find_closest_pair (c\<^sub>0, c\<^sub>1) ps"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> sparse (dist p\<^sub>0 p\<^sub>1) (set ps)"}
\end{lemma}
where @{prop "sorted_snd ps"} means that \<open>ps\<close> is sorted in ascending order by $y$-coordinate.

We wrap up the @{const combine} step by limiting our search for the closest pair to only the points contained within the
$2\delta$ wide vertical strip and choosing as argument for the initial pair of points of \textit{find\_closest\_pair}
the closest pair of the two recursive invocations of our divide-and-conquer algorithm with the smaller distance $\delta$.

\vskip 10pt
\begin{adjustwidth}{-15pt}{0pt}
\begin{quote}
@{term [source, break] "combine :: point \<times> point \<Rightarrow> point \<times> point \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> point \<times> point"} \vskip 0pt
@{thm [break] combine_simp}
\end{quote}
\end{adjustwidth}
\vskip 10pt

Lemma \ref{lemma:set_band_filter} shows that if there exists a pair \<open>(p\<^sub>0, p\<^sub>1)\<close> of distinct points with a distance \<open>< \<delta>\<close>, then 
both its points are contained in the mentioned vertical strip, otherwise we have already found our closest pair
\<open>(c\<^sub>0, c\<^sub>1)\<close>, and the pair returned by @{const find_closest_pair} is its initial argument.  

\begin{lemma} \label{lemma:set_band_filter}
@{text [source, break] "p\<^sub>0 \<in> set ps \<and> p\<^sub>1 \<in> set ps \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta> \<and>"} \vskip 0pt
@{text [source, break] "(\<forall>p \<in> P\<^sub>L. fst p \<le> l) \<and> sparse \<delta> P\<^sub>L \<and>"} \vskip 0pt
@{text [source, break] "(\<forall>p \<in> P\<^sub>R. l \<le> fst p) \<and> sparse \<delta> P\<^sub>R \<and>"} \vskip 0pt
@{text [source, break] "set ps = P\<^sub>L \<union> P\<^sub>R \<and> ps' = filter (\<lambda>p. dist p (l , snd p) < \<delta>) ps"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps'"}
\end{lemma}

We then can prove, additionally using Lemma \ref{lemma:find_closest_pair_dist}, that @{const combine} computes 
indeed a pair of points @{term "(p\<^sub>0,p\<^sub>1)"} such that our given list of points \<open>ps\<close> is (@{term "dist p\<^sub>0 p\<^sub>1"})-sparse.

\begin{lemma} \label{lemma:combine_dist}
@{text [source, break] "sorted_snd ps \<and> set ps = P\<^sub>L \<union> P\<^sub>R \<and>"} \vskip 0pt
@{text [source, break] "(\<forall>p \<in> P\<^sub>L. fst p \<le> l) \<and> sparse (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) P\<^sub>L \<and>"} \vskip 0pt
@{text [source, break] "(\<forall>p \<in> P\<^sub>R. l \<le> fst p) \<and> sparse (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) P\<^sub>R \<and>"} \vskip 0pt
@{text [source, break] "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> sparse (dist p\<^sub>0 p\<^sub>1) (set ps)"}
\end{lemma}

One can also show that \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> are in \<open>ps\<close> and distinct (and thus a closest pair of @{term "set ps"}), 
if \<open>p\<^sub>0\<^sub>L\<close> (\<open>p\<^sub>0\<^sub>R\<close>) and \<open>p\<^sub>1\<^sub>L\<close> (\<open>p\<^sub>1\<^sub>R\<close>) are in \<open>P\<^sub>L\<close> (\<open>P\<^sub>R\<close>) and distinct.

\subsection{The Divide \& Conquer Algorithm} \label{subsection:dc:fc}

In Section \ref{section:closest_pair_algorithm} we glossed over some implementation detail which
is necessary to achieve to running time of $\mathcal{O}(n \log n)$. In particular
we need to partition the given list\footnote{Our implementation deals with
concrete lists in contrast to the abstract sets used in Section \ref{section:closest_pair_algorithm}.} of points $\mathit{ps}$
along a vertical line $l$ into two lists of nearly equal length during the divide step and obtain
a list $\mathit{ys}$ of the same points, sorted in ascending order by $y$-coordinate, for the @{const combine}
step in \emph{linear} time at each level of recursion.

Cormen \emph{et al.} propose the following top-down approach: Their algorithm takes three arguments: the set 
of points \<open>P\<close> and lists \<open>xs\<close> and \<open>ys\<close> which contain the same set of points \<open>P\<close> but are respectively 
sorted by \<open>x\<close> and \<open>y\<close>-coordinate. The algorithm first splits \<open>xs\<close> at \<open>length xs div 2\<close> into two still
sorted lists \<open>xs\<^sub>L\<close> and \<open>xs\<^sub>R\<close> and chooses \<open>l\<close> as either the \<open>x\<close>-coordinate of the last element of \<open>xs\<^sub>L\<close>
or the \<open>x\<close>-coordinate of the first element of \<open>xs\<^sub>R\<close>. It constructs the sets \<open>P\<^sub>L\<close> and \<open>P\<^sub>R\<close> respectively consisting
of the points of \<open>xs\<^sub>L\<close> and \<open>xs\<^sub>R\<close>. For the recursive invocations it needs to obtain in addition lists 
\<open>ys\<^sub>L\<close> and \<open>ys\<^sub>R\<close> that are still sorted by \<open>y\<close>-coordinate and again respectively refer to the same points as
\<open>xs\<^sub>L\<close> and \<open>xs\<^sub>R\<close>. It achieves this by iterating once through \<open>ys\<close> and checking for each point if it is
contained in \<open>P\<^sub>L\<close> or not, constructing \<open>ys\<^sub>L\<close> and \<open>ys\<^sub>R\<close> along the way.

But this approach requires an implementation of sets. In fact, if we want to
achieve the overall worst case running time of $\mathcal{O}(n \log n)$ it requires an implementation
of sets with linear time construction and constant time membership test, which is nontrivial, in 
particular in a functional setting. To avoid sets many publications and implementations either assume
all points have unique \<open>x\<close>-coordinates or preprocess the points by applying for example a rotation
such that the input fulfills this condition. For distinct \<open>x\<close>-coordinates one can then compute \<open>ys\<^sub>L\<close> 
and \<open>ys\<^sub>R\<close> by simply filtering \<open>ys\<close> depending on the \<open>x\<close>-coordinate of the points relative to \<open>l\<close> and 
eliminate the usage of sets entirely.

But there exists a third option which we have found only in Cormen \emph{et al.} where it is merely hinted at in an exercise left to the reader. The approach is the following.
Looking at the overall structure of the closest pair algorithm
we recognize that it closely resembles the structure of a standard mergesort implementation and that 
we only need \<open>ys \<close> for the @{const combine} step \emph{after} the two recursive invocations of the algorithm. 
Thus we can obtain \<open>ys\<close> by merging `along the way' using a bottom-up approach. This is the actual code:

\begin{quote}
@{term [source, break] "closest_pair_rec :: point list \<Rightarrow> point list \<times> point \<times> point"} \vskip 0pt
@{thm [break, margin=70] closest_pair_rec_simp}
\end{quote}

\begin{quote}
@{term [source, break] "closest_pair :: point list \<Rightarrow> point \<times> point"} \vskip 0pt
@{thm [break] (concl) closest_pair_simp}
\end{quote}

Function @{const closest_pair_rec} expects a list of points \<open>xs\<close> sorted by \<open>x\<close>-coordinate. The
construction of \<open>xs\<^sub>L\<close>, \<open>xs\<^sub>R\<close> and \<open>l\<close> is analogous to Cormen \emph{et al}. In the base case we then
sort \<open>xs\<close> by \<open>y\<close>-coordinate and compute the closest pair using the brute-force approach 
(@{const closest_pair_bf}). The recursive call of the algorithm on \<open>xs\<^sub>L\<close> returns in addition to the 
closest pair of \<open>xs\<^sub>L\<close> the list \<open>ys\<^sub>L\<close>, containing all points of \<open>xs\<^sub>L\<close> but now sorted by \<open>y\<close>-coordinate. 
Analogously for \<open>xs\<^sub>R\<close> and \<open>ys\<^sub>R\<close>. Furthermore, we reuse function @{const merge} from our @{const mergesort} 
implementation, which we utilize to presort the points by \<open>x\<close>-coordinate, to obtain \<open>ys\<close> from \<open>ys\<^sub>L\<close> 
and \<open>ys\<^sub>R\<close> in linear time at each level of recursion.

Splitting of \<open>xs\<close> is performed
by the function @{const split_at} via a simple linear pass over \<open>xs\<close>. Our implementation of 
@{const mergesort} sorts a list of points depending on a given projection function, @{const fst} 
for `by \<open>x\<close>-coordinate' and @{const snd} for `by \<open>y\<close>-coordinate'. 

Using Lemma \ref{lemma:combine_dist}, the functional correctness proofs of our mergesort implementation
and several auxiliary lemmas proving that \textit{closest\_pair\_rec} also sorts the points by $y$-coordinate,
we arrive at the correctness proof of the desired sparsity property of the algorithm.

\begin{theorem}
@{text [source, break] "1 < length xs \<and> sorted_fst xs \<and> (ys, p\<^sub>0, p\<^sub>1) = closest_pair_rec xs"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> sparse (dist p\<^sub>0 p\<^sub>1) xs"}
\end{theorem}

Corollary \ref{cor:closest_pair_dist} together with Theorems \ref{thm:closest_pair_set} and 
\ref{thm:closest_pair_distinct} then show that the pair \<open>(p\<^sub>0, p\<^sub>1)\<close> is indeed a closest pair of \<open>ps\<close>.

\begin{corollary} \label{cor:closest_pair_dist}
@{text [source, break] "1 < length ps \<and> (p\<^sub>0, p\<^sub>1) = closest_pair ps"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> sparse (dist p\<^sub>0 p\<^sub>1) ps"}
\end{corollary}


\begin{theorem} \label{thm:closest_pair_set}
@{text [source, break] "1 < length ps \<and> (p\<^sub>0, p\<^sub>1) = closest_pair ps"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> p\<^sub>0 \<in> set ps \<and> p\<^sub>1 \<in> set ps"}
\end{theorem}

\begin{theorem} \label{thm:closest_pair_distinct}
@{text [source, break] "1 < length ps \<and> distinct ps \<and> (p\<^sub>0, p\<^sub>1) = closest_pair ps"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> p\<^sub>0 \<noteq> p\<^sub>1"}
\end{theorem}


\section{Time Complexity Proof} \label{section:proving_running_time}

To formally verify the running time we follow the approach in \cite{Nipkow-APLAS17}. For each function @{text f}
we define a function @{text "t_f"} that takes the same arguments as @{text f} but computes the number of function
calls the computation of @{text f} needs, the `time'. Function @{text "t_f"} follows the same recursion
structure as @{text f} and can be seen as an abstract interpretation of @{text f}. For simplicity of presentation
we define @{text f} and @{text "t_f"} directly rather than deriving them from a monadic function that computes
both the value and the time. We also simplify matters a bit: we count only expensive operations where the running time increases with the size of the input; in particular we assume constant time arithmetic and ignore small additive constants. Due to reasons of space we only show
one example of such a `timing' functon, @{const t_find_closest}, which is crucial to our time
complexity proof. 

\begin{quote}
@{term [source, break] "t_find_closest :: point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> nat"} \vskip 0pt
@{text "t_find_closest p \<delta> [] = 0"} \vskip 0pt
@{text "t_find_closest p \<delta> [p\<^sub>0] = 1"} \vskip 0pt
@{text "t_find_closest p \<delta> (p\<^sub>0 # ps) = 1 +"} \vskip 0pt
@{text "(\<^latex>\<open>\\textsf{\<close>if\<^latex>\<open>}\<close> \<delta> \<le> snd p\<^sub>0 - snd p \<^latex>\<open>\\textsf{\<close>then\<^latex>\<open>}\<close> 0"} \vskip 0pt
\ @{text "\<^latex>\<open>\\textsf{\<close>else\<^latex>\<open>}\<close> \<^latex>\<open>\\textsf{\<close>let\<^latex>\<open>}\<close> p\<^sub>1 = find_closest p (min \<delta> (dist p p\<^sub>0)) ps"} \vskip 0pt
\ \qquad@{text "\<^latex>\<open>\\textsf{\<close>in\<^latex>\<open>}\<close> t_find_closest p (min \<delta> (dist p p\<^sub>0)) ps +"} \vskip 0pt
\ \quad\qquad@{text "(\<^latex>\<open>\\textsf{\<close>if\<^latex>\<open>}\<close> dist p p\<^sub>0 \<le> dist p p\<^sub>1 \<^latex>\<open>\\textsf{\<close>then\<^latex>\<open>}\<close> 0 \<^latex>\<open>\\textsf{\<close>else\<^latex>\<open>}\<close> 0))"}
\end{quote}
%TODO less about base cases?
We set the time to execute @{const dist} computations to @{text 0} since it is a combination
of cheap operations. For the base cases of recursive functions
we fix the computation time to be equivalent to the size of the input. This choice of constants is arbitrary and has no
impact on the overall running time analysis but leads in general to `cleaner' arithmetic bounds. 
%Note that it might be of interest to define a similar abstract interpretation to count the number of 
%@{const dist} computations of the algorithm and compare different implementation approaches with 
%regard to this number. Since we choose not to minimize the number of @{const dist} computations,
%except for the final executable code in Section \ref{section:executable_code}, we omit such an analysis.

\subsection{Time Analysis of the Combine Step}

In Section \ref{section:closest_pair_algorithm} we claimed that the running time of the algorithm is
captured by the recurrence @{text "T(n) = T(\<lceil>n/2\<rceil>) + T(\<lfloor>n/2\<rfloor>) + O(n)"},
where @{term n} is the length of the given list of points. This claim implies an at most linear overhead
at each level of recursion. Splitting of the list @{term xs}, merging @{term ys\<^sub>L} and @{term ys\<^sub>R} and
the filtering operation of the @{const combine} step run in linear time. But it is non-trivial that the 
function @{const find_closest_pair}, central to the @{const combine} step, also exhibits a linear
time complexity. It is applied to an argument list of, in the worst case, length @{term n}, iterates
once through the list and calls @{const find_closest} for each element. Consequently our proof obligation
is the constant running time of @{const find_closest} or, considering our timing function, that there exists
some constant @{term c} such that @{term "t_find_closest p \<delta> ps \<le> c"} holds in the context of the @{const combine} step.

Looking at the definition of @{const find_closest} we see that the function terminates as soon as 
it encounters the first point within the given list @{term ps} that does not fulfill the predicate 
(@{term "\<lambda>q. \<delta> \<le> snd q - snd p"}), the point @{term p} being an argument to @{const find_closest},
or if @{term ps} is a list of length @{text "\<le>1"}. The corresponding timing function @{const t_find_closest} 
computes the number of recursive function calls, which is, in this case, synonymous with the number of examined points.
For our time complexity proof it suffices to show the following bound on the result of  @{const t_find_closest}.
The proof is by induction on the computation of @{const t_find_closest}. The function @{text "count f"} is
an abbreviation for @{text "length \<circ> filter f"}.

\begin{lemma}
@{text [break] "t_find_closest p \<delta> ps \<le> 1 + count (\<lambda>q. snd q - snd p \<le> \<delta>) ps"}
\end{lemma}

Therefore we need to prove that the term  @{text "count (\<lambda>q. snd q - snd p \<le> \<delta>) ps"} does not depend
on the length of \<open>ps\<close>. Looking back at Figure \ref{fig:Combine}, the square point representing \<open>p\<close>, 
we can assume that the list @{term "p # ps"} is distinct and sorted in ascending order by \<open>y\<close>-coordinate. 
From the precomputing effort of the @{const combine} step we know that its points are contained 
within the @{text "2\<delta>"} wide vertical strip centered around @{term l} and can be split into two sets @{term P\<^sub>L}
(@{term P\<^sub>R}) consisting of all points which lie to the left (right) of or on the line @{term l}, respectively.
Due to the two recursive invocations of the algorithm during the conquer step we can additionally assume
that both @{term P\<^sub>L} and @{term P\<^sub>R} are @{term \<delta>}-sparse, suggesting the following lemma which implies
@{term "t_find_closest p \<delta> ps \<le> 8"} and thus the constant running time of @{const find_closest}.

\begin{lemma} \label{lemma:core_argument}
@{text [source, break] "distinct (p # ps) \<and> sorted_snd (p # ps) \<and> 0 \<le> \<delta> \<and>"} \vskip 0pt
@{text [source, break] "(\<forall>q \<in> set (p # ps). l - \<delta> < fst q \<and> fst q < l + \<delta>) \<and>"} \vskip 0pt
@{text [source, break] "set (p # ps) = P\<^sub>L \<union> P\<^sub>R \<and>"} \vskip 0pt
@{text [source, break] "(\<forall>q \<in> P\<^sub>L . fst q \<le> l) \<and> sparse \<delta> P\<^sub>L \<and>"} \vskip 0pt
@{text [source, break] "(\<forall>q \<in> P\<^sub>R . l \<le> fst q) \<and> sparse \<delta> P\<^sub>R"} \vskip 0pt
@{text [source, break] "\<Longrightarrow>"} @{text [break] "count (\<lambda>q. snd q - snd p \<le> \<delta>) ps \<le> 7"}
\end{lemma}
\begin{proof}
The library HOL-Analysis defines some basic geometric building blocks needed for the proof. A \textit{closed box}
describes points contained within rectangular shapes in Euclidean space. For our purposes the planar definition is sufficient.

\begin{quote}
@{thm [display] cbox_2D}
\end{quote}

The box is `closed' since it includes points located on the border of the box. We then introduce
some useful abbreviations:

\begin{itemize}
\setlength{\itemsep}{1pt}
\setlength{\parskip}{0pt}
\setlength{\parsep}{0pt}
\item The rectangle \<open>R\<close> is the upper half of the shaded square of Figure \ref{fig:Combine}: \\
      @{term "R = cbox (l - \<delta>, snd p) (l + \<delta>, snd p + \<delta>)"}
\item The set \<open>R\<^sub>p\<^sub>s\<close> consists of all points of @{term "p # ps"} that are encompassed by \<open>R\<close>: \\
      @{term "R\<^sub>p\<^sub>s = R \<inter> set (p # ps)"}
\item The squares \<open>S\<^sub>L\<close> and \<open>S\<^sub>R\<close> denote the left and right halves of \<open>R\<close>: \\
      @{term "S\<^sub>L = cbox (l - \<delta>, snd p) (l, snd p + \<delta>)"} \\
      @{term "S\<^sub>R = cbox (l, snd p) (l + \<delta>, snd p + \<delta>)"}
\item The set \<open>S\<^sub>P\<^sub>L\<close> holds all points of \<open>P\<^sub>L\<close> that are contained within the square \<open>S\<^sub>L\<close>. The definition
      of \<open>S\<^sub>P\<^sub>R\<close> is analogous: \\
      @{term "S\<^sub>P\<^sub>L = P\<^sub>L \<inter> S\<^sub>L"}, @{term "S\<^sub>P\<^sub>R = P\<^sub>R \<inter> S\<^sub>R"}
\end{itemize}

Let additionally \<open>ps\<^sub>f\<close> abbreviate the term @{term "filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps"}.
First we prove @{term "length (p # ps\<^sub>f) \<le> card R\<^sub>p\<^sub>s"}: Let \<open>q\<close> denote an arbitrary point of \mbox{\<open>p # ps\<^sub>f\<close>}. We know
@{term "snd p \<le> snd q"} because the list @{term "p # ps"} and therefore \mbox{\<open>p # ps\<^sub>f\<close>} is sorted in ascending order by \<open>y\<close>-coordinate and
\mbox{@{term "snd q \<le> snd p + \<delta>"}} due to the filter predicate (@{term "\<lambda>q. snd q - snd p \<le> \<delta>"}). 
Using the additional facts @{term "l - \<delta> \<le> fst q"} and @{term "fst q \<le> l + \<delta>"} (derived from our assumption
that all points of @{term "p # ps"} are contained within the @{text "2\<delta>"} strip)
and the definitions of \<open>R\<^sub>p\<^sub>s\<close>, \<open>R\<close> and @{const cbox} we know @{term "q \<in> R\<^sub>p\<^sub>s"} and thus @{term "set (p # ps\<^sub>f) \<subseteq> R\<^sub>p\<^sub>s"}. 
Since the list \<open>p # ps\<^sub>f\<close> maintains the distinctness property of @{term "p # ps"} we additionally have 
\mbox{@{term "length (p # ps\<^sub>f) = card (set (p # ps\<^sub>f))"}}. Our intermediate goal immediately follows because 
@{term "card (set (p # ps\<^sub>f)) \<le> card R\<^sub>p\<^sub>s"} holds for the finite set \<open>R\<^sub>p\<^sub>s\<close>.

But how many points can there be in \<open>R\<^sub>p\<^sub>s\<close>? Lets first try to determine an upper bound for the number of points of \<open>S\<^sub>P\<^sub>L\<close>.
All its points are contained within the square \<open>S\<^sub>L\<close> whose side length is \<open>\<delta>\<close>. Moreover, since \<open>P\<^sub>L\<close> is \<open>\<delta>\<close>-sparse and 
\mbox{\<open>S\<^sub>P\<^sub>L \<subseteq> P\<^sub>L\<close>}, \<open>S\<^sub>P\<^sub>L\<close> is also \<open>\<delta>\<close>-sparse, or the distance between each distinct pair of points of \<open>S\<^sub>P\<^sub>L\<close> is at least \<open>\<delta>\<close>.
Therefore the cardinality of \<open>S\<^sub>P\<^sub>L\<close> is bounded by the number of points we can maximally fit into \<open>S\<^sub>L\<close>, maintaining
a pairwise minimum distance of \<open>\<delta>\<close>. As the left-hand side of Figure \ref{fig:core_arguments} depicts, we can arrange at most four points
adhering to these restrictions, and consequently have @{term "card S\<^sub>P\<^sub>L \<le> 4"}. An analogous argument holds for
the number of points of \<open>S\<^sub>P\<^sub>R\<close>. Furthermore we know @{term "R\<^sub>p\<^sub>s = S\<^sub>P\<^sub>L \<union> S\<^sub>P\<^sub>R"} due to our assumption
@{term "set (p # ps) = P\<^sub>L \<union> P\<^sub>R"} and the fact @{term "R = S\<^sub>L \<union> S\<^sub>R"} and can conclude @{term "card R\<^sub>p\<^sub>s \<le> 8"}.
Our original statement then follows from @{term "length (p # ps\<^sub>f) \<le> card R\<^sub>p\<^sub>s"}.
\qed
\end{proof}
%
\begin{figure}[htpb]
\centering
\includegraphics[width=0.75\textwidth]{./../../img/Core_Arguments.png}
\caption[]{Core Argument.}
\label{fig:core_arguments}
\end{figure}
%
Note that the intermediate proof for the bound on @{term "card R\<^sub>p\<^sub>s"} relies on basic human geometric intuition. 
Indeed Cormen \emph{et al.} \cite{Introduction-to-Algorithms:2009} and most of the proofs in the literature do.
But for a formal proof we have to be rigorous. First we show two auxiliary lemmas: The maximum distance
between two points in a square \<open>S\<close> with side length \<open>\<delta>\<close> is less than or equal to $\sqrt{2}\delta$. 

\begin{lemma} \label{lemma:max_dist_square}
@{text [source, break] "p\<^sub>0 = (x, y) \<and> p\<^sub>1 = (x + \<delta>, y + \<delta>) \<and> 0 \<le> \<delta> \<and>"} \vskip 0pt
@{text [source, break] "(x\<^sub>0, y\<^sub>0) \<in> cbox p\<^sub>0 p\<^sub>1 \<and> (x\<^sub>1, y\<^sub>1) \<in> cbox p\<^sub>0 p\<^sub>1"} \vskip 0pt
@{text [source ,break] "\<Longrightarrow> dist (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<le> \<^latex>\<open>$\\sqrt{2}$\<close> * \<delta>"}
\end{lemma}

The proof is straightforward. Both points are contained within the square \<open>S\<close>, the difference between
their \<open>x\<close> and \<open>y\<close> coordinates is hence bounded by \<open>\<delta>\<close> and we finish the proof using the definition of the Euclidean
distance. Below we employ the following variation of the \textit{pigeonhole} principle:

\begin{lemma} \label{lemma:pigeonhole}
@{text [source, break] "finite B \<and> A \<subseteq> \<Union>B \<and> "} @{term "card B < card A"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> \<exists>x \<in> A. \<exists>y \<in> A. \<exists>S \<in> B. x \<noteq> y \<and> x \<in> S \<and> y \<in> S"}
\end{lemma}

%The proof is by contradiction using the following chain of inequalities:
%$$\lvert B \rvert < \lvert A \cap \bigcup B \rvert \le \sum S \in B.\ \lvert A \cap S \rvert \le \lvert B \rvert$$
%The first inequality holds using our assumptions @{term "A \<subseteq> \<Union>B"} and @{term "card B < card A"}.
%The second inequality can be shown by induction over the cardinality of \<open>B\<close>. Let then \<open>x\<close> and \<open>y\<close> denote 
%arbitrary elements of \<open>A\<close> and \<open>S\<close> be an arbitrary set of \<open>B\<close>. Suppose, for the sake of contradiction,
%either @{term "x = y"}, or @{term "x \<notin> S"}, or @{term "y \<notin> S"} then @{term "card (A \<inter> S) \<le> 1"} must hold. The proof
%is again by contradiction: Suppose @{term "card (A \<inter> S) > 1"}, then there exists a distinct pair of elements
%which are both element of \<open>S\<close>. A contradiction to our previous assumptions for \<open>x\<close> and \<open>y\<close>. Thus the third inequality
%is correct and we have shown @{term "card B < card B"}, a contradiction.

Finally we replace human intuition with formal proof:

\begin{lemma}
@{text [source, break] "(\<forall>p \<in> P. p \<in> cbox (x, y) (x + \<delta>, y + \<delta>)) \<and> sparse \<delta> P \<and> 0 \<le> \<delta>"} \vskip 0pt
@{text [source, break] "\<Longrightarrow>"} @{term "card P \<le> 4"}
\end{lemma}
\begin{proof}
Let \<open>S\<close> denote the square with a side length of \<open>\<delta>\<close> and suppose, for the sake of contradiction, that @{term "card P > 4"}.
Then \<open>S\<close> can be split into the four congruent squares @{text "S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4"} along the common point
@{text "(x + \<delta>/2, y + \<delta>/2)"} as depicted by the right-hand side of Figure \ref{fig:core_arguments}. 
Since all points of \<open>P\<close> are contained within \<open>S\<close> and @{term "S = \<Union>{S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4}"} we have @{term "P \<subseteq> \<Union>{S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4}"}.
Using Lemma \ref{lemma:pigeonhole} and our assumption  @{term "card P > 4"} we know there exists a square 
\mbox{@{term "S\<^sub>i \<in> {S\<^sub>1, S\<^sub>2, S\<^sub>3, S\<^sub>4}"}} and a pair of distinct points @{term "p\<^sub>0 \<in> S\<^sub>i"} and @{term "p\<^sub>1 \<in> S\<^sub>i"}.
Lemma \ref{lemma:max_dist_square} and the fact that all four sub-squares have the same side length @{text "\<delta> / 2"}
shows that the distance between \<open>p\<^sub>0\<close> and \<open>p\<^sub>1\<close> must be less than or equal to @{text "\<^latex>\<open>$\\sqrt{2}$\<close> / 2 * \<delta>"} and hence
strictly less than \<open>\<delta>\<close>. But we also know that \<open>\<delta>\<close> is a lower bound for this distance because @{term "p\<^sub>0 \<in> P"},
@{term "p\<^sub>0 \<in> P"}, @{term "p\<^sub>0 \<noteq> p\<^sub>1"} and our premise that \<open>P\<close> is \<open>\<delta>\<close>-sparse, a contradiction.\qed
\end{proof}

\subsection{Time Analysis of the Divide \& Conquer Algorithm}

In summary, the time to evaluate @{term "find_closest p \<delta> ps"} is constant in the context of the @{const combine} step
and thus evaluating @{term "find_closest_pair (p\<^sub>0, p\<^sub>1) ps"} as well as @{term "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"} 
takes time linear in @{term "length ps"}.

Next we turn our attention to the timing of @{const closest_pair_rec}
and define (but do not show) the corresponding function @{const t_closest_pair_rec}.
At this point we could prove a concrete bound on @{const t_closest_pair_rec}.
But since we are dealing with a divide-and-conquer algorithm we should, in theory, be able to determine its
running time using the `master theorem' \cite{Introduction-to-Algorithms:2009}. This is, in practice, also
possible in Isabelle/HOL. Eberl \cite{eberl_akra_bazzi} has formalized the Akra-Bazzi theorem \cite{Akra1998}, 
a generalization of the master theorem. Using this formalization we can derive the running time of 
our divide-and-conquer algorithm without a direct proof for @{const t_closest_pair_rec}. First
we capture the essence of @{const t_closest_pair_rec} as a recurrence on natural numbers 
representing the length of the list argument of \<open>(t_)\<close>@{const closest_pair_rec}:
%
\begin{quote}
@{text [source] "closest_pair_recurrence :: nat \<Rightarrow> real"} \vskip 0pt
@{thm [break] closest_pair_rec_recurrence_simps}
\end{quote}

The time complexity of this recurrence is proved completely automatically:

\begin{lemma} \label{lemma:closest_pair_recurrence}
@{text "closest_pair_recurrence \<in> \<Theta>(\<lambda>n. n * \<^latex>\<open>$\\ln$\<close> n)"}
\end{lemma}

Next we need to connect this bound with our timing function. Lemma \ref{lemma:bigo_measure_trans} below 
expresses a procedure for deriving complexity properties of the form

\begin{quote}
@{prop "t \<in> O[m going_to at_top within A](f o m)"}
\end{quote}

where \<open>t\<close> is a timing function on the data domain, in our case lists. The function \<open>m\<close> is a measure 
on that data domain, \<open>r\<close> is a recurrence or any other function of type @{text "nat \<Rightarrow> real"} and \<open>A\<close> 
is the set of valid inputs. The term `@{text "m going_to at_top within A"}' should be read as 
`if the measured size of valid inputs is sufficiently large' and utilizes Eberls formalization of
Landau Notation \cite{eberl19issac} and the ``filter'' machinery of asymptotics in Isabelle/HOL 
\cite{filter}. For readability we omit stating the filter and \<open>m\<close> explicitly in the following and 
just state the  conditions required of the input \<open>A\<close>. The measure \<open>m\<close> always corresponds to the 
@{const length} function.

\begin{lemma} \label{lemma:bigo_measure_trans}
@{text [source, break] "(\<forall>x \<in> A. t x \<le> (r \<circ> m) x) \<and> r \<in> O(f) \<and> (\<forall>x \<in> A. 0 \<le> t x)"} \vskip 0pt
@{text [source, break] "\<Longrightarrow> t \<in> O[m going_to at_top within A](f \<circ> m)"}
\end{lemma}

\begin{lemma}\label{lemma:recurrence}
@{prop "distinct ps \<and> sorted_fst ps"} \vskip 0pt
\<open>\<Longrightarrow>\<close> @{prop "t_closest_pair_rec ps \<le> (closest_pair_recurrence \<circ> length) ps"}
\end{lemma}

Using Lemmas \ref{lemma:closest_pair_recurrence}, \ref{lemma:bigo_measure_trans} and \ref{lemma:recurrence}
we arrive at Theorem \ref{thm:t_closest_pair_rec}, expressing our main claim: the running time of the 
divide-and-conquer algorithm.

\begin{theorem} \label{thm:t_closest_pair_rec}
For inputs that are \<open>distinct\<close> and sorted by \<open>x\<close>-coordinate: \vskip 0pt
@{text [break] "t_closest_pair_rec \<in> O(\<lambda>n. n * \<^latex>\<open>$\\ln$\<close> n)"}
\end{theorem}

Since the function @{const closest_pair} only presorts the given list of points using our mergesort implementation and 
then calls @{const closest_pair_rec} we obtain Corollary \ref{cor:t_closest_pair}
and finish the time complexity proof.

\begin{corollary} \label{cor:t_closest_pair}
For \<open>distinct\<close> inputs:
@{text [break] "t_closest_pair \<in> O(\<lambda>n. n * \<^latex>\<open>$\\ln$\<close> n)"}
\end{corollary}


\section{Alternative Implementations} \label{section:alt_impl}

In the literature there exist various other algorithmic approaches to solve the closest pair problem. 
Most of them are closely related to our implementation of Section \ref{section:proving_functional_correctness},
deviating primarily in two aspects: the exact implementation of the @{const combine} step and the approach
to sorting the points by \<open>y\<close>-coordinate we already discussed in Subsection \ref{subsection:dc:fc}. We 
present a short overview, concentrating on the @{const combine} step and the second implementation we verified.

\subsection{A Second Verified Implementation} \label{subsection:snd}

Although the algorithm described by Cormen \emph{et al.} is the basis for our implementation of 
Section \ref{section:proving_functional_correctness}, we took the liberty to
optimize it. During execution of @{term "find_closest p \<delta> ps"} our algorithm
searches for the closest neighbor of \<open>p\<close> within the rectangle \<open>R\<close>, the upper half of the shaded 
square \<open>S\<close> of Figure \ref{fig:Combine}, and terminates the search if it examines points on or beyond 
the upper border of \<open>R\<close>. Cormen \emph{et al.} originally follow a slightly different approach. They 
search for a closest neighbor of \<open>p\<close> by examining a constant number of points of \<open>ps\<close>, the first 
@{text 7} to be exact. This is valid because there are at most @{text 7} points within \<open>R\<close>, not 
counting \<open>p\<close>, and the @{text 8}th point of \<open>ps\<close> would again lie on or beyond the upper border of \<open>R\<close>.
This slightly easier implementation comes at the cost of being less efficient in practice.
Cormen \emph{et al.} are always assuming the worst case by checking all @{text 7} points following \<open>p\<close>.
But it is unlikely that the algorithm needs to examine even close to @{text 7} points, except for specifically
constructed inputs. They furthermore state that the bound of @{text 7} is an over-approximation 
and dare the reader to lower it to \<open>5\<close> as an exercise. We refrain from doing so since a bound of 
\<open>7\<close> suffices for the time complexity proof of our, inherently faster, implementation. At 
this point we should also mention that the specific optimization of Section~\ref{section:proving_functional_correctness}
is not our idea but rather an algorithmic detail which is unfortunately rarely mentioned in the
literature.

Nonetheless we can adapt the implementation of Section \ref{section:proving_functional_correctness} and the proofs 
of Section \ref{section:proving_running_time} to verify the original implementation of Cormen \emph{et al.} as follows:
We replace each call of @{term "find_closest p \<delta> ps"} by a call to @{term "find_closest_bf p (take 7 ps)"} 
where @{const find_closest_bf} iterates in brute-force fashion through its argument list to find the 
closest neighbor of \<open>p\<close>. To verify this implementation we then reuse most of the elementary lemmas and proof 
structure of Sections \ref{section:proving_functional_correctness} and \ref{section:proving_running_time}, 
only a slightly adapted version of Lemma \ref{lemma:core_argument} is necessary. Note that this lemma was
previously \emph{solely} required for the time complexity proof of the algorithm. Now it is already necessary 
during the functional correctness proof since we need to argue that examining only a constant number of 
points of \<open>ps\<close> is sufficient. The time analysis is overall greatly simplified: A call of the form 
@{term "find_closest_bf p (take 7 ps)"} runs in constant time and we again are able to reuse the remaining 
time analysis proof structure of Section \ref{section:proving_running_time}. For the exact differences
between both formalizations we encourage the reader the consult our entry in the Archive of Formal Proofs 
@{cite "Closest_Pair_Points-AFP"}.

\subsection{Related Work}

Over the years a considerable amount of effort has been made to further optimize the @{const combine} step.
Central to these improvements is the `complexity of computing distances', abbreviated CCP in the following, 
a term introduced by \mbox{Zhou \emph{et al.}~\cite{zhou1998improved}} which measures the number of Euclidean 
distances computed by a closest pair algorithm. The core idea being, since computing the Euclidean 
distance is more expensive than other primitive operations, it might be possible to improve overall 
algorithmic running time by reducing this complexity measure. In the same paper they introduce an 
optimized version of the closest pair algorithm with a CCP of $2n \log n$, in contrast to $7n \log n$ 
which will be the worst case CCP of the algorithm of Section \ref{section:proving_functional_correctness} 
after we minimize the number of distance computations in Section \ref{section:executable_code}. They
improve upon the algorithm presented by Preparata and Shamos \cite{Computational-Geometry-An-Introduction:1985} 
which achieves CCP of $3n \log n$. Ge \emph{et al.} \cite{Ge2006} base their, quite sophisticated, 
algorithm on the version of Zhou \emph{et al.} and prove an even lower CCP of $\frac{3}{2}n \log n$ 
for their implementation. The race for the lowest number of distance computations culminates so far 
with the work of Jiang and Gillespie~\cite{jiang2007engineering} who present their algorithms `Basic-2' 
\footnote{Pereira and Lobo \cite{pereira2012optimized} later independently developed the same algorithm 
and additionally present extensive functional correctness proofs for all Minkowski distances.} and 
`2-Pass' with a respective CCP of $2n \log n$ and (for the first time linear) $\frac{7}{2}n$.

\section{Executable Code} \label{section:executable_code}

Before we explore how our algorithm stacks up against Basic-2 (which is surprisingly the fastest of 
the CCP minimizing algorithms according to Jiang and Gillespie) we have to make some final adjustments 
to generate executable code from our formalization.

In Section \ref{section:proving_functional_correctness} we fixed the data representation of a point 
to be a pair of mathematical ints rather than mathematical reals. During code export Isabelle 
can then correctly and automatically maps its abstract data type @{typ int} to a suitable concrete 
implementation of (arbitrary-sized) integers; for our target language OCaml using the library `zarith'. 
For the data type @{typ real} this is not possible since we cannot implement mathematical reals. We would instead 
have to resort to an approximation (e.g. floats) losing all proved guarantees in the process. 
But currently our algorithm still uses the standard Euclidean distance and hence mathematical reals due 
to the @{const sqrt} function. For the executable code we have to replace this distance measure by the 
squared Euclidean distance. To prove that we preserve the correctness of our implementation several 
small variations of the following lemma suffice:
%
\begin{quote}
@{text [display] "dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>2 p\<^sub>3 \<longleftrightarrow> (dist p\<^sub>0 p\<^sub>1)\<^sup>2 \<le> (dist p\<^sub>2 p\<^sub>3)\<^sup>2"}
\end{quote}
%
We apply two further code transformations. To minimize the number of distance computations we introduce 
auxiliary variables which capture and then replace repeated computations. For all of the shown
functions that return a point or a pair of points this entails returning the 
corresponding computed distance as well. Furthermore we replace recursive auxiliary functions such as 
@{const filter} by corresponding tail-recursive implementations to allow the OCaml compiler to 
optimize the generated code and prevent stackoverflows. To make sure these transformations are correct 
we prove lemmas expressing the equivalence of old and new implementations for each function.
Isabelles code export machinery can then apply these transformations automatically.

Now it is time to evaluate the performance of our verified code. 
Figure \ref{fig:benchmark} depicts the running time ratios of several implementations of the algorithm 
of Section \ref{section:proving_functional_correctness} (called Basic-\<open>\<delta>\<close>) and Basic-7 (the original
approach of Cormen \emph{et al.}) over Basic-2. Basis-\<open>\<delta>\<close> is tested in three variations: the exported 
(purely functional) Isabelle code and equivalent handwritten functional and imperative implementations
to gauge the overhead of the machine generated code. All algorithms are implemented in OCaml, use our 
bottom-up approach to sorting (imperative implementations sort in place) of Subsection \ref{subsection:dc:fc} 
and for each input of uniformly distributed points 50 independent executions were performed.
Remarkably the exported code is only about 2.28 \footnote{We measure differences between 
running times as the average over all data points weighted by the size of the input.} 
times slower than Basic-2 and furthermore most of the difference is caused by the inefficiencies 
inherent to machine generated code since its equivalent functional implementation is only 11\% 
slower than Basic-2. Basic-7 is 2.26 times slower than the imperative Basic-\<open>\<delta>\<close> which demonstrates 
the huge impact the small optimization of Subsection \ref{subsection:snd} can have in practice.
%
\begin{figure}[htpb]
\centering
\includegraphics[width=0.8\textwidth]{./../../benchmark/Benchmarks2.png}
\caption[]{Benchmarks.} 
\label{fig:benchmark}
\end{figure}
%
\section{Conclusion} \label{section:conclusion}

We have presented the first verification (both functional correctness and running time) of two related 
closest pair of points algorithms in the plane, without assuming the \<open>x\<close> coordinates of all points 
are distinct. The executable code generated from the formalization is competitive with existing 
reference implementations. A challenging and rewarding next step would be to formalize and verify a 
closest pair of points algorithm in arbitrary dimensions. This case is treated rather sketchily in the literature.

\paragraph{Acknowledgements}
Research supported by DFG grants NI 491/16-1 and 18-1.
\<close>

(*<*)
end
(*>*)
