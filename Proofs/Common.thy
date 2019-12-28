theory Common
imports 
  "HOL-Analysis.Analysis"
  "Landau_Symbols.Landau_More"
  "HOL-Library.Going_To_Filter"
  "Akra_Bazzi.Akra_Bazzi_Method"
  "Akra_Bazzi.Akra_Bazzi_Approximation"
  "HOL-Library.Code_Target_Numeral"
begin

type_synonym point = "int * int"

section "Auxiliary Functions and Lemmas"

subsection "Landau Auxiliary"

text \<open>
  The following lemma expresses a procedure for deriving complexity properties of
  the form @{prop"t \<in> O[m going_to at_top within A](f o m)"} where
    \<^item> \<open>t\<close> is a (timing) function on same data domain (e.g. lists),
    \<^item> \<open>m\<close> is a measure function on that data domain (e.g. length),
    \<^item> \<open>t'\<close> is a function on @{typ nat},
    \<^item> \<open>A\<close> is the set of valid inputs for the data domain.
  One needs to show that
    \<^item> \<open>t\<close> is bounded by @{term "t' o m"} for valid inputs
    \<^item> @{prop"t' \<in> O(f)"}
  to conclude the overall property @{prop"t \<in> O[m going_to at_top within A](f o m)"}.
\<close>

lemma bigo_measure_trans:
  fixes t :: "'a \<Rightarrow> real" and t' :: "nat \<Rightarrow> real" and m :: "'a \<Rightarrow> nat" and f ::"nat \<Rightarrow> real"
  assumes "\<And>x. x \<in> A \<Longrightarrow> t x \<le> (t' o m) x"
      and "t' \<in> O(f)"
      and "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> t x"
  shows "t \<in> O[m going_to at_top within A](f o m)"
proof -
  have 0: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> (t' o m) x" by (meson assms(1,3) order_trans)
  have 1: "t \<in> O[m going_to at_top within A](t' o m)"
    apply(rule bigoI[where c=1]) using assms 0
    by (simp add: eventually_inf_principal going_to_within_def)
  have 2: "t' o m \<in> O[m going_to at_top](f o m)"
    unfolding o_def going_to_def
    by(rule landau_o.big.filtercomap[OF assms(2)])
  have 3: "t' o m \<in> O[m going_to at_top within A](f o m)"
    using landau_o.big.filter_mono[OF _2] going_to_mono[OF _subset_UNIV] by blast
  show ?thesis by(rule landau_o.big_trans[OF 1 3])
qed

subsection "Miscellaneous Lemmas"

lemma set_take_drop_i_le_j:
  "i \<le> j \<Longrightarrow> set xs = set (take j xs) \<union> set (drop i xs)"
proof (induction xs arbitrary: i j)
  case (Cons x xs)
  show ?case
  proof (cases "i = 0")
    case True
    thus ?thesis
      using set_take_subset by force
  next
    case False
    hence "set xs = set (take (j - 1) xs) \<union> set (drop (i - 1) xs)"
      by (simp add: Cons diff_le_mono)
    moreover have "set (take j (x # xs)) = insert x (set (take (j - 1) xs))"
      using False Cons.prems by (auto simp: take_Cons')
    moreover have "set (drop i (x # xs)) = set (drop (i - 1) xs)"
      using False Cons.prems by (auto simp: drop_Cons')
    ultimately show ?thesis
      by auto
  qed
qed simp

lemma set_take_drop:
  "set xs = set (take n xs) \<union> set (drop n xs)"
  using set_take_drop_i_le_j by fast

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  from assms have "sorted_wrt f (take n xs @ drop n xs)" by simp
  then show "sorted_wrt f (take n xs)" and "sorted_wrt f (drop n xs)"
    unfolding sorted_wrt_append by simp_all
qed

lemma sorted_wrt_filter:
  "sorted_wrt f xs \<Longrightarrow> sorted_wrt f (filter P xs)"
  by (induction xs) auto

lemma sorted_wrt_take_drop:
  "sorted_wrt f xs \<Longrightarrow> \<forall>x \<in> set (take n xs). \<forall>y \<in> set (drop n xs). f x y"
  using sorted_wrt_append[of f "take n xs" "drop n xs"] by simp

lemma sorted_wrt_hd_less:
  assumes "sorted_wrt f xs" "\<And>x. f x x"
  shows "\<forall>x \<in> set xs. f (hd xs) x"
  using assms by (cases xs) auto

lemma sorted_wrt_hd_less_take:
  assumes "sorted_wrt f (x # xs)" "\<And>x. f x x"
  shows "\<forall>y \<in> set (take n (x # xs)). f x y"
  using assms sorted_wrt_hd_less in_set_takeD by fastforce

lemma sorted_wrt_take_less_hd_drop:
  assumes "sorted_wrt f xs" "n < length xs"
  shows "\<forall>x \<in> set (take n xs). f x (hd (drop n xs))"
  using sorted_wrt_take_drop assms by fastforce

lemma sorted_wrt_hd_drop_less_drop:
  assumes "sorted_wrt f xs" "\<And>x. f x x"
  shows "\<forall>x \<in> set (drop n xs). f (hd (drop n xs)) x"
  using assms sorted_wrt_drop sorted_wrt_hd_less by blast

lemma length_filter_P_impl_Q:
   "(\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> length (filter P xs) \<le> length (filter Q xs)"
  by (induction xs) auto

lemma filter_Un:
  "set xs = A \<union> B \<Longrightarrow> set (filter P xs) = { x \<in> A. P x } \<union> { x \<in> B. P x }"
  apply (induction xs)
  apply (auto) by (metis UnI1 UnI2 insert_iff)+

subsection "length"

fun t_length :: "'a list \<Rightarrow> nat" where
  "t_length [] = 0"
| "t_length (x#xs) = 1 + t_length xs"

lemma t_length:
  "t_length xs = length xs"
  by (induction xs) auto

definition length_cost :: "nat \<Rightarrow> real" where
  "length_cost n = n"

lemma length_cost_nonneg[simp]:
  "0 \<le> length_cost n"
  unfolding length_cost_def by simp

lemma t_length_conv_length_cost:
  "t_length xs = length_cost (length xs)"
  unfolding length_cost_def using t_length by auto

fun length_it' :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "length_it' acc [] = acc"
| "length_it' acc (x#xs) = length_it' (acc+1) xs"

definition length_it :: "'a list \<Rightarrow> nat" where
  "length_it xs = length_it' 0 xs"

lemma length_conv_length_it':
  "length xs + acc = length_it' acc xs"
  by (induction acc xs rule: length_it'.induct) auto

lemma length_conv_length_it[code_unfold]:
  "length xs = length_it xs"
  unfolding length_it_def using length_conv_length_it' add_0_right by metis

subsection "rev"

fun rev_it' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_it' acc [] = acc"
| "rev_it' acc (x#xs) = rev_it' (x#acc) xs"

definition rev_it :: "'a list \<Rightarrow> 'a list" where
  "rev_it xs = rev_it' [] xs"

lemma rev_conv_rev_it':
  "rev xs @ acc = rev_it' acc xs"
  by (induction acc xs rule: rev_it'.induct) auto

lemma rev_conv_rev_it[code_unfold]:
  "rev xs = rev_it xs"
  unfolding rev_it_def using rev_conv_rev_it' append_Nil2 by metis

subsection "take"

fun t_take :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_take n [] = 0"
| "t_take n (x#xs) = 1 + (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> t_take m xs
  )"

lemma t_take:
  "t_take n xs = min (n+1) (length xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition take_cost :: "nat \<Rightarrow> real" where
  "take_cost n = real n"

lemma t_take_conv_take_cost:
  "t_take n xs \<le> take_cost (length xs)"
  unfolding take_cost_def by (auto simp: min_def t_take)

declare t_take.simps [simp del]

subsection "filter"

fun t_filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_filter P [] = 0"
| "t_filter P (x#xs) = 1 + (if P x then t_filter P xs else t_filter P xs)"

lemma t_filter:
  "t_filter P xs = length xs"
  by (induction xs) auto

definition filter_cost :: "nat \<Rightarrow> real" where
  "filter_cost n = n"

lemma t_filter_conv_filter_cost:
  "t_filter P xs = filter_cost (length xs)"
  unfolding filter_cost_def using t_filter by auto

fun filter_it' :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_it' acc P [] = rev acc"
| "filter_it' acc P (x#xs) = (
    if P x then
      filter_it' (x#acc) P xs
    else
      filter_it' acc P xs
  )"

definition filter_it :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_it P xs = filter_it' [] P xs"

lemma filter_conv_filter_it':
  "rev acc @ filter P xs = filter_it' acc P xs"
  by (induction acc P xs rule: filter_it'.induct) auto

lemma filter_conv_filter_it[code_unfold]:
  "filter P xs = filter_it P xs"
  unfolding filter_it_def using filter_conv_filter_it' append_Nil rev.simps(1) by metis

subsection "split_at"

fun split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at n [] = ([], [])"
| "split_at n (x # xs) = (
    case n of
      0 \<Rightarrow> ([], x # xs)
    | Suc m \<Rightarrow>
      let (xs', ys') = split_at m xs in
      (x # xs', ys')
  )"

lemma split_at_take_drop_conv:
  "split_at n xs = (take n xs, drop n xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

declare split_at.simps [simp del]

fun t_split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_split_at n [] = 0"
| "t_split_at n (x#xs) = 1 + (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> t_split_at m xs
  )"

lemma t_split_at:
  "t_split_at n xs \<le> length xs"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition split_at_cost :: "nat \<Rightarrow> real" where
  "split_at_cost n = n"

lemma split_at_cost_nonneg[simp]:
  "0 \<le> split_at_cost n"
  unfolding split_at_cost_def by simp

lemma t_split_at_conv_split_at_cost:
  "t_split_at n xs \<le> split_at_cost (length xs)"
  unfolding split_at_cost_def by (auto simp: min_def t_split_at)

fun split_at_it' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at_it' acc n [] = (rev acc, [])"
| "split_at_it' acc n (x#xs) = (
    case n of
      0 \<Rightarrow> (rev acc, x#xs)
    | Suc m \<Rightarrow> split_at_it' (x#acc) m xs
  )"

definition split_at_it :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at_it n xs = split_at_it' [] n xs"

lemma split_at_conv_split_at_it':
  assumes "(ts, ds) = split_at n xs" "(tsi, dsi) = split_at_it' acc n xs"
  shows "rev acc @ ts = tsi"
    and "ds = dsi"
  using assms
  apply (induction acc n xs arbitrary: ts rule: split_at_it'.induct)
  apply (auto simp: split_at.simps split: prod.splits nat.splits)
  done

lemma split_at_conv_split_at_it_prod:
  assumes "(ts, ds) = split_at n xs" "(ts', ds') = split_at_it n xs"
  shows "(ts, ds) = (ts', ds')"
  using assms unfolding split_at_it_def 
  using split_at_conv_split_at_it' rev.simps(1) append_Nil by fast+

lemma split_at_conv_split_at_it[code_unfold]:
  "split_at n xs = split_at_it n xs"
  using split_at_conv_split_at_it_prod surj_pair by metis


section "Mergesort"

subsection "Functional Correctness Proof"

definition sortedX :: "point list \<Rightarrow> bool" where
  "sortedX ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1) ps"

definition sortedY :: "point list \<Rightarrow> bool" where
  "sortedY ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1) ps"

fun merge :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge f (x # xs) (y # ys) = (
    if f x \<le> f y then
      x # merge f xs (y # ys)
    else
      y # merge f (x # xs) ys
  )"
| "merge f [] ys = ys"
| "merge f xs [] = xs"

lemma length_merge:
  "length (merge f xs ys) = length xs + length ys"
  by (induction f xs ys rule: merge.induct) auto

lemma set_merge:
  "set (merge f xs ys) = set xs \<union> set ys"
  by (induction f xs ys rule: merge.induct) auto

lemma distinct_merge:
  assumes "set xs \<inter> set ys = {}" "distinct xs" "distinct ys"
  shows "distinct (merge f xs ys)"
  using assms by (induction f xs ys rule: merge.induct) (auto simp: set_merge)

lemma sorted_merge:
  assumes "P = (\<lambda>x y. f x \<le> f y)"
  shows "sorted_wrt P (merge f xs ys) \<longleftrightarrow> sorted_wrt P xs \<and> sorted_wrt P ys"
  using assms by (induction f xs ys rule: merge.induct) (auto simp: set_merge)

function msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "msort f [] = []"
| "msort f [x] = [x]"
| "msort f (x # y # xs') = ( 
    let xs = x # y # xs' in
    let n = length xs div 2 in
    let (l, r) = split_at n xs in
    merge f (msort f l) (msort f r)
  )"
  by pat_completeness auto
termination msort
  apply (relation "Wellfounded.measure (\<lambda>(_, xs). length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

lemma sorted_wrt_msort:
  "sorted_wrt (\<lambda>x y. f x \<le> f y) (msort f xs)"
  by (induction f xs rule: msort.induct) (auto simp: split_at_take_drop_conv sorted_merge)

lemma set_msort:
  "set (msort f xs) = set xs"
  apply (induction f xs rule: msort.induct)
  apply (simp_all add: set_merge split_at_take_drop_conv)
  using set_take_drop by (metis list.simps(15))

lemma length_msort:
  "length (msort f xs) = length xs"
  by (induction f xs rule: msort.induct) (auto simp: length_merge split_at_take_drop_conv)

lemma distinct_msort:
  "distinct xs \<Longrightarrow> distinct (msort f xs)"
proof (induction f xs rule: msort.induct)
  case (3 f x y xs)
  let ?xs' = "x # y # xs"
  obtain l r where lr_def: "(l, r) = split_at (length ?xs' div 2) ?xs'"
    by (metis surj_pair)
  have "distinct l" "distinct r"
    using "3.prems" split_at_take_drop_conv distinct_take distinct_drop lr_def by (metis prod.sel)+
  hence "distinct (msort f l)" "distinct (msort f r)"
    using "3.IH" lr_def by auto
  moreover have "set l \<inter> set r = {}"
    using "3.prems" split_at_take_drop_conv lr_def by (metis append_take_drop_id distinct_append prod.sel)
  ultimately show ?case
    using lr_def by (auto simp: distinct_merge set_msort split: prod.splits)
qed auto

definition sortX :: "point list \<Rightarrow> point list" where
  "sortX ps = msort fst ps"

definition sortY :: "point list \<Rightarrow> point list" where
  "sortY ps = msort snd ps"

lemma sortX:
  shows sortedX_sortX: "sortedX (sortX ps)" and
        set_sortX: "set (sortX ps) = set ps" and
        length_sortX: "length (sortX ps) = length ps" and
        distinct_sortX: "distinct ps \<Longrightarrow> distinct (sortX ps)"
  unfolding sortX_def sortedX_def
  by (auto simp: sorted_wrt_msort set_msort length_msort distinct_msort)

lemma sortY:
  shows sortedY_sortY: "sortedY (sortY ps)" and
        set_sortY: "set (sortY ps) = set ps" and
        length_sortY: "length (sortY ps) = length ps" and
        distinct_sortY: "distinct ps \<Longrightarrow> distinct (sortY ps)"
  unfolding sortY_def sortedY_def
  by (auto simp: sorted_wrt_msort set_msort length_msort distinct_msort)

lemma sortedX_take_less_hd_drop:
  assumes "sortedX ps" "n < length ps"
  shows "\<forall>p \<in> set (take n ps). fst p \<le> fst (hd (drop n ps))"
  using assms sorted_wrt_take_less_hd_drop[of "\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1"] sortedX_def by fastforce

lemma sortedX_hd_drop_less_drop:
  assumes "sortedX ps"
  shows "\<forall>p \<in> set (drop n ps). fst (hd (drop n ps)) \<le> fst p"
  using assms sorted_wrt_hd_drop_less_drop[of "\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1"] sortedX_def by fastforce

subsection "Time Complexity Proof"

fun t_merge' :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_merge' f (x#xs) (y#ys) = 1 + (
    if f x \<le> f y then
      t_merge' f xs (y#ys)
    else
      t_merge' f (x#xs) ys
  )"
| "t_merge' f xs [] = 0"
| "t_merge' f [] ys = 0"

definition t_merge :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> ('b list * 'b list) \<Rightarrow> nat" where
  "t_merge f xys = t_merge' f (fst xys) (snd xys)"

lemma t_merge:
  "t_merge f (xs, ys) \<le> length xs + length ys"
  unfolding t_merge_def by (induction f xs ys rule: t_merge'.induct) auto

definition merge_cost :: "nat \<Rightarrow> real" where
  "merge_cost n = n"

lemma merge_cost_nonneg[simp]:
  "0 \<le> merge_cost n"
  unfolding merge_cost_def by simp

lemma t_merge_conv_merge_cost:
  "t_merge f (xs, ys) \<le> merge_cost (length xs + length ys)"
  unfolding merge_cost_def by (metis of_nat_mono t_merge)

function t_msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_msort f [] = 0"
| "t_msort f [_] = 1"
| "t_msort f (x # y # xs') = 1 + (
    let xs = x # y # xs' in
    let (l, r) = split_at (length xs div 2) xs in
    t_length xs + t_split_at (length xs div 2) xs +
    t_msort f l + t_msort f r + t_merge f (l, r)
  )"
  by pat_completeness auto
termination t_msort
  apply (relation "Wellfounded.measure (\<lambda>(_, xs). length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

definition t_sortX :: "point list \<Rightarrow> nat" where
  "t_sortX ps = t_msort (\<lambda>p. fst p) ps"

definition t_sortY :: "point list \<Rightarrow> nat" where
  "t_sortY ps = t_msort (\<lambda>p. snd p) ps"

function msort_cost :: "nat \<Rightarrow> real" where
  "msort_cost 0 = 0"
| "msort_cost 1 = 1"
| "2 \<le> n \<Longrightarrow> msort_cost n = 1 + length_cost n + split_at_cost n + 
    msort_cost (nat \<lfloor>real n / 2\<rfloor>) + msort_cost (nat \<lceil>real n / 2\<rceil>) + merge_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

definition sortX_cost :: "nat \<Rightarrow> real" where
  "sortX_cost = msort_cost"

definition sortY_cost :: "nat \<Rightarrow> real" where
  "sortY_cost = msort_cost"

declare t_length.simps t_split_at.simps[simp del]

lemma msort_cost_nonneg[simp]:
  "0 \<le> msort_cost n"
  by (induction n rule: msort_cost.induct) (auto simp del: One_nat_def)

corollary sortX_cost_nonneg[simp]:
  "0 \<le> sortX_cost n"
  unfolding sortX_cost_def by simp

corollary sortY_cost_nonneg[simp]:
  "0 \<le> sortY_cost n"
  unfolding sortY_cost_def by simp

lemma t_msort_conv_msort_cost:
  "t_msort f xs \<le> msort_cost (length xs)"
proof (induction f xs rule: t_msort.induct)
  case (2 f x)
  thus ?case
    using msort_cost.simps(2) by auto
next
  case (3 f x y xs')

  define XS where "XS = x # y # xs'"
  define N where "N = length XS"
  obtain L R where LR_def: "(L, R) = split_at (N div 2) XS"
    using prod.collapse by blast
  note defs = XS_def N_def LR_def

  let ?LHS = "1 + t_length XS + t_split_at (N div 2) XS + t_msort f L + t_msort f R + t_merge f (L, R)"
  let ?RHS = "1 + length_cost N + split_at_cost N + msort_cost (nat \<lfloor>real N / 2\<rfloor>) +
              msort_cost (nat \<lceil>real N / 2\<rceil>) + merge_cost N"

  have IHL: "t_msort f L \<le> msort_cost (length L)"
    using defs "3.IH"(1) prod.collapse by blast
  have IHR: "t_msort f R \<le> msort_cost (length R)"
    using defs "3.IH"(2) prod.collapse by blast

  have *: "length L = N div 2" "length R = N - N div 2"
    using defs by (auto simp: split_at_take_drop_conv)
  hence "(nat \<lfloor>real N / 2\<rfloor>) = length L" "(nat \<lceil>real N / 2\<rceil>) = length R"
    by linarith+
  hence IH: "t_msort f L \<le> msort_cost (nat \<lfloor>real N / 2\<rfloor>)"
            "t_msort f R \<le> msort_cost (nat \<lceil>real N / 2\<rceil>)"
    using IHL IHR by simp_all

  have "N = length L + length R"
    using * by linarith
  hence "t_merge f (L, R) \<le> merge_cost N"
    using t_merge_conv_merge_cost by metis
  moreover have "t_length XS = length_cost N"
    using t_length_conv_length_cost defs by blast
  moreover have "t_split_at (N div 2) XS \<le> split_at_cost N"
    using t_split_at_conv_split_at_cost defs by blast
  ultimately have *: "?LHS \<le> ?RHS"
    using IH by simp
  moreover have "t_msort f XS = ?LHS"
    using defs by (auto simp: Let_def split: prod.split)
  moreover have "msort_cost N = ?RHS"
    by (simp add: defs)
  ultimately have "t_msort f XS \<le> msort_cost N"
    by presburger 
  thus ?case
    using XS_def N_def by blast
qed auto

corollary t_sortX_conv_sortX_cost:
  "t_sortX xs \<le> sortX_cost (length xs)"
  unfolding t_sortX_def sortX_cost_def using t_msort_conv_msort_cost by blast

corollary t_sortY_conv_sortY_cost:
  "t_sortY xs \<le> sortY_cost (length xs)"
  unfolding t_sortY_def sortY_cost_def using t_msort_conv_msort_cost by blast

theorem msort_cost:
  "msort_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  by (master_theorem) (auto simp: length_cost_def split_at_cost_def merge_cost_def)

corollary sortX_cost:
  "sortX_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding sortX_cost_def using msort_cost by simp

corollary sortY_cost:
  "sortY_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding sortY_cost_def using msort_cost by simp

theorem t_msort_bigo:
  "t_msort f \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
proof -
  have 0: "\<And>xs. t_msort f xs \<le> (msort_cost o length) xs"
    unfolding comp_def using t_msort_conv_msort_cost by blast
  show ?thesis
    using bigo_measure_trans[OF 0] by (simp add: bigthetaD1 msort_cost)
qed

corollary t_sortX_bigo:
  "t_sortX \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  unfolding t_sortX_def sortX_cost_def using t_msort_bigo by blast

corollary t_sortY_bigo:
  "t_sortY \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  unfolding t_sortY_def sortY_cost_def using t_msort_bigo by blast

subsection "Code Export"

lemma merge_xs_Nil[simp]:
  "merge f xs [] = xs"
  by (cases xs) auto

fun merge_it' :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge_it' f acc [] [] = rev acc"
| "merge_it' f acc (x#xs) [] = merge_it' f (x#acc) xs []"
| "merge_it' f acc [] (y#ys) = merge_it' f (y#acc) ys []"
| "merge_it' f acc (x#xs) (y#ys) = (
    if f x \<le> f y then
      merge_it' f (x#acc) xs (y#ys)
    else
      merge_it' f (y#acc) (x#xs) ys
  )"

definition merge_it :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge_it f xs ys = merge_it' f [] xs ys"

lemma merge_conv_merge_it':
  "rev acc @ merge f xs ys = merge_it' f acc xs ys"
  by (induction f acc xs ys rule: merge_it'.induct) auto

lemma merge_conv_merge_it[code_unfold]:
  "merge f xs ys = merge_it f xs ys"
  unfolding merge_it_def using merge_conv_merge_it' rev.simps(1) append_Nil by metis


section "Minimal Distance"

definition min_dist :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "min_dist \<delta> ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1)"

lemma min_dist_identity:
  assumes "min_dist \<delta> (set ps)" "\<forall>p \<in> set ps. \<delta> \<le> dist p\<^sub>0 p"
  shows "min_dist \<delta> (set (p\<^sub>0 # ps))"
  using assms by (simp add: dist_commute min_dist_def)

lemma min_dist_update:
  assumes "min_dist \<delta> (set ps)"
  assumes "dist p\<^sub>0 p\<^sub>1 \<le> \<delta>" "\<forall>p \<in> set ps. dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "min_dist (dist p\<^sub>0 p\<^sub>1) (set (p\<^sub>0 # ps))"
  using assms apply (auto simp: dist_commute min_dist_def) by force+

lemma min_dist_mono:
  "min_dist \<Delta> P \<Longrightarrow> \<delta> \<le> \<Delta> \<Longrightarrow> min_dist \<delta> P"
  unfolding min_dist_def by fastforce


section "Distance"

lemma dist_transform:
  fixes p :: point and \<delta> :: real and l :: int
  shows "dist p (l, snd p) < \<delta> \<longleftrightarrow> l - \<delta> < fst p \<and> fst p < l + \<delta>"
proof -
  have "dist p (l, snd p) = sqrt ((real_of_int (fst p) - l)\<^sup>2)"
    by (auto simp add: dist_prod_def dist_real_def prod.case_eq_if)
  thus ?thesis
    by auto
qed

fun dist_code :: "point \<Rightarrow> point \<Rightarrow> int" where
  "dist_code p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

lemma dist_eq_sqrt_dist_code:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 = sqrt (dist_code p\<^sub>0 p\<^sub>1)"
  by (auto simp: dist_prod_def dist_real_def split: prod.splits) 

lemma dist_eq_dist_code_lt:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 < dist p\<^sub>2 p\<^sub>3 \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 < dist_code p\<^sub>2 p\<^sub>3"
  using dist_eq_sqrt_dist_code real_sqrt_less_iff by presburger

lemma dist_eq_dist_code_le:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>2 p\<^sub>3 \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 \<le> dist_code p\<^sub>2 p\<^sub>3"
  using dist_eq_sqrt_dist_code real_sqrt_le_iff by presburger

lemma dist_eq_dist_code_abs_lt:
  fixes p\<^sub>0 :: point
  shows "\<bar>c\<bar> < dist p\<^sub>0 p\<^sub>1 \<longleftrightarrow> c\<^sup>2 < dist_code p\<^sub>0 p\<^sub>1"
  using dist_eq_sqrt_dist_code
  by (metis of_int_less_of_int_power_cancel_iff real_sqrt_abs real_sqrt_less_iff)

lemma dist_eq_dist_code_abs_le:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 \<le> \<bar>c\<bar> \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 \<le> c\<^sup>2"
  using dist_eq_sqrt_dist_code
  by (metis of_int_power_le_of_int_cancel_iff real_sqrt_abs real_sqrt_le_iff)

lemma dist_fst_abs:
  fixes p :: point and l :: int
  shows "dist p (l, snd p) = \<bar>fst p - l\<bar>"
proof -
  have "dist p (l, snd p) = sqrt ((real_of_int (fst p) - l)\<^sup>2)"
    by (simp add: dist_prod_def dist_real_def prod.case_eq_if)
  thus ?thesis
    by simp
qed

declare dist_code.simps [simp del]


section "Brute Force Closest Pair Algorithm"

subsection "Functional Correctness Proof"

fun find_closest_bf :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_bf _ [] = undefined"
| "find_closest_bf _ [p] = p"
| "find_closest_bf p (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest_bf p ps in
    if dist p p\<^sub>0 < dist p p\<^sub>1 then
      p\<^sub>0
    else
      p\<^sub>1
  )"

lemma find_closest_bf_set:
  "0 < length ps \<Longrightarrow> find_closest_bf p ps \<in> set ps"
  by (induction p ps rule: find_closest_bf.induct)
     (auto simp: Let_def split: prod.splits if_splits)

lemma find_closest_bf_dist:
  "\<forall>q \<in> set ps. dist p (find_closest_bf p ps) \<le> dist p q"
  by (induction p ps rule: find_closest_bf.induct)
     (auto split: prod.splits)

fun closest_pair_bf :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_bf [] = undefined"
| "closest_pair_bf [_] = undefined"
| "closest_pair_bf [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_bf (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps in
    let p\<^sub>1 = find_closest_bf p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

lemma closest_pair_bf_c0:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
  by (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
     (auto simp: Let_def find_closest_bf_set split: if_splits prod.splits)

lemma closest_pair_bf_c1:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>1 \<in> set ps" 
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  obtain c\<^sub>0 c\<^sub>1 where c\<^sub>0_def: "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ?ps"
    using prod.collapse by blast
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest_bf p\<^sub>0 ?ps"
  note defs = c\<^sub>0_def p\<^sub>1_def
  have "c\<^sub>1 \<in> set ?ps"
    using "4.IH" defs by simp
  moreover have "p\<^sub>1 \<in> set ?ps"
    using find_closest_bf_set defs by blast
  ultimately show ?case
    using "4.prems"(2) defs by (auto simp: Let_def split: prod.splits if_splits)
qed auto

lemma closest_pair_bf_c0_ne_c1:
  "1 < length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  obtain c\<^sub>0 c\<^sub>1 where c\<^sub>0_def: "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ?ps"
    using prod.collapse by blast
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest_bf p\<^sub>0 ?ps"
  note defs = c\<^sub>0_def p\<^sub>1_def
  have "c\<^sub>0 \<noteq> c\<^sub>1"
    using "4.IH" "4.prems"(2) defs by simp
  moreover have "p\<^sub>0 \<noteq> p\<^sub>1"
    using find_closest_bf_set "4.prems"(2) defs
    by (metis distinct.simps(2) length_pos_if_in_set list.set_intros(1))
  ultimately show ?case
    using "4.prems"(3) defs by (auto simp: Let_def split: prod.splits if_splits)
qed auto

lemmas closest_pair_bf_c0_c1 = closest_pair_bf_c0 closest_pair_bf_c1 closest_pair_bf_c0_ne_c1

lemma closest_pair_bf_dist:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ps"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  obtain c\<^sub>0 c\<^sub>1 where c\<^sub>0_def: "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ?ps"
    using prod.collapse by blast
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest_bf p\<^sub>0 ?ps"
  note defs = c\<^sub>0_def p\<^sub>1_def
  hence IH: "min_dist (dist c\<^sub>0 c\<^sub>1) (set ?ps)"
    using 4 c\<^sub>0_def by simp
  have *: "\<forall>p \<in> set ?ps. (dist p\<^sub>0 p\<^sub>1) \<le> dist p\<^sub>0 p"
    using find_closest_bf_dist defs by blast
  show ?case
  proof (cases "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    hence "\<forall>p \<in> set ?ps. dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p"
      using * by auto
    hence "min_dist (dist c\<^sub>0 c\<^sub>1) (set (p\<^sub>0 # ?ps))"
      using min_dist_identity IH by blast
    thus ?thesis
      using True "4.prems" defs by (auto split: prod.splits)
  next
    case False
    hence "min_dist (dist p\<^sub>0 p\<^sub>1) (set (p\<^sub>0 # ?ps))"
      using min_dist_update[of "dist c\<^sub>0 c\<^sub>1" ?ps p\<^sub>0 p\<^sub>1] IH * defs by argo
    thus ?thesis
      using False "4.prems" defs by (auto split: prod.splits)
  qed
qed (auto simp: dist_commute min_dist_def)

subsection "Time Complexity Proof"

fun t_find_closest_bf :: "point \<Rightarrow> point list \<Rightarrow> nat" where
  "t_find_closest_bf _ [] = 0"
| "t_find_closest_bf _ [_] = 1"
| "t_find_closest_bf p (p\<^sub>0 # ps) = 1 + (
    let p\<^sub>1 = find_closest_bf p ps in
    t_find_closest_bf p ps + (
    if dist p p\<^sub>0 < dist p p\<^sub>1 then 0 else 0
    )
  )"

lemma t_find_closest_bf:
  "t_find_closest_bf p ps = length ps"
  by (induction p ps rule: t_find_closest_bf.induct) auto

fun t_closest_pair_bf :: "point list \<Rightarrow> nat" where
  "t_closest_pair_bf [] = 0"
| "t_closest_pair_bf [_] = 1"
| "t_closest_pair_bf [_, _] = 2"
| "t_closest_pair_bf (p\<^sub>0 # ps) = 1 + (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps in
    t_closest_pair_bf ps + (
    let p\<^sub>1 = find_closest_bf p\<^sub>0 ps in
    t_find_closest_bf p\<^sub>0 ps + (
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then 0 else 0
    ))
  )"

lemma t_closest_pair_bf:
  "t_closest_pair_bf ps \<le> length ps * length ps"
proof (induction rule: t_closest_pair_bf.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  have "t_closest_pair_bf ?ps \<le> length ?ps * length ?ps"
    using 4 prod_cases3 by metis
  thus ?case
    using "4.prems" t_find_closest_bf by simp
qed auto

definition closest_pair_bf_cost :: "nat \<Rightarrow> real" where
  "closest_pair_bf_cost n = n * n"

lemma closest_pair_bf_cost_nonneg[simp]:
  "0 \<le> closest_pair_bf_cost n"
  unfolding closest_pair_bf_cost_def by simp

lemma t_closest_pair_bf_conv_closest_pair_bf_cost:
  "t_closest_pair_bf ps \<le> closest_pair_bf_cost (length ps)"
  unfolding closest_pair_bf_cost_def using t_closest_pair_bf of_nat_mono by fastforce

subsection "Code Export"

fun find_closest_bf_code :: "point \<Rightarrow> point list \<Rightarrow> (int * point)" where
  "find_closest_bf_code p [] = undefined"
| "find_closest_bf_code p [p\<^sub>0] = (dist_code p p\<^sub>0, p\<^sub>0)"
| "find_closest_bf_code p (p\<^sub>0 # ps) = (
    let (\<delta>\<^sub>1, p\<^sub>1) = find_closest_bf_code p ps in
    let \<delta>\<^sub>0 = dist_code p p\<^sub>0 in
    if \<delta>\<^sub>0 < \<delta>\<^sub>1 then
      (\<delta>\<^sub>0, p\<^sub>0)
    else
      (\<delta>\<^sub>1, p\<^sub>1)
  )"

lemma find_closest_bf_code_dist_eq:
  "0 < length ps \<Longrightarrow> (\<delta>, c) = find_closest_bf_code p ps \<Longrightarrow> \<delta> = dist_code p c"
  by (induction p ps rule: find_closest_bf_code.induct)
     (auto simp: Let_def split: prod.splits if_splits)

lemma find_closest_bf_code_eq:
  "0 < length ps \<Longrightarrow> c = find_closest_bf p ps \<Longrightarrow> (\<delta>', c') = find_closest_bf_code p ps \<Longrightarrow> c = c'"
proof (induction p ps arbitrary: c \<delta>' c' rule: find_closest_bf.induct)
  case (3 p p\<^sub>0 p\<^sub>2 ps)
  define \<delta>\<^sub>0 \<delta>\<^sub>0' where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist p p\<^sub>0" "\<delta>\<^sub>0' = dist_code p p\<^sub>0"
  obtain \<delta>\<^sub>1 p\<^sub>1 \<delta>\<^sub>1' p\<^sub>1' where \<delta>\<^sub>1_def: "\<delta>\<^sub>1 = dist p p\<^sub>1" "p\<^sub>1 = find_closest_bf p (p\<^sub>2 # ps)"
    "(\<delta>\<^sub>1', p\<^sub>1') = find_closest_bf_code p (p\<^sub>2 # ps)"
    using prod.collapse by blast+
  note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
  have *: "p\<^sub>1 = p\<^sub>1'"
    using "3.IH" defs by simp
  hence "\<delta>\<^sub>0 < \<delta>\<^sub>1 \<longleftrightarrow> \<delta>\<^sub>0' < \<delta>\<^sub>1'"
    using find_closest_bf_code_dist_eq[of "p\<^sub>2 # ps" \<delta>\<^sub>1' p\<^sub>1' p]
          dist_eq_dist_code_lt defs
    by simp
  thus ?case
    using "3.prems"(2,3) * defs by (auto split: prod.splits)
qed auto

declare find_closest_bf_code.simps [simp del]

fun closest_pair_bf_code :: "point list \<Rightarrow> (int * point * point)" where
  "closest_pair_bf_code [] = undefined"
| "closest_pair_bf_code [p\<^sub>0] = undefined"
| "closest_pair_bf_code [p\<^sub>0, p\<^sub>1] = (dist_code p\<^sub>0 p\<^sub>1, p\<^sub>0, p\<^sub>1)"
| "closest_pair_bf_code (p\<^sub>0 # ps) = (
    let (\<delta>\<^sub>c, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code ps in
    let (\<delta>\<^sub>p, p\<^sub>1) = find_closest_bf_code p\<^sub>0 ps in
    if \<delta>\<^sub>c \<le> \<delta>\<^sub>p then
      (\<delta>\<^sub>c, c\<^sub>0, c\<^sub>1)
    else
      (\<delta>\<^sub>p, p\<^sub>0, p\<^sub>1) 
  )"

lemma closest_pair_bf_code_dist_eq:
  "1 < length ps \<Longrightarrow> (\<delta>, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code ps \<Longrightarrow> \<delta> = dist_code c\<^sub>0 c\<^sub>1"
proof (induction ps arbitrary: \<delta> c\<^sub>0 c\<^sub>1 rule: closest_pair_bf_code.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  obtain \<delta>\<^sub>c c\<^sub>0 c\<^sub>1 where \<delta>\<^sub>c_def: "(\<delta>\<^sub>c, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code ?ps"
    by (metis prod_cases3)
  obtain \<delta>\<^sub>p p\<^sub>1 where \<delta>\<^sub>p_def: "(\<delta>\<^sub>p, p\<^sub>1) = find_closest_bf_code p\<^sub>0 ?ps"
    using prod.collapse by blast
  note defs = \<delta>\<^sub>c_def \<delta>\<^sub>p_def
  have "\<delta>\<^sub>c = dist_code c\<^sub>0 c\<^sub>1"
    using "4.IH" defs by simp
  moreover have "\<delta>\<^sub>p = dist_code p\<^sub>0 p\<^sub>1"
    using find_closest_bf_code_dist_eq defs by blast
  ultimately show ?case
    using "4.prems"(2) defs by (auto split: prod.splits if_splits)
qed auto

lemma closest_pair_bf_code_eq:
  assumes "1 < length ps" 
  assumes "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ps" "(\<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_bf_code ps"
  shows "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
  using assms
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 \<delta>' c\<^sub>0' c\<^sub>1' rule: closest_pair_bf_code.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  obtain c\<^sub>0 c\<^sub>1 \<delta>\<^sub>c' c\<^sub>0' c\<^sub>1' where \<delta>\<^sub>c_def: "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ?ps"
    "(\<delta>\<^sub>c', c\<^sub>0', c\<^sub>1') = closest_pair_bf_code ?ps"
    by (metis prod_cases3)
  obtain p\<^sub>1 \<delta>\<^sub>p' p\<^sub>1' where \<delta>\<^sub>p_def: "p\<^sub>1 = find_closest_bf p\<^sub>0 ?ps"
    "(\<delta>\<^sub>p', p\<^sub>1') = find_closest_bf_code p\<^sub>0 ?ps"
    using prod.collapse by blast
  note defs = \<delta>\<^sub>c_def \<delta>\<^sub>p_def
  have A: "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
    using "4.IH" defs by simp
  moreover have B: "p\<^sub>1 = p\<^sub>1'"
    using find_closest_bf_code_eq defs by blast
  moreover have "\<delta>\<^sub>c' = dist_code c\<^sub>0' c\<^sub>1'"
    using defs closest_pair_bf_code_dist_eq[of ?ps] by simp
  moreover have "\<delta>\<^sub>p' = dist_code p\<^sub>0 p\<^sub>1'"
    using defs find_closest_bf_code_dist_eq by blast
  ultimately have "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 \<longleftrightarrow> \<delta>\<^sub>c' \<le> \<delta>\<^sub>p'"
    by (simp add: dist_eq_dist_code_le)
  thus ?case
    using "4.prems"(2,3) defs A B by (auto simp: Let_def split: prod.splits)
qed auto


section "Geometry"

subsection "Band Filter"

lemma set_band_filter_aux:
  fixes \<delta> :: real and ps :: "point list"
  assumes "p\<^sub>0 \<in> ps\<^sub>L" "p\<^sub>1 \<in> ps\<^sub>R" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "ps' = filter (\<lambda>p. l - \<delta> < fst p \<and> fst p < l + \<delta>) ps"
  shows "p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps'"
proof (rule ccontr)
  assume "\<not> (p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps')"
  then consider (A) "p\<^sub>0 \<notin> set ps' \<and> p\<^sub>1 \<notin> set ps'"
              | (B) "p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<notin> set ps'"
              | (C) "p\<^sub>0 \<notin> set ps' \<and> p\<^sub>1 \<in> set ps'"
    by blast
  thus False
  proof cases
    case A
    hence "fst p\<^sub>0 \<le> l - \<delta> \<or> l + \<delta> \<le> fst p\<^sub>0" "fst p\<^sub>1 \<le> l - \<delta> \<or> l + \<delta> \<le> fst p\<^sub>1"
      using assms(1,2,5,8) by auto
    hence "fst p\<^sub>0 \<le> l - \<delta>" "l + \<delta> \<le> fst p\<^sub>1"
      using assms(1,2,6,7) by force+
    hence "\<delta> \<le> dist (fst p\<^sub>0) (fst p\<^sub>1)"
      using dist_real_def by simp
    hence "\<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using dist_fst_le[of p\<^sub>0 p\<^sub>1] by (auto split: prod.splits)
    then show ?thesis
      using assms(4) by fastforce
  next
    case B
    hence "fst p\<^sub>1 \<le> l - \<delta> \<or> l + \<delta> \<le> fst p\<^sub>1"
      using assms(2,5,8) by auto
    hence "l + \<delta> \<le> fst p\<^sub>1"
      using assms(2,7) by auto
    moreover have "fst p\<^sub>0 \<le> l"
      using assms(1,6) by simp
    ultimately have "\<delta> \<le> dist (fst p\<^sub>0) (fst p\<^sub>1)"
      using dist_real_def by simp
    hence "\<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using dist_fst_le[of p\<^sub>0 p\<^sub>1] less_le_trans by (auto split: prod.splits)
    thus ?thesis
      using assms(4) by simp
  next
    case C
    hence "fst p\<^sub>0 \<le> l - \<delta> \<or> l + \<delta> \<le> fst p\<^sub>0"
      using assms(1,2,5,8) by auto
    hence "fst p\<^sub>0 \<le> l - \<delta>"
      using assms(1,6) by auto
    moreover have "l \<le> fst p\<^sub>1"
      using assms(2,7) by simp
    ultimately have "\<delta> \<le> dist (fst p\<^sub>0) (fst p\<^sub>1)"
      using dist_real_def by simp
    hence "\<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using dist_fst_le[of p\<^sub>0 p\<^sub>1] less_le_trans by (auto split: prod.splits)
    thus ?thesis
      using assms(4) by simp
  qed
qed
  
lemma set_band_filter:
  fixes \<delta> :: real and ps :: "point list"
  assumes "p\<^sub>0 \<in> set ps" "p\<^sub>1 \<in> set ps" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "min_dist \<delta> ps\<^sub>L" "min_dist \<delta> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "ps' = filter (\<lambda>p. l - \<delta> < fst p \<and> fst p < l + \<delta>) ps"
  shows "p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps'"
proof -
  have "p\<^sub>0 \<notin> ps\<^sub>L \<or> p\<^sub>1 \<notin> ps\<^sub>L" "p\<^sub>0 \<notin> ps\<^sub>R \<or> p\<^sub>1 \<notin> ps\<^sub>R"
    using assms(3,4,6,7) min_dist_def by force+
  then consider (A) "p\<^sub>0 \<in> ps\<^sub>L \<and> p\<^sub>1 \<in> ps\<^sub>R" | (B) "p\<^sub>0 \<in> ps\<^sub>R \<and> p\<^sub>1 \<in> ps\<^sub>L"
    using assms(1,2,5) by auto
  thus ?thesis
  proof cases
    case A
    thus ?thesis
      using set_band_filter_aux assms(3,4,5,8,9,10) by (auto split: prod.splits)
  next
    case B
    moreover have "dist p\<^sub>1 p\<^sub>0 < \<delta>"
      using assms(4) dist_commute by metis
    ultimately show ?thesis
      using set_band_filter_aux assms(3)[symmetric] assms(5,8,9,10) by (auto split: prod.splits)
  qed
qed

subsection "2D-Boxes and Points"

lemma cbox_2D: 
  fixes x\<^sub>0 :: real and y\<^sub>0 :: real
  shows "cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) = { (x, y). x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1 }"
  by fastforce

lemma mem_cbox_2D:
  fixes x :: real and y :: real
  shows "x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1 \<longleftrightarrow> (x, y) \<in> cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1)"
  by fastforce

lemma cbox_top_un:
  fixes x\<^sub>0 :: real and y\<^sub>0 :: real
  assumes "y\<^sub>0 \<le> y\<^sub>1" "y\<^sub>1 \<le> y\<^sub>2"
  shows "cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>0, y\<^sub>1) (x\<^sub>1, y\<^sub>2) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>2)"
  using assms by auto

lemma cbox_right_un:
  fixes x\<^sub>0 :: real and y\<^sub>0 :: real
  assumes "x\<^sub>0 \<le> x\<^sub>1" "x\<^sub>1 \<le> x\<^sub>2"
  shows "cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>1, y\<^sub>0) (x\<^sub>2, y\<^sub>1) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>2, y\<^sub>1)"
  using assms by auto

lemma cbox_max_dist:
  assumes "p\<^sub>0 = (x, y)" "p\<^sub>1 = (x + \<delta>, y + \<delta>)"
  assumes "(x\<^sub>0, y\<^sub>0) \<in> cbox p\<^sub>0 p\<^sub>1" "(x\<^sub>1, y\<^sub>1) \<in> cbox p\<^sub>0 p\<^sub>1" "0 \<le> \<delta>"
  shows "dist (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<le> sqrt 2 * \<delta>"
proof -
  have X: "dist x\<^sub>0 x\<^sub>1 \<le> \<delta>"
    using assms dist_real_def by auto
  have Y: "dist y\<^sub>0 y\<^sub>1 \<le> \<delta>"
    using assms dist_real_def by auto

  have "dist (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) = sqrt ((dist x\<^sub>0 x\<^sub>1)\<^sup>2 + (dist y\<^sub>0 y\<^sub>1)\<^sup>2)"
    using dist_Pair_Pair by auto
  also have "... \<le> sqrt (\<delta>\<^sup>2 + (dist y\<^sub>0 y\<^sub>1)\<^sup>2)"
    using X power_mono by fastforce
  also have "... \<le> sqrt (\<delta>\<^sup>2 + \<delta>\<^sup>2)"
    using Y power_mono by fastforce
  also have "... = sqrt 2 * sqrt (\<delta>\<^sup>2)"
    using real_sqrt_mult by simp
  also have "... = sqrt 2 * \<delta>"
    using assms(5) by simp
  finally show ?thesis .
qed

subsection "Pigeonhole Argument"

lemma card_le_1_if_pairwise_eq:
  assumes "\<forall>x \<in> S. \<forall>y \<in> S. x = y"
  shows "card S \<le> 1"
proof (rule ccontr)
  assume "\<not> card S \<le> 1"
  hence "2 \<le> card S"
    by simp
  then obtain T where *: "T \<subseteq> S \<and> card T = 2"
    using ex_card by metis
  then obtain x y where "x \<in> T \<and> y \<in> T \<and> x \<noteq> y"
    using card_2_exists by metis
  then show False
    using * assms by blast
qed

lemma card_Int_if_either_in:
  assumes "\<forall>x \<in> S. \<forall>y \<in> S. x = y \<or> x \<notin> T \<or> y \<notin> T" 
  shows "card (S \<inter> T) \<le> 1"
proof (rule ccontr)
  assume "\<not> (card (S \<inter> T) \<le> 1)"
  then obtain x y where *: "x \<in> S \<inter> T \<and> y \<in> S \<inter> T \<and> x \<noteq> y"
    by (meson card_le_1_if_pairwise_eq)
  hence "x \<in> T" "y \<in> T"
    by simp_all
  moreover have "x \<notin> T \<or> y \<notin> T"
    using assms * by auto
  ultimately show False
    by blast
qed

lemma card_Int_Un_le_Sum_card_Int:
  assumes "finite S"
  shows "card (A \<inter> \<Union>S) \<le> (\<Sum>B \<in> S. card (A \<inter> B))"
  using assms
proof (induction "card S" arbitrary: S)
  case (Suc n)
  then obtain B T where *: "S = { B } \<union> T" "card T = n" "B \<notin> T"
    by (metis card_Suc_eq Suc_eq_plus1 insert_is_Un)
  hence "card (A \<inter> \<Union>S) = card (A \<inter> \<Union>({ B } \<union> T))"
    by blast
  also have "... \<le> card (A \<inter> B) + card (A \<inter> \<Union>T)"
    by (simp add: card_Un_le inf_sup_distrib1)
  also have "... \<le> card (A \<inter> B) + (\<Sum>B \<in> T. card (A \<inter> B))"
    using Suc * by simp
  also have "... \<le> (\<Sum>B \<in> S. card (A \<inter> B))"
    using Suc.prems * by simp
  finally show ?case .
qed simp

lemma pigeonhole:
  assumes "finite T" "S \<subseteq> \<Union>T" "card T < card S"
  shows "\<exists>x \<in> S. \<exists>y \<in> S. \<exists>X \<in> T. x \<noteq> y \<and> x \<in> X \<and> y \<in> X"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> S. \<exists>y \<in> S. \<exists>X \<in> T. x \<noteq> y \<and> x \<in> X \<and> y \<in> X)"
  hence *: "\<forall>X \<in> T. card (S \<inter> X) \<le> 1"
    using card_Int_if_either_in by metis
  have "card T < card (S \<inter> \<Union>T)"
    using Int_absorb2 assms by fastforce
  also have "... \<le> (\<Sum>X \<in> T. card (S \<inter> X))"
    using assms(1) card_Int_Un_le_Sum_card_Int by blast
  also have "... \<le> card T"
    using * sum_mono by fastforce
  finally show False by simp
qed

subsection "\<delta> Sparse Points within a Square"

lemma max_points_square:
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + \<delta>, y + \<delta>)" "min_dist \<delta> ps" "0 \<le> \<delta>"
  shows "card ps \<le> 4"
proof (cases "\<delta> = 0")
  case True
  hence "{ (x, y) } = cbox (x, y) (x + \<delta>, y + \<delta>)"
    using cbox_def by simp
  hence "\<forall>p \<in> ps. p = (x, y)"
    using assms(1) by blast
  hence "\<forall>p \<in> ps. \<forall>q \<in> ps. p = q"
    apply (auto split: prod.splits) by (metis of_int_eq_iff)+
  thus ?thesis
    using card_le_1_if_pairwise_eq by force
next
  case False
  hence \<delta>: "0 < \<delta>"
    using assms(3) by simp
  show ?thesis
  proof (rule ccontr)
    assume A: "\<not> (card ps \<le> 4)"
    define PS where PS_def: "PS = (\<lambda>(x, y). (real_of_int x, real_of_int y)) ` ps"
    have "inj_on (\<lambda>(x, y). (real_of_int x, real_of_int y)) ps"
      using inj_on_def by fastforce
    hence *: "\<not> (card PS \<le> 4)"
      using A PS_def by (simp add: card_image)

    let ?x' = "x + \<delta> / 2"
    let ?y' = "y + \<delta> / 2"

    let ?ll = "cbox ( x ,  y ) (?x'   , ?y'   )"
    let ?lu = "cbox ( x , ?y') (?x'   ,  y + \<delta>)"
    let ?rl = "cbox (?x',  y ) ( x + \<delta>, ?y'   )"
    let ?ru = "cbox (?x', ?y') ( x + \<delta>,  y + \<delta>)"

    let ?sq = "{ ?ll, ?lu, ?rl, ?ru }"

    have card_le_4: "card ?sq \<le> 4"
      by (simp add: card_insert_le_m1)

    have "cbox (x, y) (?x', y + \<delta>) = ?ll \<union> ?lu"
      using cbox_top_un assms(3) by auto
    moreover have "cbox (?x', y) (x + \<delta>, y + \<delta>) = ?rl \<union> ?ru"
      using cbox_top_un assms(3) by auto
    moreover have "cbox (x, y) (?x', y + \<delta>) \<union> cbox (?x', y) (x + \<delta>, y + \<delta>) = cbox (x, y) (x + \<delta>, y + \<delta>)"
      using cbox_right_un assms(3) by simp
    ultimately have "?ll \<union> ?lu \<union> ?rl \<union> ?ru = cbox (x, y) (x + \<delta>, y + \<delta>)"
      by blast

    hence "PS \<subseteq> \<Union>(?sq)"
      using assms(1) PS_def by (auto split: prod.splits)
    moreover have "card ?sq < card PS"
      using * card_insert_le_m1 card_le_4 by linarith
    moreover have "finite ?sq"
      by simp
    ultimately have "\<exists>p\<^sub>0 \<in> PS. \<exists>p\<^sub>1 \<in> PS. \<exists>S \<in> ?sq. (p\<^sub>0 \<noteq> p\<^sub>1 \<and> p\<^sub>0 \<in> S \<and> p\<^sub>1 \<in> S)"
      using pigeonhole[of ?sq PS] by blast
    then obtain S p\<^sub>0 p\<^sub>1 where #: "p\<^sub>0 \<in> PS" "p\<^sub>1 \<in> PS" "S \<in> ?sq" "p\<^sub>0 \<noteq> p\<^sub>1" "p\<^sub>0 \<in> S" "p\<^sub>1 \<in> S"
      by blast

    have D: "0 \<le> \<delta> / 2"
      using assms(3) by simp
    have LL: "\<forall>p\<^sub>0 \<in> ?ll. \<forall>p\<^sub>1 \<in> ?ll. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
      using cbox_max_dist[of "(x, y)" x y "(?x', ?y')" "\<delta> / 2"] D by auto
    have LU: "\<forall>p\<^sub>0 \<in> ?lu. \<forall>p\<^sub>1 \<in> ?lu. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
      using cbox_max_dist[of "(x, ?y')" x ?y' "(?x', y + \<delta>)" "\<delta> / 2"] D by auto
    have RL: "\<forall>p\<^sub>0 \<in> ?rl. \<forall>p\<^sub>1 \<in> ?rl. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
      using cbox_max_dist[of "(?x', y)" ?x' y "(x + \<delta>, ?y')" "\<delta> / 2"] D by auto
    have RU: "\<forall>p\<^sub>0 \<in> ?ru. \<forall>p\<^sub>1 \<in> ?ru. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
      using cbox_max_dist[of "(?x', ?y')" ?x' ?y' "(x + \<delta>, y + \<delta>)" "\<delta> / 2"] D by auto

    have "\<forall>p\<^sub>0 \<in> S. \<forall>p\<^sub>1 \<in> S. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
      using # LL LU RL RU by blast
    hence "dist p\<^sub>0 p\<^sub>1 \<le> (sqrt 2 / 2) * \<delta>"
      using # by simp
    moreover have "(sqrt 2 / 2) * \<delta> < \<delta>"
      using sqrt2_less_2 \<delta> by simp
    ultimately have "dist p\<^sub>0 p\<^sub>1 < \<delta>"
      by simp
    moreover have "\<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using assms(2) # min_dist_def PS_def by auto
    ultimately show False
      by simp
  qed
qed

end