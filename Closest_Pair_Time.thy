theory Closest_Pair_Time
imports 
  Closest_Pair
  "Landau_Symbols.Landau_More"
  "HOL-Library.Going_To_Filter"
  "Akra_Bazzi.Akra_Bazzi_Method"
  "Akra_Bazzi.Akra_Bazzi_Approximation"
begin

section "Auxiliary"

text \<open>
  The following lemma expresses a procedure for deriving complexity properties of
  the form @{prop"t \<in> O[c going_to at_top](f o c)"} where
    \<^item> \<open>t\<close> is a (timing) function on same data domain (e.g. lists),
    \<^item> \<open>c\<close> is a cost function on that data domain (e.g. length),
    \<^item> \<open>t'\<close> is a function on @{typ nat}.
  One needs to show that
    \<^item> \<open>t\<close> is bounded by @{term "t' o c"}
    \<^item> @{prop"t' \<in> O(f)"}
  to conclude the overall property @{prop"t \<in> O[c going_to at_top](f o c)"}.
\<close>

lemma bigo_measure_trans:
  fixes t :: "'a \<Rightarrow> real" and t' :: "nat \<Rightarrow> real" and c :: "'a \<Rightarrow> nat" and f ::"nat \<Rightarrow> real"
  assumes "\<And>x. t x \<le> (t' o c) x"
      and "t' \<in> O(f)"
      and "\<And>x. 0 \<le> t x"
  shows "t \<in> O[c going_to at_top](f o c)"
proof -
  have 0: "\<forall>x. 0 \<le> (t' o c) x" by (meson assms(1,3) order_trans)
  have 1: "t \<in> O[c going_to at_top](t' o c)"
    apply(rule bigoI[where c=1]) using assms 0 by auto
  have 2: "t' o c \<in> O[c going_to at_top](f o c)"
    unfolding o_def going_to_def
    by(rule landau_o.big.filtercomap[OF assms(2)])
  show ?thesis by(rule landau_o.big_trans[OF 1 2])
qed

section "Closest Pair Of Points Time Analysis"

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

lemma t_length_bigo:
  "t_length \<in> O[length going_to at_top](length_cost o length)"
proof -
  have "\<And>xs. t_length xs \<le> (length_cost o length) xs"
    unfolding comp_def by (simp add: length_cost_def t_length)
  thus ?thesis
    using bigo_measure_trans[of t_length length_cost length length_cost] by auto
qed


subsection "filter"

fun t_filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_filter P [] = 0"
| "t_filter P (x#xs) = (
    1 + (if P x then t_filter P xs else t_filter P xs)
  )"

lemma t_filter:
  "t_filter P xs = length xs"
  by (induction xs) auto

definition filter_cost :: "nat \<Rightarrow> real" where
  "filter_cost n = n"

lemma t_filter_conv_filter_cost:
  "t_filter P xs = filter_cost (length xs)"
  unfolding filter_cost_def using t_filter by metis

lemma t_filter_bigo:
  "t_filter P \<in> O[length going_to at_top](filter_cost o length)"
proof -
  have "\<And>xs. t_filter P xs \<le> (filter_cost o length) xs"
    unfolding comp_def  by (simp add: filter_cost_def t_filter)
  thus ?thesis
    using bigo_measure_trans[of "t_filter P" filter_cost length filter_cost] by auto
qed


subsection "take"

fun t_take :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_take n [] = 0"
| "t_take n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> 1 + t_take m xs
  )"

lemma t_take:
  "t_take n xs = min n (length xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition take_cost :: "nat \<Rightarrow> real" where
  "take_cost n = n"

lemma t_take_conv_take_cost:
  "t_take n xs \<le> take_cost (length xs)"
  unfolding take_cost_def by (auto simp: min_def t_take)

lemma t_take_bigo:
  "t_take n \<in> O[length going_to at_top](take_cost o length)"
proof -
  have "\<And>xs. t_take n xs \<le> (take_cost o length) xs"
    unfolding comp_def by (simp add: take_cost_def t_take)
  thus ?thesis
    using bigo_measure_trans[of "t_take n" take_cost length take_cost] by auto
qed

declare t_take.simps [simp del]


subsection "split_at"

fun t_split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_split_at n [] = 0"
| "t_split_at n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> 1 + t_split_at m xs
  )"

lemma t_split_at:
  "t_split_at n xs = min n (length xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition split_at_cost :: "nat \<Rightarrow> real" where
  "split_at_cost n = n"

lemma split_at_cost_nonneg[simp]:
  "0 \<le> split_at_cost n"
  unfolding split_at_cost_def by simp

lemma t_split_at_conv_split_at_cost:
  "t_split_at n xs \<le> split_at_cost (length xs)"
  unfolding split_at_cost_def by (auto simp: min_def t_split_at)

lemma t_split_at_bigo:
  "t_split_at n \<in> O[length going_to at_top](split_at_cost o length)"
proof -
  have "\<And>xs. t_split_at n xs \<le> (split_at_cost o length) xs"
    unfolding comp_def by (simp add: split_at_cost_def t_split_at)
  thus ?thesis
    using bigo_measure_trans[of "t_split_at n" split_at_cost length split_at_cost] by auto
qed


subsection "merge"

fun t_merge' :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_merge' f (x#xs) (y#ys) = (
    1 + (if f x \<le> f y then t_merge' f xs (y#ys) else t_merge' f (x#xs) ys)
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

lemma t_merge_bigo:
  assumes "m = (\<lambda>(xs, ys). length xs + length ys)"
  shows "t_merge f \<in> O[m going_to at_top](merge_cost o m)"
proof -
  have "\<And>xys. t_merge f xys \<le> (merge_cost o m) xys"
    unfolding comp_def using assms by (simp add: merge_cost_def t_merge split: prod.splits) 
  thus ?thesis
    using bigo_measure_trans[of "t_merge f" merge_cost m merge_cost] by auto
qed


subsection "msort"

function t_msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_msort f [] = 0"
| "t_msort f [_] = 1"
| "t_msort f (x # y # xs') = (
    let xs = x # y # xs' in
    let n = length xs div 2 in
    let (l, r) = split_at n xs in
    t_length xs + t_split_at n xs + t_msort f l + t_msort f r + t_merge f (l, r)
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
| "2 \<le> n \<Longrightarrow> msort_cost n = length_cost n + split_at_cost n + 
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

  let ?LHS = "t_length XS + t_split_at (N div 2) XS + t_msort f L + t_msort f R + t_merge f (L, R)"
  let ?RHS = "length_cost N + split_at_cost N + msort_cost (nat \<lfloor>real N / 2\<rfloor>) +
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
  have "\<And>xs. t_msort f xs \<le> (msort_cost o length) xs"
    unfolding comp_def using t_msort_conv_msort_cost by blast
  thus ?thesis
    by (metis (no_types, lifting) bigo_measure_trans bigthetaD1 msort_cost of_nat_0_le_iff)
qed

corollary t_sortX_bigo:
  "t_sortX \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  unfolding t_sortX_def sortX_cost_def using t_msort_bigo by blast

corollary t_sortY_bigo:
  "t_sortY \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  unfolding t_sortY_def sortY_cost_def using t_msort_bigo by blast


subsection "find_closest"

fun t_find_closest :: "point \<Rightarrow> point list \<Rightarrow> nat" where
  "t_find_closest p\<^sub>0 [] = 0"
| "t_find_closest p\<^sub>0 [p] = 1"
| "t_find_closest p\<^sub>0 (p # ps) = (
    let c = find_closest p\<^sub>0 ps in
    let t = t_find_closest p\<^sub>0 ps in
    1 + (if dist p\<^sub>0 p < dist p\<^sub>0 c then t else t)
  )"

definition find_closest_cost :: "nat \<Rightarrow> real" where
  "find_closest_cost n = n"

lemma t_find_closest:
  "t_find_closest p ps = length ps"
  by (induction p ps rule: t_find_closest.induct) auto

lemma t_find_closest_conv_find_closest_cost:
  "t_find_closest p ps = find_closest_cost (length ps)"
  unfolding find_closest_cost_def using t_find_closest by auto

lemma t_find_closest_bigo:
  "t_find_closest p\<^sub>0 \<in> O[length going_to at_top](find_closest_cost o length)"
proof -
  have "\<And>ps. t_find_closest p\<^sub>0 ps \<le> (find_closest_cost o length) ps"
    unfolding comp_def by (simp add: t_find_closest find_closest_cost_def)
  thus ?thesis
    using bigo_measure_trans[of "t_find_closest p\<^sub>0" find_closest_cost length find_closest_cost] by auto
qed


subsection "closest_pair_combine"

fun closest_pair_combine :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_combine [] = undefined"
| "closest_pair_combine [p\<^sub>0] = undefined"
| "closest_pair_combine [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_combine (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_combine ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

fun t_closest_pair_combine :: "point list \<Rightarrow> nat" where
  "t_closest_pair_combine [] = 0"
| "t_closest_pair_combine [p\<^sub>0] = 1"
| "t_closest_pair_combine [p\<^sub>0, p\<^sub>1] = 2"
| "t_closest_pair_combine (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_combine ps in
    let t_c = t_closest_pair_combine ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    let t_f = t_find_closest p\<^sub>0 (take 7 ps) in
    let t_t = t_take 7 ps in
    1 + (if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then t_c + t_f + t_t else t_c + t_f + t_t)
  )"

lemma t_closest_pair_combine:
  "t_closest_pair_combine ps \<le> 15 * length ps"
proof (induction ps rule: t_closest_pair_combine.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  have "t_closest_pair_combine ?ps \<le> 15 * length ?ps"
    using 4 prod_cases3 by metis
  moreover have "t_take 7 ?ps \<le> 7"
    by (auto simp: t_take min_def)
  ultimately show ?case
    using "4.prems" t_find_closest by auto
qed auto

definition closest_pair_combine_cost :: "nat \<Rightarrow> real" where
  "closest_pair_combine_cost n = 15 * n"

lemma t_closest_pair_combine_conv_closest_pair_combine_cost:
  "t_closest_pair_combine ps \<le> closest_pair_combine_cost (length ps)"
  unfolding closest_pair_combine_cost_def using t_closest_pair_combine of_nat_mono by blast

lemma t_closest_pair_combine_bigo:
  "t_closest_pair_combine \<in> O[length going_to at_top](closest_pair_combine_cost o length)"
proof -
  have "\<And>ps. t_closest_pair_combine ps \<le> (closest_pair_combine_cost o length) ps"
    unfolding comp_def using closest_pair_combine_cost_def t_closest_pair_combine_conv_closest_pair_combine_cost by auto
  thus ?thesis
    using bigo_measure_trans[of t_closest_pair_combine closest_pair_combine_cost length closest_pair_combine_cost] by auto
qed


subsection "closest_pair_bf"

fun closest_pair_bf :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_bf [] = undefined"
| "closest_pair_bf [p\<^sub>0] = undefined"
| "closest_pair_bf [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_bf (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps in
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

fun t_closest_pair_bf :: "point list \<Rightarrow> nat" where
  "t_closest_pair_bf [] = 0"
| "t_closest_pair_bf [p\<^sub>0] = 1"
| "t_closest_pair_bf [p\<^sub>0, p\<^sub>1] = 2"
| "t_closest_pair_bf (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps in
    let t_c = t_closest_pair_bf ps in
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    let t_f = t_find_closest p\<^sub>0 ps in
    1 + (if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then t_c + t_f else t_c + t_f)
  )"

lemma t_closest_pair_bf:
  "t_closest_pair_bf ps \<le> length ps * length ps"
proof (induction ps rule: t_closest_pair_combine.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  have "t_closest_pair_bf ?ps \<le> length ?ps * length ?ps"
    using 4 prod_cases3 by metis
  thus ?case
    using "4.prems" t_find_closest by auto
qed auto

definition closest_pair_bf_cost :: "nat \<Rightarrow> real" where
  "closest_pair_bf_cost n = n * n"

lemma closest_pair_bf_cost_nonneg[simp]:
  "0 \<le> closest_pair_bf_cost n"
  unfolding closest_pair_bf_cost_def by simp

lemma t_closest_pair_bf_conv_closest_pair_bf_cost:
  "t_closest_pair_bf ps \<le> closest_pair_bf_cost (length ps)"
  unfolding closest_pair_bf_cost_def using t_closest_pair_bf of_nat_mono by blast

lemma t_closest_pair_bf_bigo:
  "t_closest_pair_bf \<in> O[length going_to at_top](closest_pair_bf_cost o length)"
proof -
  have "\<And>ps. t_closest_pair_bf ps \<le> (closest_pair_bf_cost o length) ps"
    unfolding comp_def using closest_pair_bf_cost_def t_closest_pair_bf_conv_closest_pair_bf_cost by auto
  thus ?thesis
    using bigo_measure_trans[of t_closest_pair_bf closest_pair_bf_cost length closest_pair_bf_cost] by auto
qed


subsection "combine"

fun t_combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> nat" where
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let \<delta> = dist c\<^sub>0 c\<^sub>1 in
    let ys' = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) ys in
    let t_f = t_filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) ys in
    t_f + t_length ys' + (if length ys' < 2 then
      0
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_combine ys' in
      let t_c = t_closest_pair_combine ys' in
      if dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1 then t_c else t_c
    )
  )"

definition combine_cost :: "nat \<Rightarrow> real" where
  "combine_cost n = 17 * n"

lemma t_combine:
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys \<le> 17 * length ys"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  let ?P = "(\<lambda>p. l - dist C\<^sub>0 C\<^sub>1 \<le> fst p \<and> fst p \<le> l + dist C\<^sub>0 C\<^sub>1)"
  let ?ys' = "filter ?P ys"
  let ?t_f = "t_filter ?P ys"
  let ?t_l = "t_length ?ys'"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine ?ys'"
    using prod.collapse by blast
  let ?t_c = "t_closest_pair_combine ?ys'"
  note defs = C\<^sub>0\<^sub>1_def P\<^sub>0\<^sub>1_def

  show ?thesis
  proof cases
    assume "length ?ys' < 2"
    hence "?t_l + ?t_f = t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "?t_f = length ys"
      using t_filter[of ?P ys] by simp
    moreover have "?t_l \<le> length ys"
      by (simp add: t_length)
    ultimately show ?thesis
      by linarith
  next
    assume *: "\<not> length ?ys' < 2"
    have "?t_c \<le> 15 * length ?ys'"
      using t_closest_pair_combine by simp
    moreover have "length ?ys' \<le> length ys"
      by simp
    ultimately have "?t_c \<le> 15 * length ys"
      by linarith
    moreover have "?t_l + ?t_f + ?t_c = t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using * defs by (auto simp: Let_def split!: prod.splits)
    moreover have "?t_f = length ys"
      using t_filter[of ?P ys] by simp
    moreover have "?t_l \<le> length ys"
      by (simp add: t_length)
    ultimately show ?thesis
      by linarith
  qed
qed

lemma t_combine_conv_combine_cost:
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys \<le> combine_cost (length ys)"
  unfolding combine_cost_def using t_combine of_nat_mono by blast

lemma t_combine_bigo:
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l \<in> O[length going_to at_top](combine_cost o length)"
proof -
  have "\<And>ys. t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys \<le> (combine_cost o length) ys"
    unfolding comp_def using combine_cost_def t_combine_conv_combine_cost by auto
  thus ?thesis
    using bigo_measure_trans[of "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l" combine_cost length combine_cost] by auto
qed

declare t_combine.simps [simp del]


subsection "closest_pair_rec"

function t_closest_pair_rec :: "point list \<Rightarrow> nat" where
  "t_closest_pair_rec xs = (
    let n = length xs in
    let t_l = t_length xs in
    if n \<le> 3 then
      n + t_l + t_sortY xs + t_closest_pair_bf xs
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let t_s = t_split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
      let t_cl = t_closest_pair_rec xs\<^sub>L in
      let t_cr = t_closest_pair_rec xs\<^sub>R in

      let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
      let t_m = t_merge (\<lambda>p. snd p) (ys\<^sub>L, ys\<^sub>R) in
      let t_c = t_combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys in
      1 + t_l + t_s + t_cl + t_cr + t_m + t_c
  )"
  by pat_completeness auto
termination t_closest_pair_rec
  apply (relation "Wellfounded.measure (\<lambda>xs. length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

lemma t_closest_pair_rec_simps_1:
  assumes "n = length xs" "n \<le> 3"
  shows "t_closest_pair_rec xs = n + t_length xs + t_sortY xs + t_closest_pair_bf xs"
  using assms by simp

lemma t_closest_pair_rec_simps_2:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "t_closest_pair_rec xs = (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let t_s = t_split_at (n div 2) xs in
    let l = fst (hd xs\<^sub>R) in
    let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
    let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
    let t_cl = t_closest_pair_rec xs\<^sub>L in
    let t_cr = t_closest_pair_rec xs\<^sub>R in
    let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
    let t_m = t_merge (\<lambda>p. snd p) (ys\<^sub>L, ys\<^sub>R) in
    let t_c = t_combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys in
    1 + t_length xs + t_s + t_cl + t_cr + t_m + t_c
  )"
  using assms by (auto simp add: Let_def)

declare t_closest_pair_rec.simps [simp del]

function closest_pair_rec_cost :: "nat \<Rightarrow> real" where
  "n \<le> 3 \<Longrightarrow> closest_pair_rec_cost n = n + length_cost n + sortY_cost n + closest_pair_bf_cost n"
| "3 < n \<Longrightarrow> closest_pair_rec_cost n = 1 + length_cost n + split_at_cost n + 
    closest_pair_rec_cost (nat \<lfloor>real n / 2\<rfloor>) + closest_pair_rec_cost (nat \<lceil>real n / 2\<rceil>) +
    merge_cost n + combine_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

lemma t_closest_pair_rec_conv_closest_pair_rec_cost:
  "t_closest_pair_rec ps \<le> closest_pair_rec_cost (length ps)"
proof (induction ps rule: length_induct)
  case (1 ps)
  let ?n = "length ps"
  show ?case
  proof (cases "?n \<le> 3")
    case True        
    hence "t_closest_pair_rec ps = 
           ?n + t_length ps + t_sortY ps + t_closest_pair_bf ps"
      using t_closest_pair_rec_simps_1 by simp
    moreover have "closest_pair_rec_cost ?n = 
                   ?n + length_cost ?n + sortY_cost ?n + closest_pair_bf_cost ?n"
      using True by simp
    ultimately show ?thesis
      using t_length_conv_length_cost t_sortY_conv_sortY_cost
            t_closest_pair_bf_conv_closest_pair_bf_cost of_nat_add
      by (smt of_nat_1)
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) ps"
      using prod.collapse by blast
    define TS where "TS = t_split_at (?n div 2) ps"
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where CP\<^sub>L_def: "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by metis
    define TL where "TL = t_closest_pair_rec XS\<^sub>L"
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where CP\<^sub>R_def: "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by metis
    define TR where "TR = t_closest_pair_rec XS\<^sub>R"

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define TM where "TM = t_merge (\<lambda>p. snd p) (YS\<^sub>L, YS\<^sub>R)"
    define TC where "TC = t_combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
    note defs = XS_def TS_def L_def CP\<^sub>L_def TL_def CP\<^sub>R_def TR_def YS_def TM_def TC_def

    have FL: "t_closest_pair_rec ps = 1 + t_length ps + TS + TL + TR + TM + TC"
      using False t_closest_pair_rec_simps_2 defs by (auto split: prod.splits)

    have FR: "closest_pair_rec_cost (length ps) =
              1 + length_cost ?n + split_at_cost ?n + closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>) +
              closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>) + merge_cost ?n + combine_cost ?n"
      using False by simp

    have XSLR: "XS\<^sub>L = take (?n div 2) ps" "XS\<^sub>R = drop (?n div 2) ps"
      using defs by (auto simp: split_at_take_drop_conv)
    hence "length XS\<^sub>L = ?n div 2" "length XS\<^sub>R = ?n - ?n div 2"
      by simp_all
    hence *: "(nat \<lfloor>real ?n / 2\<rfloor>) = length XS\<^sub>L" "(nat \<lceil>real ?n / 2\<rceil>) = length XS\<^sub>R"
      by linarith+
    have "length XS\<^sub>L = length YS\<^sub>L" "length XS\<^sub>R = length YS\<^sub>R"
      using defs closest_pair_rec_set_length_sortedY by metis+
    hence L: "?n = length YS\<^sub>L + length YS\<^sub>R"
      using defs XSLR by fastforce

    have "length XS\<^sub>L < length ps"
      using False XSLR by simp
    hence "t_closest_pair_rec XS\<^sub>L \<le> closest_pair_rec_cost (length XS\<^sub>L)"
      using 1 by simp
    hence IHL: "t_closest_pair_rec XS\<^sub>L \<le> closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>)"
      using * by simp

    have "length XS\<^sub>R < length ps"
      using False XSLR by simp_all
    hence "t_closest_pair_rec XS\<^sub>R \<le> closest_pair_rec_cost (length XS\<^sub>R)"
      using 1 by simp
    hence IHR: "t_closest_pair_rec XS\<^sub>R \<le> closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>)"
      using * by simp

    have "t_length ps = length_cost ?n"
      using t_length_conv_length_cost by blast
    moreover have "TS \<le> split_at_cost ?n"
      using t_split_at_conv_split_at_cost TS_def by blast
    moreover have "TL \<le> closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>)"
      using IHL TL_def by blast
    moreover have "TR \<le> closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>)"
      using IHR TR_def by blast
    moreover have "TM \<le> merge_cost ?n"
      using L t_merge_conv_merge_cost TM_def by auto
    moreover have "TC \<le> combine_cost ?n"
      using L defs length_merge t_combine_conv_combine_cost by metis
    ultimately show ?thesis
      using FL FR by linarith
  qed
qed

theorem closest_pair_rec_cost:
  "closest_pair_rec_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  by (master_theorem) (auto simp: length_cost_def split_at_cost_def merge_cost_def combine_cost_def)

theorem t_closest_pair_rec_bigo:
  "t_closest_pair_rec \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
proof -
  have "\<And>xs. t_closest_pair_rec xs \<le> (closest_pair_rec_cost o length) xs"
    unfolding comp_def using t_closest_pair_rec_conv_closest_pair_rec_cost by blast
  thus ?thesis
    by (metis (no_types, lifting) bigo_measure_trans bigthetaD1 closest_pair_rec_cost of_nat_0_le_iff)
qed


subsection "closest_pair"

definition t_closest_pair :: "point list \<Rightarrow> nat" where
  "t_closest_pair ps = t_sortX ps + t_closest_pair_rec (sortX ps)"

definition closest_pair_cost :: "nat \<Rightarrow> real" where
  "closest_pair_cost n = sortX_cost n + closest_pair_rec_cost n"

lemma t_closest_pair_conv_closest_pair_cost:
  "t_closest_pair ps \<le> closest_pair_cost (length ps)"
  unfolding t_closest_pair_def closest_pair_cost_def
  using t_sortX_conv_sortX_cost t_closest_pair_rec_conv_closest_pair_rec_cost length_sortX of_nat_add by smt

theorem closest_pair_cost:
  "closest_pair_cost \<in> O(\<lambda>n. n * ln n)"
  unfolding closest_pair_cost_def
  using sortX_cost closest_pair_rec_cost sum_in_bigo(1) by blast

theorem t_closest_pair_bigo:
  "t_closest_pair \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
proof -
  have "\<And>ps. t_closest_pair ps \<le> (closest_pair_cost o length) ps"
    unfolding comp_def using t_closest_pair_conv_closest_pair_cost by blast
  thus ?thesis
    by (metis (no_types, lifting) bigo_measure_trans closest_pair_cost of_nat_0_le_iff)
qed

end