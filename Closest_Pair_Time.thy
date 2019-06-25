theory Closest_Pair_Time
imports 
  Closest_Pair
  "Landau_Symbols.Landau_More"
  "Akra_Bazzi.Akra_Bazzi_Method"
  "Akra_Bazzi.Akra_Bazzi_Approximation"
begin

section "Time Analysis Merge Sort"

subsection "Time Analysis length"

fun t_length :: "'a list \<Rightarrow> nat" where
  "t_length [] = 0"
| "t_length (x#xs) = 1 + t_length xs"

lemma t_length:
  "t_length xs = length xs"
  by (induction xs) auto

definition length_cost :: "nat \<Rightarrow> real" where
  "length_cost n = real n"

lemma length_cost_nonneg[simp]:
  "0 \<le> length_cost n"
  unfolding length_cost_def by simp

lemma t_length_conv_length_cost:
  "t_length xs \<le> length_cost (length xs)"
  unfolding length_cost_def by (auto simp add: t_length)


subsection "Time Analysis split_at"

fun t_split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_split_at _ [] = 0"
| "t_split_at n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> 1 + t_split_at m xs
  )"

lemma t_split_at:
  "t_split_at n xs = min n (length xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition split_at_cost :: "nat \<Rightarrow> real" where
  "split_at_cost n = real n"

lemma split_at_cost_nonneg[simp]:
  "0 \<le> split_at_cost n"
  unfolding split_at_cost_def by simp

lemma t_split_at_conv_split_at_cost:
  "t_split_at n xs \<le> split_at_cost (length xs)"
  unfolding split_at_cost_def by (auto simp add: min_def t_split_at)


subsection "Time Analysis merge"

fun t_merge :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_merge f (x#xs) (y#ys) = (
    if f x \<le> f y then
      1 + t_merge f xs (y#ys)
    else
      1 + t_merge f (x#xs) ys
  )"
| "t_merge _ xs [] = 0"
| "t_merge _ [] ys = 0"

lemma t_merge:
  "t_merge f xs ys \<le> length xs + length ys"
  by (induction f xs ys rule: t_merge.induct) auto

definition merge_cost :: "nat \<Rightarrow> real" where
  "merge_cost n = real n"

lemma merge_cost_nonneg[simp]:
  "0 \<le> merge_cost n"
  unfolding merge_cost_def by simp

lemma t_merge_conv_merge_cost:
  "t_merge f xs ys \<le> merge_cost (length xs + length ys)"
  unfolding merge_cost_def by (metis of_nat_mono t_merge)


subsection "Time Analysis msort"

function t_msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_msort _ [] = 0"
| "t_msort _ [_] = 1"
| "t_msort f (x # y # xs') = (
    let xs = x # y # xs' in
    let n = length xs div 2 in
    let (l, r) = split_at n xs in
    t_length xs + t_split_at n xs + t_msort f l + t_msort f r + t_merge f l r
  )"
  by pat_completeness auto
termination t_msort
  apply (relation "Wellfounded.measure (\<lambda>(_, xs). length xs)")
  apply (auto simp add: split_at_take_drop_conv Let_def)
  done

function msort_cost :: "nat \<Rightarrow> real" where
  "msort_cost 0 = 0"
| "msort_cost 1 = 1"
| "2 \<le> n \<Longrightarrow> msort_cost n =
    length_cost n + split_at_cost n + msort_cost (nat \<lfloor>real n / 2\<rfloor>) + msort_cost (nat \<lceil>real n / 2\<rceil>) + merge_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

declare t_length.simps t_split_at.simps t_merge.simps[simp del]


lemma t_merge_sort_conv_merge_sort_cost:
  "t_msort f xs \<le> msort_cost (length xs)"
proof (induction f xs rule: t_msort.induct)
  case (2 f x)
  thus ?case
    using msort_cost.simps(2) by auto
next
  case (3 f x y xs')

  define XS where "XS = x # y # xs'"
  define N where "N = length XS"
  define LR where "LR = split_at (N div 2) XS"
  define L where "L = fst LR"
  define R where "R = snd LR"
  note defs = XS_def N_def LR_def L_def R_def

  have IHL: "t_msort f L \<le> msort_cost (length L)"
    using defs "3.IH"(1) prod.collapse by blast
  have IHR: "t_msort f R \<le> msort_cost (length R)"
    using defs "3.IH"(2) prod.collapse by blast

  have t_msort: "t_msort f XS = t_length XS  + t_split_at (N div 2) XS + t_msort f L + t_msort f R + t_merge f L R"
    by (auto simp add: defs split: prod.split)
  have msort_cost: "msort_cost N = length_cost N + split_at_cost N + msort_cost (nat \<lfloor>real N / 2\<rfloor>) + msort_cost (nat \<lceil>real N / 2\<rceil>) + merge_cost N"
    by (simp add: defs)

  have *: "length L = N div 2" "length R = N - N div 2"
    by (auto simp add: defs split_at_take_drop_conv)
  hence "(nat \<lfloor>real N / 2\<rfloor>) = length L" "(nat \<lceil>real N / 2\<rceil>) = length R"
    by linarith+
  hence tIH: "t_msort f L \<le> msort_cost (nat \<lfloor>real N / 2\<rfloor>)" "t_msort f R \<le> msort_cost (nat \<lceil>real N / 2\<rceil>)"
    using IHL IHR by simp_all

  have "N = length L + length R"
    using * by linarith
  hence "t_merge f L R \<le> merge_cost N"
    using t_merge_conv_merge_cost by metis
  moreover have "t_length XS \<le> length_cost N"
    using t_length_conv_length_cost defs by blast
  moreover have "t_split_at (N div 2) XS \<le> split_at_cost N"
    using t_split_at_conv_split_at_cost defs by blast
  ultimately have "t_length XS + t_split_at (N div 2) XS + t_msort f L + t_msort f R + t_merge f L R \<le>
    length_cost N + split_at_cost N + msort_cost (nat \<lfloor>real N / 2\<rfloor>) + msort_cost (nat \<lceil>real N / 2\<rceil>) + merge_cost N"
    using tIH by simp
  hence "t_msort f XS \<le> msort_cost N"
    using t_msort msort_cost by presburger
  thus ?case
    using XS_def N_def by blast
qed auto

lemma msort_nonneg[simp]:
  "0 \<le> msort_cost n"
  by (induction n rule: msort_cost.induct) (auto simp del: One_nat_def)

lemma msort_cost:
  "msort_cost \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  by (master_theorem) (auto simp add: length_cost_def split_at_cost_def merge_cost_def)

end