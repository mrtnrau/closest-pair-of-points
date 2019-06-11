theory Test
imports 
  "HOL-Analysis.Analysis"
  "Landau_Symbols.Landau_More"
  "Akra_Bazzi.Akra_Bazzi_Method"
  "Akra_Bazzi.Akra_Bazzi_Approximation"
begin

section "Time Analysis Merge Sort"

subsection "Time Analysis take and drop"

fun t_take :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_take _ [] = 0"
| "t_take n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc n \<Rightarrow> 1 + t_take n xs
  )"

lemma t_take:
  "t_take n xs = min n (length xs)"
  apply (induction n xs rule: t_take.induct)
    apply (auto split: nat.split)
  done

definition take_cost :: "nat \<Rightarrow> real" where
  "take_cost n = real n"

lemma take_cost_nonneg[simp]:
  "0 \<le> take_cost n"
  unfolding take_cost_def by simp

lemma t_take_conv_take_cost:
  "real (t_take n xs) \<le> take_cost (length xs)"
  unfolding take_cost_def by (auto simp add: min_def t_take)

lemma take_cost_big_theta:
  "take_cost \<in> \<Theta>(\<lambda>n. n::real)"
  unfolding take_cost_def by simp

fun t_drop :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_drop _ [] = 0"
| "t_drop n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc n \<Rightarrow> 1 + t_drop n xs
  )"

lemma t_drop:
  "t_drop n xs = min n (length xs)"
  apply (induction n xs rule: t_drop.induct)
    apply (auto split: nat.split)
  done

definition drop_cost :: "nat \<Rightarrow> real" where
  "drop_cost n = real n"

lemma drop_cost_nonneg[simp]:
  "0 \<le> drop_cost n"
  unfolding drop_cost_def by simp

lemma t_drop_conv_drop_cost:
  "real (t_drop n xs) \<le> drop_cost (length xs)"
  unfolding drop_cost_def by (auto simp add: min_def t_drop)

lemma drop_cost_big_theta:
  "drop_cost \<in> \<Theta>(\<lambda>n. n::real)"
  unfolding drop_cost_def by simp


subsection "Time Analysis merge"

fun merge :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge (x#xs) (y#ys) = (
    if x \<le> y then 
      x # merge xs (y#ys)
    else
      y # merge (x#xs) ys)"
| "merge xs [] = xs"
| "merge [] ys = ys"

lemma length_merge:
  "length (merge xs ys) = length xs + length ys"
  apply (induction xs ys rule: merge.induct)
    apply (auto)
  done

fun t_merge :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_merge (x#xs) (y#ys) = (
    if x \<le> y then
      1 + t_merge xs (y#ys)
    else
      1 + t_merge (x#xs) ys
  )"
| "t_merge xs [] = 0"
| "t_merge [] ys = 0"

lemma t_merge:
  "t_merge xs ys \<le> length xs + length ys"
  apply (induction xs ys rule: t_merge.induct)
    apply (auto)
  done

definition merge_cost :: "nat \<Rightarrow> real" where
  "merge_cost n = real n"

lemma merge_cost_nonneg[simp]:
  "0 \<le> merge_cost n"
  unfolding merge_cost_def by simp

lemma t_merge_conv_merge_cost:
  "real (t_merge xs ys) \<le> merge_cost (length xs + length ys)"
  unfolding merge_cost_def by (metis of_nat_mono t_merge)

lemma merge_cost_big_theta:
  "merge_cost \<in> \<Theta>(\<lambda>n. n::real)"
  unfolding merge_cost_def by simp


subsection "Time Analysis msort"

fun msort :: "('a::linorder) list \<Rightarrow> 'a list" where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = merge (msort (take (length xs div 2) xs))
                    (msort (drop (length xs div 2) xs))"

lemma length_msort[simp]:
  "length (msort xs) = length xs"
  apply (induction xs rule: msort.induct)
    apply (auto simp add: min_def length_merge)
  done

fun t_msort :: "('a::linorder) list \<Rightarrow> nat" where
  "t_msort [] = 0"
| "t_msort [_] = 1"
| "t_msort xs = (
    let n = length xs div 2 in
    let l = msort (take n xs) in
    let r = msort (drop n xs) in
    t_take n xs + t_drop n xs + t_msort l + t_msort r + t_merge l r
  )"

function merge_sort_cost :: "nat \<Rightarrow> real" where
  "merge_sort_cost 0 = 0"
| "merge_sort_cost 1 = 1"
| "2 \<le> n \<Longrightarrow> merge_sort_cost n =
    take_cost n + drop_cost n + merge_sort_cost (nat \<lfloor>real n / 2\<rfloor>) + merge_sort_cost (nat \<lceil>real n / 2\<rceil>) + merge_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

declare t_take.simps t_drop.simps t_merge.simps[simp del]

lemma t_merge_sort_conv_merge_sort_cost:
  "real (t_msort xs) \<le> merge_sort_cost (length xs)"
  oops

lemma merge_sort_nonneg[simp]:
  "0 \<le> merge_sort_cost n"
  apply (induction n rule: merge_sort_cost.induct)
    apply (auto simp del: One_nat_def)
  done

lemma msort_cost:
  "merge_sort_cost \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  apply (master_theorem)
    apply (auto simp add: take_cost_def drop_cost_def merge_cost_def)
  done

end