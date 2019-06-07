theory Test
imports 
  "HOL-Analysis.Analysis"
  "Landau_Symbols.Landau_More"
  "Akra_Bazzi.Akra_Bazzi_Method"
  "Akra_Bazzi.Akra_Bazzi_Approximation"
begin

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

fun t_take :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_take _ [] = 0"
| "t_take n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc n \<Rightarrow> 1 + t_take n xs
  )"

fun t_drop :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_drop _ [] = 0"
| "t_drop n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc n \<Rightarrow> 1 + t_drop n xs
  )"

lemma t_take:
  "t_take n xs = min n (length xs)"
  apply (induction n xs rule: t_take.induct)
    apply (auto split: nat.split)
  done

lemma t_drop:
  "t_drop n xs = min n (length xs)"
  apply (induction n xs rule: t_drop.induct)
    apply (auto split: nat.split)
  done

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

(* *)

function merge_sort_cost :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "merge_sort_cost _ 0 = 0"
| "merge_sort_cost _ 1 = 1"
| "2 \<le> n \<Longrightarrow> merge_sort_cost t n =
    merge_sort_cost t (nat \<lfloor>real n / 2\<rfloor>) + merge_sort_cost t (nat \<lceil>real n / 2\<rceil>) + t n"
  by force simp_all
termination by akra_bazzi_termination simp_all

lemma merge_sort_nonneg[simp]:
  "(\<And>n. 0 \<le> t n) \<Longrightarrow> 0 \<le> merge_sort_cost t n"
  apply (induction t n rule: merge_sort_cost.induct)
    apply (auto simp del: One_nat_def)
  done

lemma "t \<in> \<Theta>(\<lambda>n. real n) \<Longrightarrow> (\<And>n. 0 \<le> t n) \<Longrightarrow> merge_sort_cost t \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  apply (master_theorem)
    apply auto
  done

definition take_cost :: "nat \<Rightarrow> real" where
  "take_cost n = real n"

lemma t_take_conv_take_cost:
  "real (t_take n xs) \<le> take_cost (length xs)"
  unfolding take_cost_def by (auto simp add: min_def t_take)

lemma take_cost_big_theta:
  "take_cost \<in> \<Theta>(\<lambda>n. n::real)"
  unfolding take_cost_def by simp

definition drop_cost :: "nat \<Rightarrow> real" where
  "drop_cost n = real n"

lemma t_drop_conv_drop_cost:
  "real (t_drop n xs) \<le> drop_cost (length xs)"
  unfolding drop_cost_def by (auto simp add: min_def t_drop)

lemma drop_cost_big_theta:
  "drop_cost \<in> \<Theta>(\<lambda>n. n::real)"
  unfolding drop_cost_def by simp

definition take_drop_cost :: "nat \<Rightarrow> real" where
  "take_drop_cost n = take_cost n + drop_cost n"

lemma take_drop_big_theta:
  "take_drop_cost \<in> \<Theta>(\<lambda>n. n::real)"
  unfolding take_drop_cost_def take_cost_def drop_cost_def by simp

end