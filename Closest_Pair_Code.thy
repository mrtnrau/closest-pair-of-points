theory Closest_Pair_Code
  imports
    Closest_Pair
    (* "HOL-Library.Code_Real_Approx_By_Float" *)
    "HOL-Library.Code_Target_Numeral"
begin

section "Closest Pair Of Points Exported Code"

subsection "auxiliary"

fun rev_it_rec :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_it_rec acc [] = acc"
| "rev_it_rec acc (x#xs) = rev_it_rec (x#acc) xs"

definition rev_it :: "'a list \<Rightarrow> 'a list" where
  "rev_it xs = rev_it_rec [] xs"

lemma rev_conv_rev_it_rec:
  "rev xs @ acc = rev_it_rec acc xs"
  by (induction acc xs rule: rev_it_rec.induct) auto

lemma rev_conv_rev_it[code_unfold]:
  "rev xs = rev_it xs"
  unfolding rev_it_def using rev_conv_rev_it_rec append_Nil2 by metis

lemma merge_xs_Nil[simp]:
  "merge f xs [] = xs"
  by (cases xs) auto

fun merge_it_rec :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge_it_rec _ acc [] [] = rev acc"
| "merge_it_rec f acc (x#xs) [] = merge_it_rec f (x#acc) xs []"
| "merge_it_rec f acc [] (y#ys) = merge_it_rec f (y#acc) ys []"
| "merge_it_rec f acc (x#xs) (y#ys) = (
    if f x \<le> f y then
      merge_it_rec f (x#acc) xs (y#ys)
    else
      merge_it_rec f (y#acc) (x#xs) ys
  )"

definition merge_it :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge_it f xs ys = merge_it_rec f [] xs ys"

lemma merge_conv_merge_it_rec:
  "rev acc @ merge f xs ys = merge_it_rec f acc xs ys"
  by (induction f acc xs ys rule: merge_it_rec.induct) auto

lemma merge_conv_merge_it[code_unfold]:
  "merge f xs ys = merge_it f xs ys"
  unfolding merge_it_def using merge_conv_merge_it_rec rev.simps(1) append_Nil by metis

subsection "find_closest"

fun find_closest_it_rec :: "point \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_it_rec _ c\<^sub>0 [] = c\<^sub>0"
| "find_closest_it_rec p c\<^sub>0 (c\<^sub>1 # cs) = (
    if dist p c\<^sub>0 < dist p c\<^sub>1 then
      find_closest_it_rec p c\<^sub>0 cs
    else 
      find_closest_it_rec p c\<^sub>1 cs
  )"

fun find_closest_it :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_it _ [] = undefined"
| "find_closest_it p (p\<^sub>0 # ps) = find_closest_it_rec p p\<^sub>0 ps"

lemma find_closest_drop_snd:
  "dist p p\<^sub>0 < dist p p\<^sub>1 \<Longrightarrow> find_closest p (p\<^sub>0 # p\<^sub>1 # ps) = find_closest p (p\<^sub>0 # ps)"
  by (induction p ps arbitrary: p\<^sub>1 rule: find_closest.induct) (auto simp add: Let_def)

lemma find_closest_drop_fst:
  "\<not> dist p p\<^sub>0 < dist p p\<^sub>1 \<Longrightarrow> find_closest p (p\<^sub>0 # p\<^sub>1 # ps) = find_closest p (p\<^sub>1 # ps)"
  by (induction p ps arbitrary: p\<^sub>1 rule: find_closest.induct) (auto simp add: Let_def)

lemma find_closest_conv_find_closest_it_rec:
  "find_closest p (c\<^sub>0 # cs) = find_closest_it_rec p c\<^sub>0 cs"
proof (induction p c\<^sub>0 cs rule: find_closest_it_rec.induct)
  case (2 p c\<^sub>0 c\<^sub>1 cs)
  then show ?case
  proof (cases "dist p c\<^sub>0 < dist p c\<^sub>1")
    case True
    thus ?thesis
      using find_closest_drop_snd "2"(1) by simp
  next
    case False
    hence "find_closest_it_rec p c\<^sub>0 (c\<^sub>1 # cs) = find_closest p (c\<^sub>1 # cs)"
      using False "2"(2) by simp
    thus ?thesis
      using find_closest_drop_fst False by simp
  qed
qed simp

lemma find_closest_conv_find_closest_it[code_unfold]:
  "find_closest p ps = find_closest_it p ps"
  using find_closest_conv_find_closest_it_rec by (cases ps) simp_all

subsection "bf_closest_pair"

fun bf_closest_pair_it_rec :: "(point * point) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) [] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) [_] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest_it p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 < dist p\<^sub>0 p\<^sub>1 then
      bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) ps
    else
      bf_closest_pair_it_rec (p\<^sub>0, p\<^sub>1) ps
  )"

fun bf_closest_pair_it :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # p\<^sub>1 # ps)"
| "bf_closest_pair_it _ = undefined"

lemma bf_closest_pair_conv_bf_closest_pair_it_rec:
  "bf_closest_pair (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # p\<^sub>1 # ps)"
  sorry

lemma bf_closest_pair_conv_bf_closest_pair_it[code_unfold]:
  "bf_closest_pair ps = bf_closest_pair_it ps"
  using bf_closest_pair_conv_bf_closest_pair_it_rec
  by (metis bf_closest_pair.simps(1,2) bf_closest_pair_it.elims bf_closest_pair_it.simps(2))

subsection "dist"

definition dist_code :: "point \<Rightarrow> point \<Rightarrow> real" where
  "dist_code p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

lemma dist_point:
  "dist (p\<^sub>0 :: point) p\<^sub>1 = sqrt ((fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2)"
  by (simp add: dist_prod_def dist_real_def)

lemma dist_transform:
  "(l - dist (c\<^sub>0 :: point) c\<^sub>1 \<le> fst (p :: point) \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1) \<longleftrightarrow> dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1"
proof -
  have "dist p (l, snd p) = \<bar>fst p - l\<bar>"
    using dist_point by simp
  thus ?thesis
    by linarith
qed

fun combine_code :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine_code (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ys' = filter (\<lambda>p. dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1) ys in
    if length ys' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_7 ys' in
      if dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1 then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

lemma combine_conv_combine_code[code_unfold]:
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = combine_code (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
  using dist_transform by simp

lemma lt_dist_conv_lt_sq_dist[code_unfold]:
  "dist a b < dist c d \<longleftrightarrow> dist_code a b < dist_code c d"
  using dist_point dist_code_def by simp

lemma le_dist_conv_le_sq_dist[code_unfold]:
  "dist a b \<le> dist c d \<longleftrightarrow> dist_code a b \<le> dist_code c d"
  using dist_point dist_code_def by simp

subsection "Export Code"

export_code closest_pair in SML
  module_name ClosestPair

end