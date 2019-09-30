theory Closest_Pair_Code
  imports
    Closest_Pair
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Real_Approx_By_Float"
begin

section "Closest Pair Of Points Without Stackoverflow"

subsection "length"

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


subsection "filter"

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


subsection "split_at"

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


subsection "merge"

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


subsection "find_closest"

fun find_closest_it' :: "point \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_it' p c\<^sub>0 [] = c\<^sub>0"
| "find_closest_it' p c\<^sub>0 (c\<^sub>1 # cs) = (
    if dist p c\<^sub>0 < dist p c\<^sub>1 then
      find_closest_it' p c\<^sub>0 cs
    else 
      find_closest_it' p c\<^sub>1 cs
  )"

fun find_closest_it :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_it _ [] = undefined"
| "find_closest_it p (p\<^sub>0 # ps) = find_closest_it' p p\<^sub>0 ps"

lemma find_closest_drop_snd:
  "dist p p\<^sub>0 < dist p p\<^sub>1 \<Longrightarrow> find_closest p (p\<^sub>0 # p\<^sub>1 # ps) = find_closest p (p\<^sub>0 # ps)"
  by (induction p ps arbitrary: p\<^sub>1 rule: find_closest.induct) (auto simp: Let_def)

lemma find_closest_drop_fst:
  "\<not> dist p p\<^sub>0 < dist p p\<^sub>1 \<Longrightarrow> find_closest p (p\<^sub>0 # p\<^sub>1 # ps) = find_closest p (p\<^sub>1 # ps)"
  by (induction p ps arbitrary: p\<^sub>1 rule: find_closest.induct) (auto simp: Let_def)

lemma find_closest_conv_find_closest_it':
  "find_closest p (c\<^sub>0 # cs) = find_closest_it' p c\<^sub>0 cs"
proof (induction p c\<^sub>0 cs rule: find_closest_it'.induct)
  case (2 p c\<^sub>0 c\<^sub>1 cs)
  then show ?case
  proof (cases "dist p c\<^sub>0 < dist p c\<^sub>1")
    case True
    thus ?thesis
      using find_closest_drop_snd "2"(1) by simp
  next
    case False
    hence "find_closest_it' p c\<^sub>0 (c\<^sub>1 # cs) = find_closest p (c\<^sub>1 # cs)"
      using False "2"(2) by simp
    thus ?thesis
      using find_closest_drop_fst False by simp
  qed
qed simp

lemma find_closest_conv_find_closest_it[code_unfold]:
  "find_closest p ps = find_closest_it p ps"
  using find_closest_conv_find_closest_it' by (cases ps) simp_all


subsection "closest_pair_combine"

fun closest_pair_combine_it' :: "(point * point) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "closest_pair_combine_it' (c\<^sub>0, c\<^sub>1) [] = (c\<^sub>0, c\<^sub>1)"
| "closest_pair_combine_it' (c\<^sub>0, c\<^sub>1) [p\<^sub>0] = (c\<^sub>0, c\<^sub>1)"
| "closest_pair_combine_it' (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist c\<^sub>0 c\<^sub>1 < dist p\<^sub>0 p\<^sub>1 then
      closest_pair_combine_it' (c\<^sub>0, c\<^sub>1) ps
    else
      closest_pair_combine_it' (p\<^sub>0, p\<^sub>1) ps
  )"

fun closest_pair_combine_it :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_combine_it (p\<^sub>0 # p\<^sub>1 # ps) = closest_pair_combine_it' (p\<^sub>0, find_closest p\<^sub>0 (take 7 (p\<^sub>1 # ps))) (p\<^sub>1 # ps)"
| "closest_pair_combine_it _ = undefined"

fun fl :: "point * point \<Rightarrow> point list \<Rightarrow> point * point" where
  "fl c [] = (fst c, snd c)"
| "fl c [p\<^sub>0] = (fst c, snd c)"
| "fl c (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist (fst c) (snd c) < dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

fun fr :: "point list \<Rightarrow> point * point \<Rightarrow> point * point" where
  "fr [] c = (fst c, snd c)"
| "fr [p\<^sub>0] c = (fst c, snd c)"
| "fr (p\<^sub>0 # ps) c = (
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist (fst c) (snd c) \<le> dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

fun prefixes :: "'a list \<Rightarrow> 'a list list" where
  "prefixes [] = [[]]"
| "prefixes (x#xs) = (x#xs) # prefixes xs"

lemma closest_pair_combine_it'_conv_foldl:
  "closest_pair_combine_it' (c\<^sub>0, c\<^sub>1) ps = foldl fl (c\<^sub>0, c\<^sub>1) (prefixes ps)"
  by (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine_it'.induct) (auto simp: Let_def)

lemma closest_pair_combine_conv_foldr:
  assumes "n = length ps" "2 \<le> n"
  shows "closest_pair_combine ps = foldr fr (prefixes ps) (ps!(n-2), ps!(n-1))"
  using assms by (induction ps arbitrary: n rule: closest_pair_combine.induct) (auto simp: Let_def case_prod_unfold)

lemma fl_foldl_conv_fr_foldr:
  "fl (foldl fl (d\<^sub>0, d\<^sub>1) (prefixes ps)) [c\<^sub>0, c\<^sub>1] = fr [d\<^sub>0, d\<^sub>1] (foldr fr (prefixes ps) (c\<^sub>0, c\<^sub>1))"
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 d\<^sub>0 d\<^sub>1)
  case (Cons p ps)
  show ?case 
  proof (cases "ps = [p]")
    case True
    thus ?thesis
      by auto
  next
    case False
    let ?p' = "find_closest p (take 7 ps)"
    show ?thesis
    proof cases
      assume *: "fl (d\<^sub>0, d\<^sub>1) (p # ps) = (d\<^sub>0, d\<^sub>1)"
      hence "fl (foldl fl (d\<^sub>0, d\<^sub>1) (prefixes (p # ps))) [c\<^sub>0, c\<^sub>1] =
             fl (foldl fl (d\<^sub>0, d\<^sub>1) (prefixes ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = fr [d\<^sub>0, d\<^sub>1] (foldr fr (prefixes ps) (c\<^sub>0, c\<^sub>1))"
        using Cons.IH by simp
      also have "... = fr [d\<^sub>0, d\<^sub>1] (fr (p # ps) (foldr fr (prefixes ps) (c\<^sub>0, c\<^sub>1)))"
        using * by (cases ps) (auto simp: Let_def)
      also have "... = fr [d\<^sub>0, d\<^sub>1] (foldr fr (prefixes (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    next 
      assume "\<not> fl (d\<^sub>0, d\<^sub>1) (p # ps) = (d\<^sub>0, d\<^sub>1)"
      hence *: "fl (d\<^sub>0, d\<^sub>1) (p # ps) = (p, find_closest p (take 7 ps))"
        by (cases ps) (auto simp: Let_def)
      have "fl (foldl fl (d\<^sub>0, d\<^sub>1) (prefixes (p # ps))) [c\<^sub>0, c\<^sub>1] =
            fl (foldl fl (fl (d\<^sub>0, d\<^sub>1) (p # ps)) (prefixes ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = fl (foldl fl (p, ?p') (prefixes ps)) [c\<^sub>0, c\<^sub>1]"
        using * by (cases ps) (auto simp: Let_def)
      also have "... = fr [p, ?p'] (foldr fr (prefixes ps) (c\<^sub>0, c\<^sub>1))"
        using Cons by simp
      also have "... = fr [d\<^sub>0, d\<^sub>1] (fr (p # ps) (foldr fr (prefixes ps) (c\<^sub>0, c\<^sub>1)))"
        using * by (cases ps) (auto simp: Let_def)
      also have "... = fr [d\<^sub>0, d\<^sub>1] (foldr fr (prefixes (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    qed
  qed
qed simp

lemma prefixes_decomp_2:
  "n = length xs \<Longrightarrow> 2 \<le> n \<Longrightarrow> \<exists>ls. prefixes xs = ls @ [xs!(n-2), xs!(n-1)] # [xs!(n-1)] # [[]]"
proof (induction xs arbitrary: n)
  case (Cons x xs)
  show ?case
  proof (cases "n = 2")
    case True
    hence "prefixes (x#xs) = [[(x#xs)!(n - 2), (x#xs)!(n - 1)], [(x#xs)!(n - 1)], []]"
      using Cons.prems(1) by (cases xs) auto
    thus ?thesis
      by simp
  next
    case False
    hence *: "2 < n"
      using Cons.prems(2) by simp
    then obtain ls where "prefixes xs = ls @ [[xs!(n - 3), xs!(n - 2)], [xs!(n - 2)], []]"
      using Cons by fastforce
    thus ?thesis using *
      by (simp; simp add: numeral_2_eq_2)
  qed
qed simp

lemma foldl_fl_expand:
  assumes "ps = p\<^sub>0 # ps'" "n = length ps" "2 \<le> n"
  shows "foldl fl (p\<^sub>0, p\<^sub>1) (prefixes ps) = fl (foldl fl (p\<^sub>0, p\<^sub>1) (prefixes ps)) [ps!(n-2), ps!(n-1)]"
proof -
  let ?ps = "[ps!(n-2), ps!(n-1)]"
  let ?rs = "?ps # [ps!(n-1)] # [[]]"
  obtain ls where *: "prefixes ps = ls @ ?rs"
    using prefixes_decomp_2 assms by blast
  have "foldl fl (p\<^sub>0, p\<^sub>1) (prefixes ps) = fl (foldl fl (p\<^sub>0, p\<^sub>1) ls) ?ps"
    using * by simp
  also have "... = fl (fl (foldl fl (p\<^sub>0, p\<^sub>1) ls) ?ps) ?ps"
    by (cases ps) (auto simp: Let_def)
  also have "... = fl (foldl fl (p\<^sub>0, p\<^sub>1) (prefixes ps)) ?ps"
    using * by auto
  finally show ?thesis .
qed

lemma foldr_fr_expand:
  assumes "ps = p\<^sub>0 # ps'" "n = length ps" "2 \<le> n" "p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps')"
  shows "foldr fr (prefixes ps) (c\<^sub>0, c\<^sub>1) = fr [p\<^sub>0, p\<^sub>1] (foldr fr (prefixes ps) (c\<^sub>0, c\<^sub>1))"
proof -
  define c where *: "c = foldr fr (prefixes ps') (c\<^sub>0, c\<^sub>1)"
  show ?thesis
  proof (cases "dist (fst c) (snd c) \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    hence "fr ps c = (fst c, snd c)"
      using assms(1,4) by (cases ps') auto
    thus ?thesis
      using * True assms(1) by simp
  next
    case False
    hence "fr ps c = (p\<^sub>0, p\<^sub>1)"
      using assms by (cases ps') auto
    then show ?thesis
      using * assms(1) by simp
  qed
qed

lemma closest_pair_combine_conv_closest_pair_combine_it':
  assumes "ps = p\<^sub>0 # ps'" "n = length ps" "2 \<le> n" "p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps')"
  shows "closest_pair_combine ps = closest_pair_combine_it' (p\<^sub>0, p\<^sub>1) ps"
proof -
  have "closest_pair_combine ps = foldr fr (prefixes ps) (ps!(n-2), ps!(n-1))"
    using assms(2,3) closest_pair_combine_conv_foldr by blast
  also have "... = fr [p\<^sub>0, p\<^sub>1] (foldr fr (prefixes ps) (ps!(n-2), ps!(n-1)))"
    using assms foldr_fr_expand by blast
  also have "... = fl (foldl fl (p\<^sub>0, p\<^sub>1) (prefixes ps)) [ps!(n-2), ps!(n-1)]"
    using fl_foldl_conv_fr_foldr by presburger
  also have "... = foldl fl (p\<^sub>0, p\<^sub>1) (prefixes ps)"
    using assms foldl_fl_expand by presburger
  also have "... = closest_pair_combine_it' (p\<^sub>0, p\<^sub>1) ps"
    using closest_pair_combine_it'_conv_foldl by simp
  finally show ?thesis .
qed

lemma cases_list012:
  "P [] \<Longrightarrow> (\<And>x. P [x]) \<Longrightarrow> (\<And>x y xs. P (x # y # xs)) \<Longrightarrow> P xs"
  using induct_list012 by metis

lemma closest_pair_combine_conv_closest_pair_combine_it[code_unfold]:
  "closest_pair_combine ps = closest_pair_combine_it ps"
  using closest_pair_combine_conv_closest_pair_combine_it' by (cases rule: cases_list012) auto


subsection "dist"

definition dist_code :: "point \<Rightarrow> point \<Rightarrow> real" where
  "dist_code p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

lemma dist_point:
  "dist (p\<^sub>0 :: point) p\<^sub>1 = sqrt ((fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2)"
  by (simp add: dist_prod_def dist_real_def)

lemma lt_dist_conv_lt_sq_dist[code_unfold]:
  "dist a b < dist c d \<longleftrightarrow> dist_code a b < dist_code c d"
  using dist_point dist_code_def by simp

lemma le_dist_conv_le_sq_dist[code_unfold]:
  "dist a b \<le> dist c d \<longleftrightarrow> dist_code a b \<le> dist_code c d"
  using dist_point dist_code_def by simp

lemma dist_transform:
  "(l - dist (c\<^sub>0 :: point) c\<^sub>1 \<le> fst (p :: point) \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1) \<longleftrightarrow> 
   dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1"
proof -
  have "dist p (l, snd p) = \<bar>fst p - l\<bar>"
    using dist_point by simp
  thus ?thesis
    by linarith
qed


subsection "combine"

fun combine_code :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine_code (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ys' = filter (\<lambda>p. dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1) ys in
    if length ys' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_combine ys' in
      if dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1 then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

lemma combine_conv_combine_code[code_unfold]:
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = combine_code (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
  using dist_transform combine.simps by (auto simp: Let_def split: prod.splits)


subsection "Export Code"

declare [[code drop: "(<) :: real \<Rightarrow> real \<Rightarrow> bool" "(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool"]] 

export_code closest_pair in SML
  module_name Verified

end