theory Closest_Pair_Code
  imports
    Closest_Pair
    (* "HOL-Library.Code_Real_Approx_By_Float" *)
    "HOL-Library.Code_Target_Numeral"
begin

section "Closest Pair Of Points Without Stackoverflow"

subsection "length"

fun length_it_rec :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "length_it_rec acc [] = acc"
| "length_it_rec acc (x#xs) = length_it_rec (acc+1) xs"

definition length_it :: "'a list \<Rightarrow> nat" where
  "length_it xs = length_it_rec 0 xs"

lemma length_conv_length_it_rec:
  "length xs + acc = length_it_rec acc xs"
  by (induction acc xs rule: length_it_rec.induct) auto

lemma length_conv_length_it[code_unfold]:
  "length xs = length_it xs"
  unfolding length_it_def using length_conv_length_it_rec add_0_right by metis


subsection "filter"

fun filter_it_rec :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_it_rec acc P [] = rev acc"
| "filter_it_rec acc P (x#xs) = (
    if P x then
      filter_it_rec (x#acc) P xs
    else
      filter_it_rec acc P xs
  )"

definition filter_it :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_it P xs = filter_it_rec [] P xs"

lemma filter_conv_filter_it_rec:
  "rev acc @ filter P xs = filter_it_rec acc P xs"
  by (induction acc P xs rule: filter_it_rec.induct) auto

lemma filter_conv_filter_it[code_unfold]:
  "filter P xs = filter_it P xs"
  unfolding filter_it_def using filter_conv_filter_it_rec append_Nil rev.simps(1) by metis


subsection "rev"

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


subsection "split_at"

fun split_at_it_rec :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at_it_rec acc n [] = (rev acc, [])"
| "split_at_it_rec acc n (x#xs) = (
    case n of
      0 \<Rightarrow> (rev acc, x#xs)
    | Suc m \<Rightarrow> split_at_it_rec (x#acc) m xs
  )"

definition split_at_it :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at_it n xs = split_at_it_rec [] n xs"

lemma split_at_conv_split_at_it_rec:
  assumes "(ts, ds) = split_at n xs" "(tsi, dsi) = split_at_it_rec acc n xs"
  shows "rev acc @ ts = tsi"
    and "ds = dsi"
  using assms
  apply (induction acc n xs arbitrary: ts rule: split_at_it_rec.induct)
  apply (auto simp: split_at.simps split: prod.splits nat.splits)
  done

lemma split_at_conv_split_at_it_prod:
  assumes "(ts, ds) = split_at n xs" "(ts', ds') = split_at_it n xs"
  shows "(ts, ds) = (ts', ds')"
  using assms unfolding split_at_it_def 
  using split_at_conv_split_at_it_rec rev.simps(1) append_Nil by fast+

lemma split_at_conv_split_at_it[code_unfold]:
  "split_at n xs = split_at_it n xs"
  using split_at_conv_split_at_it_prod surj_pair by metis

subsection "merge"

lemma merge_xs_Nil[simp]:
  "merge f xs [] = xs"
  by (cases xs) auto

fun merge_it_rec :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge_it_rec f acc [] [] = rev acc"
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
  "find_closest_it_rec p c\<^sub>0 [] = c\<^sub>0"
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


subsection "gen_closest_pair"

fun gen_closest_pair_it_rec :: "(point list \<Rightarrow> point list) \<Rightarrow> (point * point) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "gen_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) [] = (c\<^sub>0, c\<^sub>1)"
| "gen_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) [p\<^sub>0] = (c\<^sub>0, c\<^sub>1)"
| "gen_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist c\<^sub>0 c\<^sub>1 < dist p\<^sub>0 p\<^sub>1 then
      gen_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) ps
    else
      gen_closest_pair_it_rec f (p\<^sub>0, p\<^sub>1) ps
  )"

fun gen_closest_pair_it :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "gen_closest_pair_it f (p\<^sub>0 # p\<^sub>1 # ps) = gen_closest_pair_it_rec f (p\<^sub>0, find_closest p\<^sub>0 (f (p\<^sub>1 # ps))) (p\<^sub>1 # ps)"
| "gen_closest_pair_it _ _ = undefined"

fun fl :: "(point list \<Rightarrow> point list) \<Rightarrow> point * point \<Rightarrow> point list \<Rightarrow> point * point" where
  "fl f c [] = (fst c, snd c)"
| "fl f c [p\<^sub>0] = (fst c, snd c)"
| "fl f c (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist (fst c) (snd c) < dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

fun fr :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> point * point \<Rightarrow> point * point" where
  "fr f [] c = (fst c, snd c)"
| "fr f [p\<^sub>0] c = (fst c, snd c)"
| "fr f (p\<^sub>0 # ps) c = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist (fst c) (snd c) \<le> dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

fun prefixes :: "'a list \<Rightarrow> 'a list list" where
  "prefixes [] = [[]]"
| "prefixes (x#xs) = (x#xs) # prefixes xs"


lemma gen_closest_pair_it_rec_conv_foldl:
  "gen_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) ps = foldl (fl f) (c\<^sub>0, c\<^sub>1) (prefixes ps)"
  apply (induction f "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 rule: gen_closest_pair_it_rec.induct)
  apply (auto simp add: Let_def)
  done

lemma gen_closest_pair_conv_foldr:
  assumes "n = length ps" "2 \<le> n" "\<And>x. f [x] = [x]"
  shows "gen_closest_pair f ps = foldr (fr f) (prefixes ps) (ps!(n-2), ps!(n-1))"
  using assms
  apply (induction f ps arbitrary: n rule: gen_closest_pair.induct)
  apply (auto simp add: Let_def case_prod_unfold)
  done

lemma fl_foldl_conv_fr_foldr:
  assumes  "\<And>x. f [x] = [x]"
  shows "fl f (foldl (fl f) (d\<^sub>0, d\<^sub>1) (prefixes ps)) [c\<^sub>0, c\<^sub>1] =
         fr f [d\<^sub>0, d\<^sub>1] (foldr (fr f) (prefixes ps) (c\<^sub>0, c\<^sub>1))"
  using assms
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 d\<^sub>0 d\<^sub>1)
  case (Cons p ps)
  show ?case 
  proof (cases "ps = [p]")
    case True
    thus ?thesis
      using Cons.prems by auto
  next
    case False
    let ?p' = "find_closest p (f ps)"
    show ?thesis
    proof cases
      assume *: "fl f (d\<^sub>0, d\<^sub>1) (p # ps) = (d\<^sub>0, d\<^sub>1)"
      hence "fl f (foldl (fl f) (d\<^sub>0, d\<^sub>1) (prefixes (p # ps))) [c\<^sub>0, c\<^sub>1] =
             fl f (foldl (fl f) (d\<^sub>0, d\<^sub>1) (prefixes ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = fr f [d\<^sub>0, d\<^sub>1] (foldr (fr f) (prefixes ps) (c\<^sub>0, c\<^sub>1))"
        using Cons by simp
      also have "... = fr f [d\<^sub>0, d\<^sub>1] ((fr f) (p # ps) (foldr (fr f) (prefixes ps) (c\<^sub>0, c\<^sub>1)))"
        using * Cons.prems by (cases ps) (auto simp add: Let_def)
      also have "... = fr f [d\<^sub>0, d\<^sub>1] (foldr (fr f) (prefixes (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    next 
      assume ASM: "\<not> fl f (d\<^sub>0, d\<^sub>1) (p # ps) = (d\<^sub>0, d\<^sub>1)"
      hence *: "fl f (d\<^sub>0, d\<^sub>1) (p # ps) = (p, find_closest p (f ps))"
        by (cases ps) (auto simp add: Let_def)
      have "fl f (foldl (fl f) (d\<^sub>0, d\<^sub>1) (prefixes (p # ps))) [c\<^sub>0, c\<^sub>1] =
            fl f (foldl (fl f) (fl f (d\<^sub>0, d\<^sub>1) (p # ps)) (prefixes ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = fl f (foldl (fl f) (p, ?p') (prefixes ps)) [c\<^sub>0, c\<^sub>1]"
        using Cons.prems * by (cases ps) (auto simp add: Let_def)
      also have "... = fr f [p, ?p'] (foldr (fr f) (prefixes ps) (c\<^sub>0, c\<^sub>1))"
        using Cons by simp
      also have "... = fr f [d\<^sub>0, d\<^sub>1] (fr f (p # ps) (foldr (fr f) (prefixes ps) (c\<^sub>0, c\<^sub>1)))"
        using Cons.prems * by (cases ps) (auto simp add: Let_def)
      also have "... = fr f [d\<^sub>0, d\<^sub>1] (foldr (fr f) (prefixes (p # ps)) (c\<^sub>0, c\<^sub>1))"
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
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p (f ps)"
  shows "foldl (fl f) (p, p') (prefixes (p#ps)) =
         fl f (foldl (fl f) (p, p') (prefixes (p#ps))) [(p#ps)!(n-2), (p#ps)!(n-1)]"
proof -
  let ?ps = "p # ps"
  let ?psn = "[?ps!(n-2), ?ps!(n-1)]"
  let ?rs = "?psn # [?ps!(n-1)] # [[]]"
  obtain ls where *: "prefixes ?ps = ls @ ?rs"
    using prefixes_decomp_2 assms by blast
  have "foldl (fl f) (p, p') (prefixes ?ps) = fl f (foldl (fl f) (p, p') ls) ?psn"
    using * by simp
  also have "... = fl f (fl f (foldl (fl f) (p, p') ls) ?psn) ?psn"
    by (cases ?ps) (auto simp add: Let_def)
  also have "... = fl f (foldl (fl f) (p, p') (prefixes ?ps)) ?psn"
    using * by auto
  finally show ?thesis .
qed

lemma foldr_fr_expand:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p (f ps)" "\<And>x. f [x] = [x]"
  shows "foldr (fr f) (prefixes (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)) =
         fr f [p, p'] (foldr (fr f) (prefixes (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)))"
proof -
  define RS where "RS = foldr (fr f) (prefixes ps) ((p#ps)!(n-2), (p#ps)!(n-1))"
  show ?thesis
  proof (cases "dist (fst RS) (snd RS) \<le> dist p p'")
    case True
    have "0 < length (p#ps)"
      by simp
    hence "fr f (p#ps) RS = (fst RS, snd RS)"
      using assms(3) True by (cases ps) auto
    thus ?thesis
      using RS_def assms(4) True by simp
  next
    case False
    have "0 < length ps"
      using assms(1,2) by (cases ps) auto
    hence "fr f (p#ps) RS = (p, p')"
      using False assms(3) by (cases ps) auto
    then show ?thesis
      using RS_def assms(4) by simp
  qed
qed

lemma gen_closest_pair_conv_gen_closest_pair_it_rec:
  assumes "n = length (p#ps)" "2 \<le> n" "p' = find_closest p (f ps)" "\<And>x. f [x] = [x]"
  shows "gen_closest_pair f (p#ps) = gen_closest_pair_it_rec f (p, p') (p#ps)"
proof -
  let ?ps = "p # ps"
  have "gen_closest_pair f ?ps = foldr (fr f) (prefixes ?ps) (?ps!(n-2), ?ps!(n-1))"
    using assms gen_closest_pair_conv_foldr by blast
  also have "... = fr f [p, p'] (foldr (fr f) (prefixes ?ps) (?ps!(n-2), ?ps!(n-1)))"
    using assms foldr_fr_expand by blast
  also have "... = fl f (foldl (fl f) (p, p') (prefixes ?ps)) [?ps!(n-2), ?ps!(n-1)]"
    using fl_foldl_conv_fr_foldr assms(4) by presburger
  also have "... = foldl (fl f) (p, p') (prefixes ?ps)"
    using assms foldl_fl_expand by presburger
  also have "... = gen_closest_pair_it_rec f (p, p') ?ps"
    using gen_closest_pair_it_rec_conv_foldl by simp
  finally show ?thesis .
qed


lemma cases_list012:
  "P [] \<Longrightarrow> (\<And>x. P [x]) \<Longrightarrow> (\<And>x y xs. P (x # y # xs)) \<Longrightarrow> P xs"
  using induct_list012 by metis

lemma gen_closest_pair_conv_gen_closest_pair_it:
  "(\<And>x. f [x] = [x]) \<Longrightarrow> gen_closest_pair f ps = gen_closest_pair_it f ps"
  using gen_closest_pair_conv_gen_closest_pair_it_rec by (cases rule: cases_list012) auto


subsection "bf_closest_pair"

definition bf_closest_pair_it :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it ps = gen_closest_pair_it (\<lambda>ps. ps) ps"

lemma bf_closest_pair_conv_bf_closest_pair_it[code_unfold]:
  "bf_closest_pair ps = bf_closest_pair_it ps"
  unfolding bf_closest_pair_def bf_closest_pair_it_def
  using gen_closest_pair_conv_gen_closest_pair_it by simp


subsection "closest_pair_7"

definition closest_pair_7_it :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_7_it ps = gen_closest_pair_it (take 7) ps"

lemma closest_pair_7_conv_closest_pair_7_it[code_unfold]:
  "closest_pair_7 ps = closest_pair_7_it ps"
  unfolding closest_pair_7_def closest_pair_7_it_def
  using gen_closest_pair_conv_gen_closest_pair_it by simp


subsection "dist"

definition dist_code :: "point \<Rightarrow> point \<Rightarrow> real" where
  "dist_code p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

lemma dist_point:
  "dist (p\<^sub>0 :: point) p\<^sub>1 = sqrt ((fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2)"
  by (simp add: dist_prod_def dist_real_def)

lemma dist_transform:
  "(l - dist (c\<^sub>0 :: point) c\<^sub>1 \<le> fst (p :: point) \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1) \<longleftrightarrow> 
   dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1"
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