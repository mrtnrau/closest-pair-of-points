theory Test
  imports "HOL-Analysis.Analysis"
begin

type_synonym point = "real * real"

definition dist :: "point \<Rightarrow> point \<Rightarrow> real" where
  "dist p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2"

fun find_closest :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest _ [] = undefined"
| "find_closest _ [p] = p"
| "find_closest p\<^sub>0 (p # ps) = (
    let c = find_closest p\<^sub>0 ps in
    if dist p\<^sub>0 p < dist p\<^sub>0 c then
      p
    else
      c
  )"

fun bf_closest_pair' :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair' _ [] = undefined"
| "bf_closest_pair' _ [_] = undefined"
| "bf_closest_pair' _ [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "bf_closest_pair' f (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = bf_closest_pair' f ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"


fun bf_closest_pair_it_rec' :: "(point list \<Rightarrow> point list) \<Rightarrow> (point * point) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it_rec' _ (c\<^sub>0, c\<^sub>1) [] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec' _ (c\<^sub>0, c\<^sub>1) [_] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec' f (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist c\<^sub>0 c\<^sub>1 < dist p\<^sub>0 p\<^sub>1 then
      bf_closest_pair_it_rec' f (c\<^sub>0, c\<^sub>1) ps
    else
      bf_closest_pair_it_rec' f (p\<^sub>0, p\<^sub>1) ps
  )"

fun bf_closest_pair_it' :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it' f (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec' f (p\<^sub>0, find_closest p\<^sub>0 (f (p\<^sub>1 # ps))) (p\<^sub>1 # ps)"
| "bf_closest_pair_it' _ _ = undefined"

fun fl :: "(point list \<Rightarrow> point list) \<Rightarrow> point * point \<Rightarrow> point list \<Rightarrow> point * point" where
  "fl _ c [] = (fst c, snd c)"
| "fl _ c [_] = (fst c, snd c)"
| "fl f c (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist (fst c) (snd c) < dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

fun fr :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> point * point \<Rightarrow> point * point" where
  "fr _ [] c = (fst c, snd c)"
| "fr _ [_] c = (fst c, snd c)"
| "fr f (p\<^sub>0 # ps) c = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist (fst c) (snd c) \<le> dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

fun lists :: "'a list \<Rightarrow> 'a list list" where
  "lists [] = [[]]"
| "lists (x#xs) = (x#xs) # lists xs"


lemma bf_closest_pair_it_rec'_conv_foldl:
  "bf_closest_pair_it_rec' f (c\<^sub>0, c\<^sub>1) ps = foldl (fl f) (c\<^sub>0, c\<^sub>1) (lists ps)"
  apply (induction f "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 rule: bf_closest_pair_it_rec'.induct)
  apply (auto simp add: Let_def)
  done

lemma bf_closest_pair'_conv_foldr:
  assumes "n = length ps" "2 \<le> n" "\<And>x. f [x] = [x]"
  shows "bf_closest_pair' f ps = foldr (fr f) (lists ps) (ps!(n-2), ps!(n-1))"
  using assms
  apply (induction f ps arbitrary: n rule: bf_closest_pair'.induct)
  apply (auto simp add: Let_def case_prod_unfold)
  done

lemma fl_foldl_conv_fr_foldr:
  assumes  "\<And>x. f [x] = [x]"
  shows "fl f (foldl (fl f) (c\<^sub>0', c\<^sub>1') (lists ps)) [c\<^sub>0, c\<^sub>1] = fr f [c\<^sub>0', c\<^sub>1'] (foldr (fr f) (lists ps) (c\<^sub>0, c\<^sub>1))"
  using assms
proof (induction ps arbitrary: c\<^sub>0' c\<^sub>1' c\<^sub>0 c\<^sub>1)
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
      assume *: "fl f (c\<^sub>0', c\<^sub>1') (p # ps) = (c\<^sub>0', c\<^sub>1')"
      hence "fl f (foldl (fl f) (c\<^sub>0', c\<^sub>1') (lists (p # ps))) [c\<^sub>0, c\<^sub>1] =
             fl f (foldl (fl f) (c\<^sub>0', c\<^sub>1') (lists ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = fr f [c\<^sub>0', c\<^sub>1'] (foldr (fr f) (lists ps) (c\<^sub>0, c\<^sub>1))"
        using Cons by simp
      also have "... = fr f [c\<^sub>0', c\<^sub>1'] ((fr f) (p # ps) (foldr (fr f) (lists ps) (c\<^sub>0, c\<^sub>1)))"
        using * Cons.prems by (cases ps) (auto simp add: Let_def)
      also have "... = fr f [c\<^sub>0', c\<^sub>1'] (foldr (fr f) (lists (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    next 
      assume ASM: "\<not> fl f (c\<^sub>0', c\<^sub>1') (p # ps) = (c\<^sub>0', c\<^sub>1')"
      hence *: "fl f (c\<^sub>0', c\<^sub>1') (p # ps) = (p, find_closest p (f ps))"
        by (cases ps) (auto simp add: Let_def)
      have "fl f (foldl (fl f) (c\<^sub>0', c\<^sub>1') (lists (p # ps))) [c\<^sub>0, c\<^sub>1] =
            fl f (foldl (fl f) (fl f (c\<^sub>0', c\<^sub>1') (p # ps)) (lists ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = fl f (foldl (fl f) (p, ?p') (lists ps)) [c\<^sub>0, c\<^sub>1]"
        using Cons.prems * by (cases ps) (auto simp add: Let_def)
      also have "... = fr f [p, ?p'] (foldr (fr f) (lists ps) (c\<^sub>0, c\<^sub>1))"
        using Cons by simp
      also have "... = fr f [c\<^sub>0', c\<^sub>1'] (fr f (p # ps) (foldr (fr f) (lists ps) (c\<^sub>0, c\<^sub>1)))"
        using Cons.prems * by (cases ps) (auto simp add: Let_def)
      also have "... = fr f [c\<^sub>0', c\<^sub>1'] (foldr (fr f) (lists (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    qed
  qed
qed simp

lemma lists_decomp_2:
  "n = length xs \<Longrightarrow> 2 \<le> n \<Longrightarrow> \<exists>ls. lists xs = ls @ [xs!(n-2), xs!(n-1)] # [xs!(n-1)] # [[]]"
proof (induction xs arbitrary: n)
  case (Cons x xs)
  show ?case
  proof (cases "n = 2")
    case True
    hence "lists (x#xs) = [[(x#xs)!(n - 2), (x#xs)!(n - 1)], [(x#xs)!(n - 1)], []]"
      using Cons.prems(1) by (cases xs) auto
    thus ?thesis
      by simp
  next
    case False
    hence *: "2 < n"
      using Cons.prems(2) by simp
    then obtain ls where "lists xs = ls @ [[xs!(n - 3), xs!(n - 2)], [xs!(n - 2)], []]"
      using Cons by fastforce
    thus ?thesis using *
      by (simp; simp add: numeral_2_eq_2)
  qed
qed simp

lemma foldl_fl_expand:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p (f ps)"
  shows "foldl (fl f) (p, p') (lists (p#ps)) =
         fl f (foldl (fl f) (p, p') (lists (p#ps))) [(p#ps)!(n-2), (p#ps)!(n-1)]"
  using assms
proof -
  let ?ps = "p # ps"
  let ?psn = "[?ps!(n-2), ?ps!(n-1)]"
  let ?rs = "?psn # [?ps!(n-1)] # [[]]"
  obtain ls where *: "lists ?ps = ls @ ?psn # [?ps!(n-1)] # [[]]"
    using lists_decomp_2 assms by blast
  have "fl f (foldl (fl f) (p, p') (lists ?ps)) ?psn =
        fl f (foldl (fl f) (foldl (fl f) (p, p') ls) ?rs) ?psn"
    using * by simp
  also have "... =  fl f (foldl (fl f) (foldl (fl f) (p, p') ls) [?psn]) ?psn"
    by simp
  also have "... = fl f (fl f (foldl (fl f) (p, p') ls) ?psn) ?psn"
    by simp
  also have "... = fl f (foldl (fl f) (p, p') ls) ?psn"
    by (cases ?ps) (auto simp add: Let_def)
  also have "... = foldl (fl f) (foldl (fl f) (p, p') ls) [?psn]"
    by simp
  also have "... = foldl (fl f) (foldl (fl f) (p, p') ls) ?rs"
    by simp
  also have "... = foldl (fl f) (p, p') (lists ?ps)"
    using * by simp
  finally have "fl f (foldl (fl f) (p, p') (lists ?ps)) ?psn = foldl (fl f) (p, p') (lists ?ps)" .
  thus ?thesis
    by simp
qed

lemma foldr_fr_expand:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p (f ps)" "\<And>x. f [x] = [x]"
  shows "foldr (fr f) (lists (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)) =
         fr f [p, p'] (foldr (fr f) (lists (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)))"
proof -
  let ?ps = "p # ps"
  let ?psn = "(?ps!(n-2), ?ps!(n-1))"
  define RS where "RS = foldr (fr f) (lists ps) ?psn"
  have *: "fr f [p, p'] (foldr (fr f) (lists ?ps) ?psn) = fr f [p, p'] (foldr (fr f) [?ps] RS)"
    by (simp add: RS_def)
  have #: "foldr (fr f) (lists ?ps) ?psn = foldr (fr f) [?ps] RS"
    by (simp add: RS_def)
  show ?thesis
  proof (cases "dist (fst RS) (snd RS) \<le> dist p p'")
    case True
    have "0 < length ?ps"
      using assms(1,2) by simp
    hence "fr f ?ps RS = (fst RS, snd RS)"
      using assms(3) True by (cases ps) auto
    hence "foldr (fr f) [?ps] RS = (fst RS, snd RS)"
      by simp
    hence "foldr (fr f) (lists ?ps) ?psn = (fst RS, snd RS)"
      using # by simp
    moreover have "fr f [p, p'] (fst RS, snd RS) = (fst RS, snd RS)"
      using True assms(4) by simp
    ultimately show ?thesis
      by simp
  next
    case False
    have "0 < length ps"
      using assms(1,2) by (cases ps) auto
    hence "fr f ?ps RS = (p, p')"
      using False assms(3) by (cases ps) auto
    then show ?thesis
      using * # assms(4) by simp
  qed
qed

lemma bf_closest_pair'_conv_bf_closest_pair_it_rec':
  assumes "n = length (p#ps)" "2 \<le> n" "p' = find_closest p (f ps)" "\<And>x. f [x] = [x]"
  shows "bf_closest_pair' f (p#ps) = bf_closest_pair_it_rec' f (p, p') (p#ps)"
proof -
  let ?ps = "p # ps"
  have "bf_closest_pair' f ?ps = foldr (fr f) (lists ?ps) (?ps!(n-2), ?ps!(n-1))"
    using assms bf_closest_pair'_conv_foldr by blast
  also have "... = fr f [p, p'] (foldr (fr f) (lists ?ps) (?ps!(n-2), ?ps!(n-1)))"
    using assms foldr_fr_expand by blast
  also have "... = fl f (foldl (fl f) (p, p') (lists ?ps)) [?ps!(n-2), ?ps!(n-1)]"
    using fl_foldl_conv_fr_foldr assms(4) by presburger
  also have "... = foldl (fl f) (p, p') (lists ?ps)"
    using assms foldl_fl_expand by presburger
  also have "... = bf_closest_pair_it_rec' f (p, p') ?ps"
    using bf_closest_pair_it_rec'_conv_foldl by simp
  finally show ?thesis .
qed


lemma cases_list012:
  "P [] \<Longrightarrow> (\<And>x. P [x]) \<Longrightarrow> (\<And>x y xs. P (x # y # xs)) \<Longrightarrow> P xs"
  using induct_list012 by metis

lemma bf_closest_pair'_conv_bf_closest_pair_it':
  "(\<And>x. f [x] = [x]) \<Longrightarrow> bf_closest_pair' f ps = bf_closest_pair_it' f ps"
  using bf_closest_pair'_conv_bf_closest_pair_it_rec' by (cases rule: cases_list012) auto


definition bf_closest_pair :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair ps = bf_closest_pair' (\<lambda>ps. ps) ps"

definition bf_closest_pair_it :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it ps = bf_closest_pair_it' (\<lambda>ps. ps) ps"

lemma bf_closest_pair_conv_bf_closest_pair_it[code_unfold]:
  "bf_closest_pair ps = bf_closest_pair_it ps"
  unfolding bf_closest_pair_def bf_closest_pair_it_def
  using bf_closest_pair'_conv_bf_closest_pair_it' by simp


definition closest_pair_7 :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_7 ps = bf_closest_pair' (take 7) ps"

definition closest_pair_7_it :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_7_it ps = bf_closest_pair_it' (take 7) ps"

lemma closest_pair_7_conv_closest_pair_7_it[code_unfold]:
  "closest_pair_7 ps = closest_pair_7_it ps"
  unfolding closest_pair_7_def closest_pair_7_it_def
  using bf_closest_pair'_conv_bf_closest_pair_it' by simp


subsection "Alternatives"

text \<open>
lemma
  assumes @{term "0 < length ps"}
  shows @{term "bf_closest_pair' f (p\<^sub>0 # ps) = bf_closest_pair_it_rec' f (p\<^sub>0, find_closest p\<^sub>0 (f ps)) ps"}
  using assms
  apply (induction f @{term "(p\<^sub>0, find_closest p\<^sub>0 ps)"} ps arbitrary: \<open>p\<^sub>0\<close> rule: bf_closest_pair_it_rec'.induct)
  oops

lemma
  @{term "bf_closest_pair' f (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec' f (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # p\<^sub>1 # ps)"}
  apply (induction f @{term "(p\<^sub>0, p\<^sub>1)"} ps arbitrary: \<open>p\<^sub>0\<close> \<open>p\<^sub>1\<close> rule: bf_closest_pair_it_rec'.induct)
  oops
\<close>

end