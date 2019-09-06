theory Test
  imports "HOL-Analysis.Analysis"
begin

type_synonym point = "real * real"




fun find_closest :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest p\<^sub>0 [] = undefined"
| "find_closest p\<^sub>0 [p] = p"
| "find_closest p\<^sub>0 (p # ps) = (
    let c = find_closest p\<^sub>0 ps in
    if dist p\<^sub>0 p < dist p\<^sub>0 c then
      p
    else
      c
  )"

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

lemma closest_pair_combine_conv_closest_pair_combine_it:
  "closest_pair_combine ps = closest_pair_combine_it ps"
  using closest_pair_combine_conv_closest_pair_combine_it' by (cases rule: cases_list012) auto

end