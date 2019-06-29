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

fun bf_closest_pair :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair _ [] = undefined"
| "bf_closest_pair _ [_] = undefined"
| "bf_closest_pair _ [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "bf_closest_pair f (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = bf_closest_pair f ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

fun bf_closest_pair_it_rec :: "(point list \<Rightarrow> point list) \<Rightarrow> (point * point) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it_rec _ (c\<^sub>0, c\<^sub>1) [] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec _ (c\<^sub>0, c\<^sub>1) [_] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist c\<^sub>0 c\<^sub>1 < dist p\<^sub>0 p\<^sub>1 then
      bf_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) ps
    else
      bf_closest_pair_it_rec f (p\<^sub>0, p\<^sub>1) ps
  )"

fun bf_closest_pair_it :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it f (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec f (p\<^sub>0, find_closest p\<^sub>0 (f (p\<^sub>1 # ps))) (p\<^sub>1 # ps)"
| "bf_closest_pair_it _ _ = undefined"




fun bf :: "(point list \<Rightarrow> point list) \<Rightarrow> point * point \<Rightarrow> point list \<Rightarrow> point * point" where
  "bf _ c [] = (fst c, snd c)"
| "bf _ c [_] = (fst c, snd c)"
| "bf f c (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist (fst c) (snd c) < dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

lemma cases_list012:
  assumes "P []" "\<And>x. P [x]" "\<And>x y xs. P (x # y # xs)"
  shows "P xs"
  using assms induct_list012 by metis

lemma Z: 
  assumes "\<not> bf f c (p # ps) = c"
  shows "bf f c (p # ps) = (p, find_closest p (f ps))"
  using assms
  apply (cases ps)
   apply (auto simp add: Let_def)
  done

fun bf' :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> point * point \<Rightarrow> point * point" where
  "bf' _ [] c = (fst c, snd c)"
| "bf' _ [_] c = (fst c, snd c)"
| "bf' f (p\<^sub>0 # ps) c = (
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    if dist (fst c) (snd c) \<le> dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

lemma X:
  assumes "0 < length ps" "dist (fst c) (snd c) \<le> dist p (find_closest p (f ps))"
  shows "bf' f (p # ps) c = c"
  using assms by (cases ps) (auto simp add: Let_def)

lemma Y:
  assumes "0 < length ps" "\<not> dist (fst c) (snd c) \<le> dist p (find_closest p (f ps))"
  shows "bf' f (p # ps) c = (p, find_closest p (f ps))"
  using assms by (cases ps) (auto simp add: Let_def)

fun lists :: "'a list \<Rightarrow> 'a list list" where
  "lists [] = [[]]"
| "lists (x#xs) = (x#xs) # lists xs"

lemma bf_foldl:
  "bf_closest_pair_it_rec f (c\<^sub>0, c\<^sub>1) ps = foldl (bf f) (c\<^sub>0, c\<^sub>1) (lists ps)"
  apply (induction f "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 rule: bf_closest_pair_it_rec.induct)
    apply (auto simp add: Let_def)
  done

lemma bf_foldr:
  assumes "n = length ps" "2 \<le> n" "\<And>x. f [x] = [x]"
  shows "bf_closest_pair f ps = foldr (bf' f) (lists ps) (ps!(n-2), ps!(n-1))"
  using assms
  apply (induction f ps arbitrary: n rule: bf_closest_pair.induct)
     apply (auto simp add: Let_def case_prod_unfold)
  done

lemma AUX:
  assumes  "\<And>x. f [x] = [x]"
  shows "bf f (foldl (bf f) (c\<^sub>0', c\<^sub>1') (lists ps)) [c\<^sub>0, c\<^sub>1] = bf' f [c\<^sub>0', c\<^sub>1'] (foldr (bf' f) (lists ps) (c\<^sub>0, c\<^sub>1))"
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
      assume *: "bf f (c\<^sub>0', c\<^sub>1') (p # ps) = (c\<^sub>0', c\<^sub>1')"
      hence "bf f (foldl (bf f) (c\<^sub>0', c\<^sub>1') (lists (p # ps))) [c\<^sub>0, c\<^sub>1] = bf f (foldl (bf f) (c\<^sub>0', c\<^sub>1') (lists ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = bf' f [c\<^sub>0', c\<^sub>1'] (foldr (bf' f) (lists ps) (c\<^sub>0, c\<^sub>1))"
        using Cons by simp
      also have "... = bf' f [c\<^sub>0', c\<^sub>1'] ((bf' f) (p # ps) (foldr (bf' f) (lists ps) (c\<^sub>0, c\<^sub>1)))"
        using * Cons.prems by (cases ps) (auto simp add: Let_def)
      also have "... = bf' f [c\<^sub>0', c\<^sub>1'] (foldr (bf' f) (lists (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    next 
      assume ASM: "\<not> bf f (c\<^sub>0', c\<^sub>1') (p # ps) = (c\<^sub>0', c\<^sub>1')"
      hence *: "bf f (c\<^sub>0', c\<^sub>1') (p # ps) = (p, find_closest p (f ps))"
        using Z by simp
      hence "bf f (foldl (bf f) (c\<^sub>0', c\<^sub>1') (lists (p # ps))) [c\<^sub>0, c\<^sub>1] = bf f (foldl (bf f) (bf f (c\<^sub>0', c\<^sub>1') (p # ps)) (lists ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = bf f (foldl (bf f) (p, ?p') (lists ps)) [c\<^sub>0, c\<^sub>1]"
        using Cons.prems * by (cases ps) (auto simp add: Let_def)
      also have "... = bf' f [p, ?p'] (foldr (bf' f) (lists ps) (c\<^sub>0, c\<^sub>1))"
        using Cons by simp
      also have "... = bf' f [c\<^sub>0', c\<^sub>1'] (bf' f (p # ps) (foldr (bf' f) (lists ps) (c\<^sub>0, c\<^sub>1)))"
        using Cons.prems * by (cases ps) (auto simp add: Let_def)
      also have "... = bf' f [c\<^sub>0', c\<^sub>1'] (foldr (bf' f) (lists (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    qed
  qed
qed simp

lemma lists_decomp_2:
  "n = length xs \<Longrightarrow> 2 \<le> n \<Longrightarrow> \<exists>ls. lists xs = ls @ [xs!(n-2), xs!(n-1)] # [xs!(n-1)] # [[]]"
proof (induction xs arbitrary: n)
  case (Cons x xs)
  then show ?case
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

lemma BUX:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p (f ps)"
  shows "foldl (bf f) (p, p') (lists (p#ps)) = bf f (foldl (bf f) (p, p') (lists (p#ps))) [(p#ps)!(n-2), (p#ps)!(n-1)]"
  using assms
proof -
  let ?ps = "p # ps"
  obtain ls where *: "lists ?ps = ls @ [?ps!(n-2), ?ps!(n-1)] # [?ps!(n-1)] # [[]]"
    using lists_decomp_2 assms by blast
  let ?rs = "[?ps!(n-2), ?ps!(n-1)] # [?ps!(n-1)] # [[]]"
  have "bf f (foldl (bf f) (p, p') (lists ?ps)) [?ps!(n-2), ?ps!(n-1)] = bf f (foldl (bf f) (foldl (bf f) (p, p') ls) ?rs) [?ps!(n-2), ?ps!(n-1)]"
    using * by simp
  also have "... =  bf f (foldl (bf f) (foldl (bf f) (p, p') ls) [[?ps!(n-2), ?ps!(n-1)]]) [?ps!(n-2), ?ps!(n-1)]"
    by simp
  also have "... = bf f (bf f (foldl (bf f) (p, p') ls) [?ps!(n-2), ?ps!(n-1)]) [?ps!(n-2), ?ps!(n-1)]"
    by simp
  also have "... = bf f (foldl (bf f) (p, p') ls) [?ps!(n-2), ?ps!(n-1)]"
    by (cases ?ps) (auto simp add: Let_def)
  also have "... = foldl (bf f) (foldl (bf f) (p, p') ls) [[?ps!(n-2), ?ps!(n-1)]]"
    by simp
  also have "... = foldl (bf f) (foldl (bf f) (p, p') ls) ?rs"
    by simp
  also have "... = foldl (bf f) (p, p') (lists ?ps)"
    using * by simp
  finally have "bf f (foldl (bf f) (p, p') (lists ?ps)) [?ps!(n-2), ?ps!(n-1)] = foldl (bf f) (p, p') (lists ?ps)" .
  thus ?thesis
    by simp
qed

lemma Q:
  assumes "dist (fst RS) (snd RS) \<le> dist p p'" "\<And>x. f [x] = [x]"
  shows "bf' f [p, p'] (fst RS, snd RS) = (fst RS, snd RS)"
  using assms by (auto simp add: Let_def)

lemma CUX:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p (f ps)" "\<And>x. f [x] = [x]"
  shows "foldr (bf' f) (lists (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)) = bf' f [p, p'] (foldr (bf' f) (lists (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)))"
proof -
  let ?ps = "p # ps"
  define RS where "RS = foldr (bf' f) (lists ps) (?ps!(n-2), ?ps!(n-1))"
  have *: "bf' f [p, p'] (foldr (bf' f) (lists ?ps) (?ps!(n-2), ?ps!(n-1))) = bf' f [p, p'] (foldr (bf' f) [?ps] RS)"
    by (simp add: RS_def)
  have #: "foldr (bf' f) (lists ?ps) (?ps!(n-2), ?ps!(n-1)) = foldr (bf' f) [?ps] RS"
    by (simp add: RS_def)
  show ?thesis
  proof (cases "dist (fst RS) (snd RS) \<le> dist p p'")
    case True
    have "0 < length ?ps"
      using assms(1,2) by simp
    hence "bf' f ?ps RS = (fst RS, snd RS)"
      using assms(3) True X[of ps RS p] by fastforce
    hence x: "foldr (bf' f) [?ps] RS = (fst RS, snd RS)"
      by simp
    hence "foldr (bf' f) (lists ?ps) (?ps!(n-2), ?ps!(n-1)) = (fst RS, snd RS)"
      using # by simp
    moreover have "bf' f [p, p'] (fst RS, snd RS) = (fst RS, snd RS)"
      using True assms(4) by simp
    ultimately show ?thesis
      by simp
  next
    case False
    have "0 < length ps"
      using assms(1,2) by (metis One_nat_def gr0I le_numeral_extra(4) length_Cons not_less_eq_eq numeral_2_eq_2)
    hence "bf' f ?ps RS = (p, p')"
      using False assms(3) Y[of ps RS p] by simp
    then show ?thesis
      using * # assms(4) by simp
  qed
qed

lemma DUX:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p (f ps)" "\<And>x. f [x] = [x]"
  shows "bf_closest_pair f (p#ps) = bf_closest_pair_it_rec f (p, p') (p#ps)"
proof -
  let ?ps = "p # ps"
  have "bf_closest_pair f ?ps = foldr (bf' f) (lists ?ps) (?ps!(n-2), ?ps!(n-1))"
    using assms bf_foldr by blast
  also have "... = bf' f [p, p'] (foldr (bf' f) (lists ?ps) (?ps!(n-2), ?ps!(n-1)))"
    using assms CUX by blast
  also have "... = bf f (foldl (bf f) (p, p') (lists ?ps)) [?ps!(n-2), ?ps!(n-1)]"
    using AUX assms(4) by presburger
  also have "... = foldl (bf f) (p, p') (lists ?ps)"
    using assms BUX by presburger
  also have "... = bf_closest_pair_it_rec f (p, p') ?ps"
    using bf_foldl by simp
  finally show ?thesis .
qed

lemma bf_closest_pair_conv_bf_closest_pair_it[code_unfold]:
  assumes "\<And>x. f [x] = [x]"
  shows "bf_closest_pair f ps = bf_closest_pair_it f ps"
  using assms DUX by (cases rule: cases_list012) auto


subsection "Alternatives"

lemma
  assumes "0 < length ps"
  shows "bf_closest_pair f (p\<^sub>0 # ps) = bf_closest_pair_it_rec f (p\<^sub>0, find_closest p\<^sub>0 (f ps)) ps"
  using assms
  apply (induction f "(p\<^sub>0, find_closest p\<^sub>0 ps)" ps arbitrary: p\<^sub>0 rule: bf_closest_pair_it_rec.induct)
  sorry

lemma
  "bf_closest_pair f (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec f (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # p\<^sub>1 # ps)"
  apply (induction f "(p\<^sub>0, p\<^sub>1)" ps arbitrary: p\<^sub>0 p\<^sub>1 rule: bf_closest_pair_it_rec.induct)
  sorry

end