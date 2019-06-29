theory Test
  imports "HOL-Analysis.Analysis"
begin

type_synonym point = "(real * real)"

definition dist :: "point \<Rightarrow> point \<Rightarrow> real" where
  "dist p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

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

fun bf_closest_pair :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair [] = undefined"
| "bf_closest_pair [_] = undefined"
| "bf_closest_pair [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "bf_closest_pair (p\<^sub>0 # ps) = (
    let c = bf_closest_pair ps in
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist (fst c) (snd c) \<le> dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

fun bf_closest_pair_it_rec :: "(point * point) \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) [] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) [_] = (c\<^sub>0, c\<^sub>1)"
| "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 < dist p\<^sub>0 p\<^sub>1 then
      bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) ps
    else
      bf_closest_pair_it_rec (p\<^sub>0, p\<^sub>1) ps
  )"

fun bf_closest_pair_it :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair_it (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec (p\<^sub>0, find_closest p\<^sub>0 (p\<^sub>1 # ps)) (p\<^sub>0 # p\<^sub>1 # ps)"
| "bf_closest_pair_it _ = undefined"




fun bf :: "point * point \<Rightarrow> point list \<Rightarrow> point * point" where
  "bf c [] = (fst c, snd c)"
| "bf c [_] = (fst c, snd c)"
| "bf c (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist (fst c) (snd c) < dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

fun bf' :: "point list \<Rightarrow> point * point \<Rightarrow> point * point" where
  "bf' [] c = (fst c, snd c)"
| "bf' [_] c = (fst c, snd c)"
| "bf' (p\<^sub>0 # ps) c = (
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist (fst c) (snd c) \<le> dist p\<^sub>0 p\<^sub>1 then
      c
    else
      (p\<^sub>0, p\<^sub>1)
  )"

lemma X:
  assumes "0 < length ps" "dist (fst c) (snd c) \<le> dist p (find_closest p ps)"
  shows "bf' (p # ps) c = c"
  using assms by (cases ps) (auto simp add: Let_def)

lemma Y:
  assumes "0 < length ps" "\<not> dist (fst c) (snd c) \<le> dist p (find_closest p ps)"
  shows "bf' (p # ps) c = (p, find_closest p ps)"
  using assms by (cases ps) (auto simp add: Let_def)

fun lists :: "'a list \<Rightarrow> 'a list list" where
  "lists [] = [[]]"
| "lists (x#xs) = (x#xs) # lists xs"

lemma bf_foldl:
  "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) ps = foldl bf (c\<^sub>0, c\<^sub>1) (lists ps)"
  apply (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: c\<^sub>0 c\<^sub>1 rule: bf_closest_pair_it_rec.induct)
    apply (auto simp add: Let_def)
  done

lemma bf_foldr:
  assumes "n = length ps" "2 \<le> n" "c\<^sub>0 = ps!(n-2)" "c\<^sub>1 = ps!(n-1)"
  shows "bf_closest_pair ps = foldr bf' (lists ps) (c\<^sub>0, c\<^sub>1)"
  using assms
  apply (induction ps arbitrary: n c\<^sub>0 c\<^sub>1 rule: bf_closest_pair.induct)
    apply (auto simp add: Let_def)
  done

lemma AUX:
  "bf (foldl bf (c\<^sub>0', c\<^sub>1') (lists ps)) [c\<^sub>0, c\<^sub>1] = bf' [c\<^sub>0', c\<^sub>1'] (foldr bf' (lists ps) (c\<^sub>0, c\<^sub>1))"
proof (induction ps arbitrary: c\<^sub>0' c\<^sub>1' c\<^sub>0 c\<^sub>1)
  case (Cons p ps)
  show ?case 
  proof (cases "ps = [p]")
    case True
    thus ?thesis
      by auto
  next
    case False
    let ?p' = "find_closest p ps"
    show ?thesis
    proof cases
      assume *: "bf (c\<^sub>0', c\<^sub>1') (p # ps) = (c\<^sub>0', c\<^sub>1')"
      hence "bf (foldl bf (c\<^sub>0', c\<^sub>1') (lists (p # ps))) [c\<^sub>0, c\<^sub>1] = bf (foldl bf (c\<^sub>0', c\<^sub>1') (lists ps)) [c\<^sub>0, c\<^sub>1]"
        by simp
      also have "... = bf' [c\<^sub>0', c\<^sub>1'] (foldr bf' (lists ps) (c\<^sub>0, c\<^sub>1))"
        using Cons.IH by simp
      also have "... = bf' [c\<^sub>0', c\<^sub>1'] (bf' (p # ps) (foldr bf' (lists ps) (c\<^sub>0, c\<^sub>1)))"
        using * by (cases ps) (auto simp add: Let_def)
      also have "... = bf' [c\<^sub>0', c\<^sub>1'] (foldr bf' (lists (p # ps)) (c\<^sub>0, c\<^sub>1))"
        by simp
      finally show ?thesis .
    next 
      assume *: "\<not> bf (c\<^sub>0', c\<^sub>1') (p # ps) = (c\<^sub>0', c\<^sub>1')"
      hence "bf (foldl bf (c\<^sub>0', c\<^sub>1') (lists (p # ps))) [c\<^sub>0, c\<^sub>1] = bf (foldl bf (p, ?p') (lists ps)) [c\<^sub>0, c\<^sub>1]"
        by (cases ps) (auto simp add: Let_def)
      also have "... = bf' [p, ?p'] (foldr bf' (lists ps) (c\<^sub>0, c\<^sub>1))"
        using Cons.IH by simp
      also have "... = bf' [c\<^sub>0', c\<^sub>1'] (bf' (p # ps) (foldr bf' (lists ps) (c\<^sub>0, c\<^sub>1)))"
        using * by (cases ps) (auto simp add: Let_def)
      also have "... = bf' [c\<^sub>0', c\<^sub>1'] (foldr bf' (lists (p # ps)) (c\<^sub>0, c\<^sub>1))"
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
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p ps"
  shows "foldl bf (p, p') (lists (p#ps)) = bf (foldl bf (p, p') (lists (p#ps))) [(p#ps)!(n-2), (p#ps)!(n-1)]"
  using assms
proof -
  let ?ps = "p # ps"
  obtain ls where *: "lists ?ps = ls @ [?ps!(n-2), ?ps!(n-1)] # [?ps!(n-1)] # [[]]"
    using lists_decomp_2 assms by blast
  let ?rs = "[?ps!(n-2), ?ps!(n-1)] # [?ps!(n-1)] # [[]]"
  have "bf (foldl bf (p, p') (lists ?ps)) [?ps!(n-2), ?ps!(n-1)] = bf (foldl bf (foldl bf (p, p') ls) ?rs) [?ps!(n-2), ?ps!(n-1)]"
    using * by simp
  also have "... =  bf (foldl bf (foldl bf (p, p') ls) [[?ps!(n-2), ?ps!(n-1)]]) [?ps!(n-2), ?ps!(n-1)]"
    by simp
  also have "... = bf (bf (foldl bf (p, p') ls) [?ps!(n-2), ?ps!(n-1)]) [?ps!(n-2), ?ps!(n-1)]"
    by simp
  also have "... = bf (foldl bf (p, p') ls) [?ps!(n-2), ?ps!(n-1)]"
    by (cases ?ps) (auto simp add: Let_def)
  also have "... = foldl bf (foldl bf (p, p') ls) [[?ps!(n-2), ?ps!(n-1)]]"
    by simp
  also have "... = foldl bf (foldl bf (p, p') ls) ?rs"
    by simp
  also have "... = foldl bf (p, p') (lists ?ps)"
    using * by simp
  finally have "bf (foldl bf (p, p') (lists ?ps)) [?ps!(n-2), ?ps!(n-1)] = foldl bf (p, p') (lists ?ps)" .
  thus ?thesis
    by simp
qed

lemma CUX:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p ps"
  shows "foldr bf' (lists (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)) = bf' [p, p'] (foldr bf' (lists (p#ps)) ((p#ps)!(n-2), (p#ps)!(n-1)))"
proof -
  let ?ps = "p # ps"
  define RS where "RS = foldr bf' (lists ps) (?ps!(n-2), ?ps!(n-1))"
  have *: "bf' [p, p'] (foldr bf' (lists ?ps) (?ps!(n-2), ?ps!(n-1))) = bf' [p, p'] (foldr bf' [?ps] RS)"
    by (simp add: RS_def)
  have #: "foldr bf' (lists ?ps) (?ps!(n-2), ?ps!(n-1)) = foldr bf' [?ps] RS"
    by (simp add: RS_def)
  show ?thesis
  proof (cases "dist (fst RS) (snd RS) \<le> dist p p'")
    case True
    have "0 < length ?ps"
      using assms(1,2) by simp
    hence "bf' ?ps RS = (fst RS, snd RS)"
      using assms(3) True X[of ps RS p] by fastforce
    hence x: "foldr bf' [?ps] RS = (fst RS, snd RS)"
      by simp
    hence "foldr bf' (lists ?ps) (?ps!(n-2), ?ps!(n-1)) = (fst RS, snd RS)"
      using # by simp
    moreover have "bf' [p, p'] (foldr bf' (lists ?ps) (?ps!(n-2), ?ps!(n-1))) = (fst RS, snd RS)"
      using * x True by simp
    ultimately show ?thesis
      by simp
  next
    case False
    have "0 < length ps"
      using assms(1,2) by (metis One_nat_def gr0I le_numeral_extra(4) length_Cons not_less_eq_eq numeral_2_eq_2)
    hence "bf' ?ps RS = (p, p')"
      using False assms(3) Y[of ps RS p] by simp
    then show ?thesis
      using * # by simp
  qed
qed

lemma DUX:
  assumes "n = length (p # ps)" "2 \<le> n" "p' = find_closest p ps"
  shows "bf_closest_pair (p#ps) = bf_closest_pair_it_rec (p, p') (p#ps)"
proof -
  let ?ps = "p # ps"
  have "bf_closest_pair ?ps = foldr bf' (lists ?ps) (?ps!(n-2), ?ps!(n-1))"
    using assms bf_foldr by blast
  also have "... = bf' [p, p'] (foldr bf' (lists ?ps) (?ps!(n-2), ?ps!(n-1)))"
    using assms CUX by blast
  also have "... = bf (foldl bf (p, p') (lists ?ps)) [?ps!(n-2), ?ps!(n-1)]"
    using AUX by metis
  also have "... = foldl bf (p, p') (lists ?ps)"
    using assms BUX by simp
  also have "... = bf_closest_pair_it_rec (p, p') ?ps"
    using bf_foldl by simp
  finally show ?thesis .
qed

lemma bf_closest_pair_conv_bf_closest_pair_it[code_unfold]:
  "bf_closest_pair ps = bf_closest_pair_it ps"
  using DUX apply (cases ps) apply (auto) sledgehammer



lemma bf_closest_pair_drop_fst:
  assumes "0 < length ps" "dist p\<^sub>0 (find_closest p\<^sub>0 ps) \<le> dist c\<^sub>0 (find_closest c\<^sub>0 (p\<^sub>0 # ps))"
  shows "bf_closest_pair (c\<^sub>0 # p\<^sub>0 # ps) = bf_closest_pair (p\<^sub>0 # ps)"
  using assms
proof (induction ps arbitrary: c\<^sub>0 p\<^sub>0 rule: bf_closest_pair.induct)
  case (3 p\<^sub>1 p\<^sub>2)
  then show ?case
    by (smt bf_closest_pair.simps(4) prod.sel(1) prod.sel(2) split_def)
next
  case (4 p\<^sub>2 p\<^sub>3 p\<^sub>4 ps)
  let ?ps = "p\<^sub>0 # p\<^sub>2 # p\<^sub>3 # p\<^sub>4 # ps"
  let ?c\<^sub>0\<^sub>1 = "bf_closest_pair ?ps"
  let ?c\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
  let ?c\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"
  let ?p\<^sub>1 = "find_closest c\<^sub>0 ?ps"

  have "dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist c\<^sub>0 ?p\<^sub>1"
    by (smt "4.prems"(2) bf_closest_pair.simps(4) prod.sel(1) prod.sel(2) split_def)
  hence "(?c\<^sub>0, ?c\<^sub>1) = bf_closest_pair (c\<^sub>0 # p\<^sub>0 # p\<^sub>2 # p\<^sub>3 # p\<^sub>4 # ps)"
    by (auto split: prod.splits)
  thus ?case
    by simp
qed auto

lemma bf_closest_pair_drop_snd:
  assumes "dist c\<^sub>0 (find_closest c\<^sub>0 (p\<^sub>0 # p\<^sub>2 # ps)) < dist p\<^sub>0 (find_closest p\<^sub>0 (p\<^sub>2 # ps))" "find_closest c\<^sub>0 (p\<^sub>0 # p\<^sub>2 # ps) \<noteq> p\<^sub>0"
  shows "bf_closest_pair (c\<^sub>0 # p\<^sub>0 # p\<^sub>2 # ps) = bf_closest_pair (c\<^sub>0 # p\<^sub>2 # ps)"
  sorry

lemma bf_closest_pair_conv_bf_closest_pair_it_rec':
  assumes "0 < length ps"
  shows "bf_closest_pair (p\<^sub>0 # ps) = bf_closest_pair_it_rec (p\<^sub>0, find_closest p\<^sub>0 ps) ps"
  using assms
proof (induction "(p\<^sub>0, find_closest p\<^sub>0 ps)" ps arbitrary: p\<^sub>0 rule: bf_closest_pair_it_rec.induct)
  case (3 c\<^sub>0 p\<^sub>0 p\<^sub>2 ps)

  let ?c\<^sub>1 = "find_closest c\<^sub>0 (p\<^sub>0 # p\<^sub>2 # ps)"
  let ?p\<^sub>1 = "find_closest p\<^sub>0 (p\<^sub>2 # ps)"

  thm "3.prems"
  thm "3.hyps"(1)
  thm "3.hyps"(2)

  show ?case
  proof (cases "dist c\<^sub>0 ?c\<^sub>1 < dist p\<^sub>0 ?p\<^sub>1")
    case True
    let ?bf = "bf_closest_pair (p\<^sub>0 # p\<^sub>2 # ps)"
    show ?thesis
    proof cases
      assume *: "?c\<^sub>1 = find_closest c\<^sub>0 (p\<^sub>2 # ps)"
      hence "?c\<^sub>1 \<noteq> p\<^sub>0"
        sorry
      have "bf_closest_pair (c\<^sub>0 # p\<^sub>2 # ps) = bf_closest_pair_it_rec (c\<^sub>0, ?c\<^sub>1) (p\<^sub>0 # p\<^sub>2 # ps)"
        using * "3.hyps"(1) True by simp
      thus ?thesis
        using True sorry
    next
      assume "\<not> ?c\<^sub>1 = find_closest c\<^sub>0 (p\<^sub>2 # ps)"
      hence "?c\<^sub>1 = p\<^sub>0"
        by (smt find_closest.simps(3))
      thus ?thesis
        using True sorry
    qed
  next
    case False
    hence "bf_closest_pair (p\<^sub>0 # p\<^sub>2 # ps) = bf_closest_pair_it_rec (c\<^sub>0, ?c\<^sub>1) (p\<^sub>0 # p\<^sub>2 # ps)"
      using "3.hyps"(2) by simp
    moreover have "bf_closest_pair (c\<^sub>0 # p\<^sub>0 # p\<^sub>2 # ps) = bf_closest_pair (p\<^sub>0 # p\<^sub>2 # ps)"
      using False bf_closest_pair_drop_fst[of "p\<^sub>2 # ps"] by simp
    ultimately show ?thesis
      by argo
  qed
qed oops




lemma bf_closest_pair_conv_bf_closest_pair_it_rec:
  "bf_closest_pair (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # p\<^sub>1 # ps)"
  oops

end