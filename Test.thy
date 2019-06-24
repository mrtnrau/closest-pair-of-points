theory Test
  imports "HOL-Analysis.Analysis"
begin

type_synonym point = "(real * real)"

find_theorems dist

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

lemma find_closest_dist:
  "\<forall>p \<in> set ps. dist p\<^sub>0 (find_closest p\<^sub>0 ps) \<le> dist p\<^sub>0 p"
  sorry

lemma find_closest_set:
  "0 < length ps \<Longrightarrow> find_closest p\<^sub>0 ps \<in> set ps"
  sorry

lemma find_closest_ne:
  "0 < length ps \<Longrightarrow> p\<^sub>0 \<notin> set ps \<Longrightarrow> find_closest p\<^sub>0 ps \<noteq> p\<^sub>0"
  sorry


fun bf_closest_pair :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair [] = undefined"
| "bf_closest_pair [_] = undefined"
| "bf_closest_pair [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "bf_closest_pair (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps in
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

lemma bf_closest_pair_c0:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
  sorry

lemma bf_closest_pair_c1:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps \<Longrightarrow> c\<^sub>1 \<in> set ps"
  sorry

lemma bf_closest_pair_c0_ne_c1:
  "1 < length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
  sorry

lemma bf_closest_pair_dist:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = bf_closest_pair ps"
  shows "\<forall>p\<^sub>0 \<in> set ps. \<forall>p\<^sub>1 \<in> set ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1"
  sorry

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
  "bf_closest_pair_it (p\<^sub>0 # p\<^sub>1 # ps) = bf_closest_pair_it_rec (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # p\<^sub>1 # ps)"
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

lemma bf_foldl:
  "bf_closest_pair_it_rec (c\<^sub>0, c\<^sub>1) ps = foldl bf (c\<^sub>0, c\<^sub>1) (rev (subseqs ps))"
  sorry

lemma bf_foldr:
  "2 \<le> length ps \<Longrightarrow> bf_closest_pair ps = foldr (\<lambda>a b. bf b a) (rev (subseqs ps)) (ps!0, ps!1)"
  sorry

lemma list3:
  assumes "P []" "\<And>x. P [x]" "\<And>x y xs. P (x#y#xs)"
  shows "P xs"
  using assms apply (induction xs) apply (auto)
  by (metis assms(2) assms(3) neq_Nil_conv)

lemma BUX:
  "bf (bf x y) z = bf (bf x z) y"
  apply (cases rule: list3)
    apply (auto simp add: Let_def)
  subgoal sorry
  subgoal sorry
  subgoal sorry
  done

lemma AUX:
  assumes "\<And>x y. f x y = g y x"
  assumes "\<And>x y z. f (f x y) z = f (f x z) y"
  assumes "\<And>x y z. g x (g y z) = g y (g x z)"
  shows "foldl f a xs = foldr g xs a"
  sorry

lemma
  "2 \<le> length ps \<Longrightarrow> bf_closest_pair ps = bf_closest_pair_it_rec (ps!0, ps!1) ps"
  using bf_foldl[of "ps!0" "ps!1"] bf_foldr BUX by (simp add: AUX)

lemma foldr_com_distrib:
  assumes "\<And>a b. f a b = f b a" "\<And>a b c. f a (f b c) = f (f a b) c"
  shows "foldr f xs (f x a) = f x (foldr f xs a)"
  using assms
proof (induction xs)
  case (Cons y xs)
  have "foldr f (y#xs) (f x a) = f y (foldr f xs (f x a))"
    by simp
  also have "... = f y (f x (foldr f xs a))"
    using Cons by fastforce
  also have "... = f (f x (foldr f xs a)) y"
    using Cons.prems(1) by simp
  also have "... = f x (f (foldr f xs a) y)"
    using Cons.prems(2)[symmetric] by simp
  also have "... = f x (f y (foldr f xs a))"
    using Cons.prems(1) by simp
  also have "... = f x (foldr f (y#xs) a)"
    by simp
  finally show ?case .
qed simp

lemma foldl_conv_foldr_if_com_distrib:
  assumes "\<And>a b. f a b = f b a" "\<And>a b c. f a (f b c) = f (f a b) c"
  shows "foldl f a xs = foldr f xs a"
  using assms
proof (induction xs arbitrary: a)
  case (Cons x xs)
  have "foldl f a (x#xs) = foldl f (f a x) xs"
    by simp
  also have "... = foldr f xs (f a x)"
    using Cons by blast
  also have "... = foldr f xs (f x a)"
    using Cons.prems(1) by simp
  also have "... = f x (foldr f xs a)"
    using Cons.prems by (meson foldr_com_distrib)
  also have "... = foldr f (x#xs) a"
    by simp
  finally show ?case .
qed simp











value "bf_closest_pair_it_rec ((0,1), (0,0)) [(0,1),(0,0)]"
value "dist (0,0) (0,1)"
  
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


lemma bf_closest_pair_conv_bf_closest_pair_it[code_unfold]:
  "bf_closest_pair ps = bf_closest_pair_it ps"
  using bf_closest_pair_conv_bf_closest_pair_it_rec
  by (metis bf_closest_pair.simps(1,2) bf_closest_pair_it.elims bf_closest_pair_it.simps(2))

end