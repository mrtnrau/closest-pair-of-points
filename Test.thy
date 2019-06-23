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
proof (induction "(p\<^sub>0, p\<^sub>1)" ps arbitrary: p\<^sub>0 p\<^sub>1 rule: bf_closest_pair_it_rec.induct)
case (1 c\<^sub>0 c\<^sub>1)
  then show ?case sorry
next
  case (2 c\<^sub>0 c\<^sub>1 uu)
  then show ?case sorry
next
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  then show ?case sorry
qed

lemma bf_closest_pair_conv_bf_closest_pair_it[code_unfold]:
  "bf_closest_pair ps = bf_closest_pair_it ps"
  using bf_closest_pair_conv_bf_closest_pair_it_rec
  by (metis bf_closest_pair.simps(1,2) bf_closest_pair_it.elims bf_closest_pair_it.simps(2))

end