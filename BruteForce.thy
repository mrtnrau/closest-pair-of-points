theory BruteForce
  imports "HOL-Analysis.Analysis" "Geometry" "ClosestPairOfPoints"
begin




fun brute_force_closest' :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "brute_force_closest' _ [] = undefined"
| "brute_force_closest' _ [p\<^sub>1] = p\<^sub>1"
| "brute_force_closest' p\<^sub>0 (p\<^sub>1 # ps) = (
    let p\<^sub>2 = brute_force_closest' p\<^sub>0 ps in
    if dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>2 then
      p\<^sub>1
    else
      p\<^sub>2
  )"




lemma brute_force_closest'_dist:
  "\<forall>p\<^sub>1 \<in> set ps. dist p\<^sub>0 (brute_force_closest' p\<^sub>0 ps) \<le> dist p\<^sub>0 p\<^sub>1"
  by (induction p\<^sub>0 ps rule: brute_force_closest'.induct) (auto simp add: Let_def)

lemma brute_force_closest'_set:
  assumes "0 < length ps"
  shows "brute_force_closest' p ps \<in> set ps"
  using assms by (induction p ps rule: brute_force_closest'.induct) (auto simp add: Let_def)

lemma brute_force_closest'_ne:
  assumes "0 < length ps" "p \<notin> set ps"
  shows "brute_force_closest' p ps \<noteq> p"
  using assms by (induction p ps rule: brute_force_closest'.induct) (auto simp add: Let_def)

declare brute_force_closest'.simps [simp del]




fun brute_force_closest :: "point list \<Rightarrow> (point * point)" where
  "brute_force_closest [] = undefined"
| "brute_force_closest [_] = undefined"
| "brute_force_closest [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "brute_force_closest (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = brute_force_closest ps in
    let p\<^sub>1 = brute_force_closest' p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"




lemma brute_force_closest_set_p0:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "p\<^sub>0 \<in> set ps"
  using assms
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: brute_force_closest.induct)
  apply (auto simp add: Let_def brute_force_closest'_set split!: prod.splits if_splits)
  done

lemma brute_force_closest_set_p1:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "p\<^sub>1 \<in> set ps"
  using assms brute_force_closest'_set
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: brute_force_closest.induct)
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (meson list.discI set_ConsD)
  done

lemma brute_force_closest_set_p0_ne_p1:
  assumes "distinct ps" "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "p\<^sub>0 \<noteq> p\<^sub>1"
  using assms brute_force_closest'_ne
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: brute_force_closest.induct)
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (metis Pair_inject neq_Nil_conv set_ConsD)+
  done

lemma brute_force_closest_dist:
  assumes "1 < length ps"
  shows "cpop_dist (brute_force_closest ps) ps"
  using assms
proof (induction ps rule: brute_force_closest.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)

  let ?ps' = "p\<^sub>1 # p\<^sub>2 # ps"
  let ?c = "brute_force_closest ?ps'"
  let ?c\<^sub>0 = "fst ?c"
  let ?c\<^sub>1 = "snd ?c"

  have *: "\<forall>p \<in> set ?ps'. dist p\<^sub>0 (brute_force_closest' p\<^sub>0 ?ps') \<le> dist p\<^sub>0 p"
    using brute_force_closest'_dist by blast

  thus ?case using 4
  proof (cases "dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist p\<^sub>0 (brute_force_closest' p\<^sub>0 ?ps')")
    case True
    hence "\<forall>p \<in> set ?ps'. dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist p\<^sub>0 p"
      using * by auto
    thus ?thesis using 4 True
      by (auto simp add: cpop_dist_id split: prod.splits)
  next
    case False
    thus ?thesis using 4 *
      by (auto simp add: cpop_dist_upd split: prod.splits)
  qed
qed (auto simp add: dist_commute cpop_dist)

end