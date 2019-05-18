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




lemma brute_force_closest'_point:
  "0 < length ps \<Longrightarrow> \<forall>p\<^sub>1 \<in> set ps. dist p\<^sub>0 (brute_force_closest' p\<^sub>0 ps) \<le> dist p\<^sub>0 p\<^sub>1"
  by (induction p\<^sub>0 ps rule: brute_force_closest'.induct) (auto simp add: Let_def)

lemma brute_force_closest'_set:
  "0 < length ps \<Longrightarrow> brute_force_closest' p ps \<in> set ps"
  by (induction p ps rule: brute_force_closest'.induct) (auto simp add: Let_def)

lemma brute_force_closest'_distinct:
  "0 < length ps \<Longrightarrow> p \<notin> set ps \<Longrightarrow> brute_force_closest' p ps \<noteq> p"
  by (induction p ps rule: brute_force_closest'.induct) (auto simp add: Let_def)

lemma brute_force_closest'_not_distinct:
  "0 < length ps \<Longrightarrow> p \<in> set ps \<Longrightarrow> brute_force_closest' p ps = p"
  by (induction p ps rule: brute_force_closest'.induct) (auto simp add: Let_def)




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




lemma brute_force_closest_set:
  "1 < length ps \<Longrightarrow> cpop_set (brute_force_closest ps) ps"
  apply (induction ps rule: brute_force_closest.induct)
  apply (auto simp add: Let_def split: prod.splits if_splits)
  using brute_force_closest'_set by fastforce+

lemma brute_force_closest_distinct:
  "1 < length ps \<Longrightarrow> distinct ps \<Longrightarrow> (p\<^sub>0, p\<^sub>1) = brute_force_closest ps \<Longrightarrow> p\<^sub>0 \<noteq> p\<^sub>1"
  using brute_force_closest'_distinct
  apply (induction ps rule: brute_force_closest.induct)
  apply (auto simp add: Let_def split: prod.splits if_splits)
  apply (metis list.discI prod.inject set_ConsD)+
  done

lemma brute_force_closest_not_distinct:
  "1 < length ps \<Longrightarrow> \<not> distinct ps \<Longrightarrow> (p\<^sub>0, p\<^sub>1) = brute_force_closest ps \<Longrightarrow> p\<^sub>0 = p\<^sub>1 \<and> p\<^sub>0 \<in> set (dups ps)"
proof (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: brute_force_closest.induct)
  case (4 x y z ps)

  let ?ps' = "y # z # ps"
  let ?c = "brute_force_closest ?ps'"
  let ?x' = "brute_force_closest' x ?ps'"
  let ?c\<^sub>0 = "fst ?c"
  let ?c\<^sub>1 = "snd ?c"

  show ?case
  proof (cases "distinct ?ps'")
    case True
    hence 0: "x \<in> set ?ps'"
      using "4.prems"(2) by auto
    have "?c\<^sub>0 \<noteq> ?c\<^sub>1"
      using True brute_force_closest_distinct[of ?ps' ?c\<^sub>0 ?c\<^sub>1] by simp
    moreover have "?x' = x"
      using brute_force_closest'_not_distinct 0 by blast
    ultimately have "(x, x) = brute_force_closest (x # y # z # ps)"
      by (auto split: prod.splits)
    moreover have "x = p\<^sub>0" "x = p\<^sub>1"
      using calculation "4.prems"(3) by (metis prod.inject)+
    ultimately show ?thesis
      using 0 by auto
  next
    case False
    hence 0: "?c\<^sub>0 = ?c\<^sub>1 \<and> ?c\<^sub>0 \<in> set (dups ?ps')"
      using "4.IH"[of ?c\<^sub>0 ?c\<^sub>1]  "4.prems"(1) by fastforce
    hence "(?c\<^sub>0, ?c\<^sub>1) = brute_force_closest (x # y # z # ps)"
      by (auto split: prod.splits)
    hence "p\<^sub>0 = ?c\<^sub>0" "p\<^sub>1 = ?c\<^sub>1"
      using "4.prems"(3) by (metis prod.inject)+
    then show ?thesis
      using 0 by fastforce
  qed
qed auto

lemma brute_force_closest_distinct_dist:
  "1 < length ps \<Longrightarrow> cpop_distinct_dist (brute_force_closest ps) ps"
proof (induction ps rule: brute_force_closest.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)

  let ?ps' = "p\<^sub>1 # p\<^sub>2 # ps"
  let ?c = "brute_force_closest ?ps'"
  let ?c\<^sub>0 = "fst ?c"
  let ?c\<^sub>1 = "snd ?c"

  have *: "cpop_distinct_dist (brute_force_closest ?ps') ?ps'"
    using 4 by simp
  have #: "\<forall>x \<in> set ?ps'. dist p\<^sub>0 (brute_force_closest' p\<^sub>0 ?ps') \<le> dist p\<^sub>0 x"
    using brute_force_closest'_point by blast

  thus ?case
  proof (cases "dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist p\<^sub>0 (brute_force_closest' p\<^sub>0 ?ps')")
    case True
    hence "\<forall>p \<in> set ?ps'. dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist p\<^sub>0 p"
      using "#" by auto
    thus ?thesis using * True
      by (auto simp add: Let_def cpop_distinct_dist_id split: prod.splits if_splits)
  next
    case False
    thus ?thesis using * #
      by (auto simp add: cpop_distinct_dist_upd Let_def split: prod.splits if_splits)
  qed
qed (auto simp add: dist_commute cpop_distinct_dist.simps)




theorem brute_force_closest_cpop_set:
  "1 < length ps \<Longrightarrow> cpop_set (brute_force_closest ps) ps"
  by (simp add: brute_force_closest_set)

theorem brute_force_closest_cpop_distinct:
  "1 < length ps \<Longrightarrow> cpop_distinct (brute_force_closest ps) ps"
  by (metis brute_force_closest_distinct brute_force_closest_not_distinct cpop_distinct.elims(3))

theorem brute_force_closest_cpop_dist:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "cpop_dist (p\<^sub>0, p\<^sub>1) ps"
proof (cases "distinct ps")
  case True
  thus ?thesis
    using assms by (metis brute_force_closest_distinct_dist cpop_dist_iff_cpop_distinct_dist)
next
  case False
  hence "p\<^sub>0 = p\<^sub>1 \<and> p\<^sub>0 \<in> set (dups ps)"
    using brute_force_closest_not_distinct[of ps p\<^sub>0 p\<^sub>1] assms by blast
  moreover obtain i j where "i < length ps \<and> j < length ps \<and> i \<noteq> j \<and> p\<^sub>0 = ps!i \<and> p\<^sub>0 = ps!j"
    using dups_duplicate calculation by metis
  ultimately show ?thesis
    by simp
qed

end