theory ClosestPairOfPoints
  imports "HOL-Analysis.Analysis" "Geometry"
begin




text \<open>
  Closest Pair of Points Distance Criteria
\<close>

fun cpop_dist :: "(point * point) \<Rightarrow> point list \<Rightarrow> bool" where
  "cpop_dist (p\<^sub>0, p\<^sub>1) ps \<longleftrightarrow> (\<forall>x \<in> set ps. \<forall>y \<in> set ps. x \<noteq> y \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist x y)"

lemma cpop_dist:
  "cpop_dist (p\<^sub>0, p\<^sub>1) ps \<longleftrightarrow> (\<forall>x \<in> set ps. \<forall>y \<in> set ps. x \<noteq> y \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist x y)"
  by simp

lemma cpop_dist_id:
  assumes "cpop_dist (c\<^sub>0, c\<^sub>1) ps" "\<forall>p \<in> set ps. dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "cpop_dist (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps)"
  using assms by (simp add: dist_commute)

lemma cpop_dist_upd:
  assumes "cpop_dist (c\<^sub>0, c\<^sub>1) ps" "dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1" "\<forall>p \<in> set ps. dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "cpop_dist (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # ps)"
  using assms by (smt cpop_dist.simps cpop_dist_id)

declare cpop_dist.simps [simp del]

end