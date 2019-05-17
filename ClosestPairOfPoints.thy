theory ClosestPairOfPoints
  imports "HOL-Analysis.Analysis" "Geometry"
begin




text \<open>
  Closest Pair of Points Criteria
\<close>

fun cpop_dist :: "(point * point) \<Rightarrow> point list \<Rightarrow> bool" where
  "cpop_dist (p\<^sub>0, p\<^sub>1) ps \<longleftrightarrow> (\<forall>i < length ps. \<forall>j < length ps. i \<noteq> j \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist (ps!i) (ps!j))"

fun cpop_set :: "(point * point) \<Rightarrow> point list \<Rightarrow> bool" where
  "cpop_set (p\<^sub>0, p\<^sub>1) ps \<longleftrightarrow> p\<^sub>0 \<in> set ps \<and> p\<^sub>1 \<in> set ps"

fun cpop_distinct :: "(point * point) \<Rightarrow> point list \<Rightarrow> bool" where
  "cpop_distinct (p\<^sub>0, p\<^sub>1) ps \<longleftrightarrow> (
    if distinct ps then
      p\<^sub>0 \<noteq> p\<^sub>1
    else
      (p\<^sub>0 = p\<^sub>1) \<and> 2 \<le> length (filter (\<lambda>p. p = p\<^sub>0) ps)
  )"

fun cpop_distinct_dist :: "(point * point) \<Rightarrow> point list \<Rightarrow> bool" where
  "cpop_distinct_dist (p\<^sub>0, p\<^sub>1) ps \<longleftrightarrow> (\<forall>x \<in> set ps. \<forall>y \<in> set ps. x \<noteq> y \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist x y)"




lemma distinct_pairwise:
  "distinct xs \<Longrightarrow> (\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j \<longrightarrow> P (xs!i) (xs!j)) \<longleftrightarrow> (\<forall>x \<in> set xs. \<forall>y \<in> set xs. x \<noteq> y \<longrightarrow> P x y)"
  by (metis (no_types, hide_lams) distinct_conv_nth in_set_conv_nth)

lemma cpop_dist_iff_cpop_distinct_dist:
  "distinct ps \<Longrightarrow> cpop_dist (p\<^sub>0, p\<^sub>1) ps \<longleftrightarrow> cpop_distinct_dist (p\<^sub>0, p\<^sub>1) ps"
  using distinct_pairwise[of ps "(\<lambda>x y. dist p\<^sub>0 p\<^sub>1 \<le> dist x y)"] by simp

lemma cpop_distinct_dist_id:
  "cpop_distinct_dist (c\<^sub>0, c\<^sub>1) ps \<Longrightarrow> \<forall>p \<in> set ps. dist c\<^sub>0 c\<^sub>1 \<le> dist c p \<Longrightarrow> cpop_distinct_dist (c\<^sub>0, c\<^sub>1) (c # ps)"
  by (simp add: dist_commute)

lemma cpop_distinct_dist_upd:
  assumes "cpop_distinct_dist (c\<^sub>0, c\<^sub>1) ps" "dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1" "\<forall>p \<in> set ps. dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "cpop_distinct_dist (p\<^sub>0, p\<^sub>1) (p\<^sub>0 # ps)"
  using assms by (smt cpop_distinct_dist.simps cpop_distinct_dist_id)

declare cpop_distinct_dist.simps [simp del]

lemma _?:
  assumes "\<not> distinct ps" "cpop_dist (p\<^sub>0, p\<^sub>1) ps"
  shows "p\<^sub>0 = p\<^sub>1"
proof (rule ccontr)
  assume *: "p\<^sub>0 \<noteq> p\<^sub>1"
  obtain p as bs cs where 0: "ps = as @ [p] @ bs @ [p] @ cs"
    using assms(1) not_distinct_decomp by blast
  hence 1: "ps = as @ [ps!(length as)] @ bs @ [ps!(length as + 1 + length bs)] @ cs"
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 append.assoc append_Cons length_append list.size(3) list.size(4) nth_append_length)
  moreover have "length as < length ps" "length as + 1 + length bs < length ps"
    apply (metis (no_types, lifting) add_diff_cancel_left' add_is_0 calculation gr0I length_append list.size(4) nat.simps(3) zero_less_diff)
    sorry
  ultimately obtain i j where 2: "ps = as @ [ps!i] @ bs @ [ps!j] @ cs \<and> i \<noteq> j \<and> i < length ps \<and> j < length ps"
    by fastforce
  hence "dist p\<^sub>0 p\<^sub>1 \<le> dist (ps!i) (ps!j)"
    using assms(2) by simp
  also have "... = 0"
    using 0 2 by simp
  finally show False
     using * by simp
qed

end