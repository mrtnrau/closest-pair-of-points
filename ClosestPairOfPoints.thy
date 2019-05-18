theory ClosestPairOfPoints
  imports "HOL-Analysis.Analysis" "Geometry"
begin




text \<open>
  Duplicates
\<close>

fun dups :: "'a list \<Rightarrow> 'a list" where
  "dups [] = []"
| "dups (x # xs) = (
    if x \<in> set xs then
      x # dups xs
    else
      dups xs
  )"

lemma dups_duplicate:
  "x \<in> set (dups xs) \<longleftrightarrow> (\<exists>i j. i < length xs \<and> j < length xs \<and> i \<noteq> j \<and> x = xs!i \<and> x = xs!j)" (is "?A \<longleftrightarrow> ?B")
proof standard
  assume ?A
  then show ?B
  proof (induction xs)
    case (Cons y xs)
    thus ?case
    proof (cases "x \<in> set (dups xs)")
      case True
      thus ?thesis
        using Cons by fastforce
    next
      case False
      hence 0: "x = y"
        using Cons False by (metis dups.simps(2) set_ConsD)
      hence "x \<in> set xs"
        by (metis Cons.prems False dups.simps(2))
      then obtain j where "j < length xs \<and> x = xs!j"
        by (metis in_set_conv_nth)
      hence "j + 1 < length (y#xs) \<and> x = (y#xs)!(j+1)"
        by auto
      moreover have "0 < length (y#xs) \<and> y = (y#xs)!0"
        by simp
      ultimately show ?thesis
        using 0 by fastforce
    qed
  qed simp
next
  assume ?B
  then show ?A
  proof (induction xs)
    case (Cons y xs)
    then obtain i j where "i < length (y # xs) \<and> j < length (y # xs) \<and> i \<noteq> j \<and> x = (y # xs) ! i \<and> x = (y # xs) ! j"
      by blast
    thus ?case 
      using Cons.IH less_Suc_eq_0_disj apply (auto) by fastforce+
  qed simp
qed




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
      (p\<^sub>0 = p\<^sub>1) \<and> p\<^sub>0 \<in> set (dups ps)
  )"




text \<open>
  Simplification of cpop_dist for distinct lists of points
\<close>

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

end