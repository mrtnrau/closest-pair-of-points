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




text \<open>
  Helper: Find the closest point to p0 within ps.
\<close>

fun find_closest :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest _ [] = undefined"
| "find_closest _ [p\<^sub>1] = p\<^sub>1"
| "find_closest p\<^sub>0 (p\<^sub>1 # ps) = (
    let p\<^sub>2 = find_closest p\<^sub>0 ps in
    if dist p\<^sub>0 p\<^sub>1 < dist p\<^sub>0 p\<^sub>2 then
      p\<^sub>1
    else
      p\<^sub>2
  )"




lemma find_closest_dist:
  "\<forall>p\<^sub>1 \<in> set ps. dist p\<^sub>0 (find_closest p\<^sub>0 ps) \<le> dist p\<^sub>0 p\<^sub>1"
  by (induction p\<^sub>0 ps rule: find_closest.induct) (auto simp add: Let_def)

lemma find_closest_set:
  assumes "0 < length ps"
  shows "find_closest p ps \<in> set ps"
  using assms by (induction p ps rule: find_closest.induct) (auto simp add: Let_def)

lemma find_closest_ne:
  assumes "0 < length ps" "p \<notin> set ps"
  shows "find_closest p ps \<noteq> p"
  using assms by (induction p ps rule: find_closest.induct) (auto simp add: Let_def)

declare find_closest.simps [simp del]




text \<open>
  Brute Force Algorithm
\<close>

fun brute_force_closest :: "point list \<Rightarrow> (point * point)" where
  "brute_force_closest [] = undefined"
| "brute_force_closest [_] = undefined"
| "brute_force_closest [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "brute_force_closest (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = brute_force_closest ps in
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
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
  apply (auto simp add: Let_def find_closest_set split!: prod.splits if_splits)
  done

lemma brute_force_closest_set_p1:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "p\<^sub>1 \<in> set ps"
  using assms find_closest_set
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: brute_force_closest.induct)
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (meson list.discI set_ConsD)
  done

lemma brute_force_closest_set_p0_ne_p1:
  assumes "distinct ps" "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "p\<^sub>0 \<noteq> p\<^sub>1"
  using assms find_closest_ne
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

  have *: "\<forall>p \<in> set ?ps'. dist p\<^sub>0 (find_closest p\<^sub>0 ?ps') \<le> dist p\<^sub>0 p"
    using find_closest_dist by blast

  thus ?case using 4
  proof (cases "dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist p\<^sub>0 (find_closest p\<^sub>0 ?ps')")
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




text \<open>
  Sorted with respect to x or y axis aliases.
\<close>

definition sortX :: "point list \<Rightarrow> point list" where
  "sortX ps = sort_key fst ps"

definition sortedX :: "point list \<Rightarrow> bool" where
  "sortedX ps = sorted_wrt (\<lambda>(x\<^sub>0, _) (x\<^sub>1, _). x\<^sub>0 \<le> x\<^sub>1) ps"

definition sortY :: "point list \<Rightarrow> point list" where
  "sortY ps = sort_key snd ps"

definition sortedY :: "point list \<Rightarrow> bool" where
  "sortedY ps = sorted_wrt (\<lambda>(_, y\<^sub>0) (_, y\<^sub>1). y\<^sub>0 \<le> y\<^sub>1) ps"




text \<open>
  Helper: Split list of points into two list depending on set membership while keeping them sorted.
\<close>

fun split :: "point set \<Rightarrow> point list \<Rightarrow> (point list * point list)" where
  "split _ [] = ([], [])"
| "split ps\<^sub>L (y # ys) = (
    let (ys\<^sub>L, ys\<^sub>R) = split ps\<^sub>L ys in
    if y \<in> ps\<^sub>L then
      (y # ys\<^sub>L, ys\<^sub>R)
    else
      (ys\<^sub>L, y # ys\<^sub>R)
  )"




text \<open>
  Helper: Brute Force but only the 7 points following the one under question.
\<close>

fun closest_7 :: "point list \<Rightarrow> (point * point)" where
  "closest_7 [] = undefined"
| "closest_7 [_] = undefined"
| "closest_7 [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_7 (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_7 ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"




text \<open>
  Closest' Pair of Points Algorithm
\<close>

fun combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let \<delta> = min (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) in
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ys' = filter (\<lambda>(x, _). l - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys in
    if length ys' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_7 ys' in
      if dist p\<^sub>0 p\<^sub>1 < \<delta> then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"





function (sequential) closest' :: "point set \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "closest' ps xs ys = (
    let n = length xs in
    if n \<le> 3 then
      brute_force_closest xs
    else
      let xs\<^sub>L = take (n div 2) xs in
      let xs\<^sub>R = drop (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in
      let ps\<^sub>L = set xs\<^sub>L in
      let ps\<^sub>R = set xs\<^sub>R in
      let (ys\<^sub>L, ys\<^sub>R) = split ps\<^sub>L ys in
      let (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest' ps\<^sub>L xs\<^sub>L ys\<^sub>L in
      let (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest' ps\<^sub>R xs\<^sub>R ys\<^sub>R in
      combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys 
  )"
  by pat_completeness auto
termination closest'
  apply (relation "Wellfounded.measure (\<lambda>(_, xs, _). length xs)")
  apply (auto)
  done

declare split.simps closest_7.simps combine.simps [simp del]




lemma closest'_set_p0:
  assumes "1 < length xs" "set xs = set ys" "(p\<^sub>0, p\<^sub>1) = closest' (set xs) xs ys"
  shows "p\<^sub>0 \<in> set xs"
  using assms
proof (induction xs arbitrary: ys p\<^sub>0 p\<^sub>1 rule: length_induct)
  case (1 xs)

  let ?n = "length xs"

  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(p\<^sub>0, p\<^sub>1) = brute_force_closest xs"
      using "1.prems"(3) by simp
    thus ?thesis
      using "1.prems"(1) brute_force_closest_set_p0 by simp
  next
    case False

    let ?xs\<^sub>L = "take (?n div 2) xs"
    let ?xs\<^sub>R = "drop (?n div 2) xs"
    let ?l = "fst (hd ?xs\<^sub>R)"
    let ?ps\<^sub>L = "set ?xs\<^sub>L"
    let ?ps\<^sub>R = "set ?xs\<^sub>R"
    let ?ys\<^sub>L\<^sub>R = "split ?ps\<^sub>L ys"
    let ?ys\<^sub>L = "fst ?ys\<^sub>L\<^sub>R"
    let ?ys\<^sub>R = "snd ?ys\<^sub>L\<^sub>R"
    let ?p\<^sub>0\<^sub>1\<^sub>L = "closest' ?ps\<^sub>L ?xs\<^sub>L ?ys\<^sub>L"
    let ?p\<^sub>0\<^sub>L = "fst ?p\<^sub>0\<^sub>1\<^sub>L"
    let ?p\<^sub>1\<^sub>L = "snd ?p\<^sub>0\<^sub>1\<^sub>L"
    let ?p\<^sub>0\<^sub>1\<^sub>R = "closest' ?ps\<^sub>R ?xs\<^sub>R ?ys\<^sub>R"
    let ?p\<^sub>0\<^sub>R = "fst ?p\<^sub>0\<^sub>1\<^sub>R"
    let ?p\<^sub>1\<^sub>R = "snd ?p\<^sub>0\<^sub>1\<^sub>R"

    have "length ?xs\<^sub>L < ?n" "1 < length ?xs\<^sub>L"
      using False by simp_all
    moreover have "(?p\<^sub>0\<^sub>L, ?p\<^sub>1\<^sub>L) = closest' ?ps\<^sub>L ?xs\<^sub>L ?ys\<^sub>L"
      by simp
    moreover have "set ?xs\<^sub>L = set ?ys\<^sub>L"
      sorry
    ultimately have "?p\<^sub>0\<^sub>L \<in> ?ps\<^sub>L"
      using 1 by blast
    hence IHL: "?p\<^sub>0\<^sub>L \<in> set xs"
      by (meson in_set_takeD)

    have "length ?xs\<^sub>R < ?n" "1 < length ?xs\<^sub>R"
      using False by simp_all
    moreover have "(?p\<^sub>0\<^sub>R, ?p\<^sub>1\<^sub>R) = closest' ?ps\<^sub>R ?xs\<^sub>R ?ys\<^sub>R"
      by simp
    moreover have "set ?xs\<^sub>R = set ?ys\<^sub>R"
      sorry
    ultimately have "?p\<^sub>0\<^sub>R \<in> ?ps\<^sub>R"
      using 1 by blast
    hence IHR: "?p\<^sub>0\<^sub>R \<in> set xs"
      by (meson in_set_dropD)

    let ?c\<^sub>0\<^sub>1 = "combine ?p\<^sub>0\<^sub>1\<^sub>L ?p\<^sub>0\<^sub>1\<^sub>R ?l ys"
    let ?c\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
    let ?c\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"

    have "(?c\<^sub>0, ?c\<^sub>1) = closest' (set xs) xs ys"
      using "1.prems" False by (auto simp add: Let_def split!: prod.splits if_splits)

    show ?thesis
      sorry
  qed
qed





text \<open>
  Closest' Pair of Points Algorithm
\<close>

definition closest :: "point list \<Rightarrow> (point * point)" where
  "closest ps = closest' (set ps) (sortX ps) (sortY ps)"

end
