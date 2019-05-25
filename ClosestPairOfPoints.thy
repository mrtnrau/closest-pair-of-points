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
  Helper: Find the closest point to \<open>p\<^sub>0\<close> within ps.
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

lemma sortX_set:
  "set ps = set (sortX ps)"
  using sortX_def by simp

lemma sortX_length:
  "length ps = length (sortX ps)"
  using sortX_def by simp

lemma sortX_distinct:
  "distinct ps \<Longrightarrow> distinct (sortX ps)"
  using sortX_def by simp

lemma sortY_set:
  "set ps = set (sortY ps)"
  using sortY_def by simp

lemma sortY_length:
  "length ps = length (sortY ps)"
  using sortY_def by simp

lemma sortY_distinct:
  "distinct ps \<Longrightarrow> distinct (sortY ps)"
  using sortY_def by simp




text \<open>
  Random Auxiliary Lemmas
\<close>




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

lemma closest_7_set_p0:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = closest_7 ps"
  shows "p\<^sub>0 \<in> set ps"
  using assms
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: closest_7.induct)
  apply (auto simp add: Let_def find_closest_set split!: prod.splits if_splits)
  done

lemma closest_7_set_p1:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = closest_7 ps"
  shows "p\<^sub>1 \<in> set ps"
  using assms find_closest_set
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: closest_7.induct)
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (meson in_set_takeD list.discI set_ConsD)
  done

lemma closest_7_set_p0_ne_p1:
  assumes "distinct ps" "1 < length ps" "(p\<^sub>0, p\<^sub>1) = closest_7 ps"
  shows "p\<^sub>0 \<noteq> p\<^sub>1"
  using assms find_closest_ne
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: closest_7.induct)
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (metis in_set_takeD list.discI Pair_inject set_ConsD)+
  done




text \<open>
  Closest' Pair of Points Algorithm
\<close>

fun divide :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> (point list * point list)" where
  "divide f xs ys = (
    let xs' = f xs in
    let ps = set xs' in
    let ys' = filter (\<lambda>p. p \<in> ps) ys in
    (xs', ys')
  )"

lemma divide_set:
  assumes "set xs = set ys" "set (f xs) \<subseteq> set xs" "(xs', ys') = divide f xs ys"
  shows "set xs' = set ys'"
  using assms by (auto simp add: Let_def)

lemma divide_subset:
  assumes "set (f xs) \<subseteq> set xs" "(xs', ys') = divide f xs ys"
  shows "set xs' \<subseteq> set xs"
  using assms by (auto simp add: Let_def)

lemma divide_distinct_xs:
  assumes "(xs', ys') = divide f xs ys" "distinct (f xs)"
  shows "distinct xs'"
  using assms by (auto simp add: Let_def)

lemma divide_distinct_ys:
  assumes "(xs', ys') = divide f xs ys" "distinct ys"
  shows "distinct ys'"
  using assms by (auto simp add: Let_def)

lemma divide_length_take:
  assumes "n = length xs div 2" "3 < length xs" "(xs', ys') = divide (take n) xs ys"
  shows "length xs' < length xs"
    and "1 < length xs'"
  using assms by (auto simp add: Let_def)

lemma divide_length_drop:
  assumes "n = length xs div 2" "3 < length xs" "(xs', ys') = divide (drop n) xs ys"
  shows "length xs' < length xs"
    and "1 < length xs'"
  using assms by (auto simp add: Let_def)




fun combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let \<delta> = dist c\<^sub>0 c\<^sub>1 in
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

lemma combine_set_p0:
  "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys \<Longrightarrow> p\<^sub>0 = p\<^sub>0\<^sub>L \<or> p\<^sub>0 = p\<^sub>0\<^sub>R \<or> p\<^sub>0 \<in> set ys"
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (metis (mono_tags, lifting) closest_7_set_p0 filter_is_subset less_trans linorder_neqE_nat one_less_numeral_iff semiring_norm(76) subsetCE)+
  done

lemma combine_set_p1:
  "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys \<Longrightarrow> p\<^sub>1 = p\<^sub>1\<^sub>L \<or> p\<^sub>1 = p\<^sub>1\<^sub>R \<or> p\<^sub>1 \<in> set ys"
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (metis (mono_tags, lifting) closest_7_set_p1 filter_is_subset less_trans linorder_neqE_nat one_less_numeral_iff semiring_norm(76) subsetCE)+
  done

lemma combine_set_p0_ne_p1:
  assumes "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R" "distinct ys"
  shows "p\<^sub>0 \<noteq> p\<^sub>1"
proof -
  let ?c\<^sub>0\<^sub>1 = "(if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
  let ?c\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
  let ?c\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"
  let ?\<delta> = "dist ?c\<^sub>0 ?c\<^sub>1"
  let ?ys' = "filter (\<lambda>(x, _). l - ?\<delta> \<le> x \<and> x \<le> l + ?\<delta>) ys"
  let ?p\<^sub>0\<^sub>1 = "closest_7 ?ys'"
  let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
  let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

  show ?thesis
  proof cases
    assume *: "length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>)"
    have "?c\<^sub>0 \<noteq> ?c\<^sub>1"
      using assms(2,3) by auto
    moreover have "(?c\<^sub>0, ?c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      using * by (auto simp add: Let_def split!: prod.splits)
    moreover have "(p\<^sub>0, p\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using assms(1) calculation by auto
    ultimately show ?thesis
      by blast
  next
    assume *: "\<not> (length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>))"
    hence "distinct ?ys'" "2 \<le> length ?ys'"
      using assms(4) by auto
    hence "?p\<^sub>0 \<noteq> ?p\<^sub>1"
      using closest_7_set_p0_ne_p1 by auto
    moreover have "(?p\<^sub>0, ?p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      using * by (auto simp add: Let_def split!: prod.splits)
    moreover have "(p\<^sub>0, p\<^sub>1) = (?p\<^sub>0, ?p\<^sub>1)"
      using assms(1) calculation by auto
    ultimately show ?thesis
      by blast
  qed
qed




function (sequential) closest' :: "point set \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "closest' ps xs ys = (
    let n = length xs in
    if n \<le> 3 then
      brute_force_closest xs
    else
      let (xs\<^sub>L, ys\<^sub>L) = divide (take (n div 2)) xs ys in
      let (xs\<^sub>R, ys\<^sub>R) = divide (drop (n div 2)) xs ys in

      let (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest' (set xs\<^sub>L) xs\<^sub>L ys\<^sub>L in
      let (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest' (set xs\<^sub>R) xs\<^sub>R ys\<^sub>R in

      combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) (fst (hd xs\<^sub>R)) ys 
  )"
  by pat_completeness auto
termination closest'
  apply (relation "Wellfounded.measure (\<lambda>(_, xs, _). length xs)")
  apply (auto simp add: Let_def)
  done

declare closest_7.simps divide.simps combine.simps [simp del]

lemma closest'_simps:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "closest' ps xs ys = (
    let (xs\<^sub>L, ys\<^sub>L) = divide (take (n div 2)) xs ys in
    let (xs\<^sub>R, ys\<^sub>R) = divide (drop (n div 2)) xs ys in
    let (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest' (set xs\<^sub>L) xs\<^sub>L ys\<^sub>L in
    let (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest' (set xs\<^sub>R) xs\<^sub>R ys\<^sub>R in
    combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) (fst (hd xs\<^sub>R)) ys
  )"
  using assms by (auto simp add: Let_def)

declare closest'.simps [simp del]




lemma closest'_set:
  assumes "1 < length xs" "(p\<^sub>0, p\<^sub>1) = closest' (set xs) xs ys"
  assumes "set xs = set ys" "distinct xs" "distinct ys"
  shows "p\<^sub>0 \<in> set xs \<and> p\<^sub>1 \<in> set xs \<and> p\<^sub>0 \<noteq> p\<^sub>1"
  using assms
proof (induction xs arbitrary: ys p\<^sub>0 p\<^sub>1 rule: length_induct)
  case (1 xs)

  let ?n = "length xs"

  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(p\<^sub>0, p\<^sub>1) = brute_force_closest xs"
      using "1.prems"(2) closest'.simps by simp
    thus ?thesis
      using "1.prems"(1,4) brute_force_closest_set_p0 brute_force_closest_set_p1 brute_force_closest_set_p0_ne_p1 by simp
  next
    case False

    let ?xys\<^sub>L = "divide (take (?n div 2)) xs ys"
    let ?xs\<^sub>L = "fst ?xys\<^sub>L"
    let ?ys\<^sub>L = "snd ?xys\<^sub>L"
    let ?xys\<^sub>R = "divide (drop (?n div 2)) xs ys"
    let ?xs\<^sub>R = "fst ?xys\<^sub>R"
    let ?ys\<^sub>R = "snd ?xys\<^sub>R"

    let ?p\<^sub>0\<^sub>1\<^sub>L = "closest' (set ?xs\<^sub>L) ?xs\<^sub>L ?ys\<^sub>L"
    let ?p\<^sub>0\<^sub>L = "fst ?p\<^sub>0\<^sub>1\<^sub>L"
    let ?p\<^sub>1\<^sub>L = "snd ?p\<^sub>0\<^sub>1\<^sub>L"
    let ?p\<^sub>0\<^sub>1\<^sub>R = "closest' (set ?xs\<^sub>R) ?xs\<^sub>R ?ys\<^sub>R"
    let ?p\<^sub>0\<^sub>R = "fst ?p\<^sub>0\<^sub>1\<^sub>R"
    let ?p\<^sub>1\<^sub>R = "snd ?p\<^sub>0\<^sub>1\<^sub>R"

    have "set ?xs\<^sub>L = set ?ys\<^sub>L"
      using "1.prems"(3) divide_set by (smt prod.collapse set_take_subset)
    moreover have "distinct ?xs\<^sub>L" "distinct ?ys\<^sub>L"
      using "1.prems"(4,5) divide_distinct_xs divide_distinct_ys by (smt distinct_take distinct_drop prod.collapse)+
    moreover have "length ?xs\<^sub>L < ?n" "1 < length ?xs\<^sub>L"
      using False divide_length_take by (smt prod.collapse not_le_imp_less)+
    moreover have "(?p\<^sub>0\<^sub>L, ?p\<^sub>1\<^sub>L) = closest' (set ?xs\<^sub>L) ?xs\<^sub>L ?ys\<^sub>L"
      by simp
    ultimately have "?p\<^sub>0\<^sub>L \<in> set ?xs\<^sub>L" "?p\<^sub>1\<^sub>L \<in> set ?xs\<^sub>L" "?p\<^sub>0\<^sub>L \<noteq> ?p\<^sub>1\<^sub>L"
      using 1 by blast+
    hence IHL: "?p\<^sub>0\<^sub>L \<in> set xs" "?p\<^sub>1\<^sub>L \<in> set xs" "?p\<^sub>0\<^sub>L \<noteq> ?p\<^sub>1\<^sub>L"
      using divide_subset by (meson prod.collapse set_take_subset subset_code(1))+

    have "set ?xs\<^sub>R = set ?ys\<^sub>R"
      using "1.prems"(3) divide_set by (smt prod.collapse set_drop_subset)
    moreover have "distinct ?xs\<^sub>R" "distinct ?ys\<^sub>R"
      using "1.prems"(4,5) divide_distinct_xs divide_distinct_ys by (smt distinct_take distinct_drop prod.collapse)+
    moreover have "length ?xs\<^sub>R < ?n" "1 < length ?xs\<^sub>R"
      using False divide_length_drop by (smt prod.collapse not_le_imp_less)+
    moreover have "(?p\<^sub>0\<^sub>R, ?p\<^sub>1\<^sub>R) = closest' (set ?xs\<^sub>R) ?xs\<^sub>R ?ys\<^sub>R"
      by simp
    ultimately have "?p\<^sub>0\<^sub>R \<in> set ?xs\<^sub>R" "?p\<^sub>1\<^sub>R \<in> set ?xs\<^sub>R" "?p\<^sub>0\<^sub>R \<noteq> ?p\<^sub>1\<^sub>R"
      using 1 by blast+
    hence IHR: "?p\<^sub>0\<^sub>R \<in> set xs" "?p\<^sub>1\<^sub>R \<in> set xs" "?p\<^sub>0\<^sub>R \<noteq> ?p\<^sub>1\<^sub>R"
      using divide_subset by (meson prod.collapse set_drop_subset subset_code(1))+

    let ?p\<^sub>0\<^sub>1 = "combine ?p\<^sub>0\<^sub>1\<^sub>L ?p\<^sub>0\<^sub>1\<^sub>R (fst (hd ?xs\<^sub>R)) ys"
    let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
    let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

    have "(?p\<^sub>0, ?p\<^sub>1) = closest' (set xs) xs ys"
      using "1.prems" False by (auto simp add: closest'_simps Let_def)
    moreover have "?p\<^sub>0 \<in> set xs" "?p\<^sub>1 \<in> set xs" "?p\<^sub>0 \<noteq> ?p\<^sub>1"
      using combine_set_p0 "1.prems"(3) IHL(1) IHR(1) apply (metis (no_types, lifting) prod.collapse)
      using combine_set_p1 "1.prems"(3) IHL(2) IHR(2) apply (metis (no_types, lifting) prod.collapse)
      using combine_set_p0_ne_p1 "1.prems"(5) IHL(3) IHR(3) by (metis (no_types, lifting) prod.collapse)
    ultimately show ?thesis
      using "1.prems"(2) by (metis Pair_inject)
  qed
qed





text \<open>
  Closest' Pair of Points Algorithm
\<close>

definition closest :: "point list \<Rightarrow> (point * point)" where
  "closest ps = closest' (set ps) (sortX ps) (sortY ps)"

lemma closest_set:
  assumes "1 < length ps" "distinct ps" "(p\<^sub>0, p\<^sub>1) = closest ps"
  shows "p\<^sub>0 \<in> set ps"
    and "p\<^sub>1 \<in> set ps"
    and "p\<^sub>0 \<noteq> p\<^sub>1"
proof -
  have "set (sortX ps) = set (sortY ps)"
    using sortX_set sortY_set by blast
  moreover have "set ps = set (sortX ps)"
    using sortX_set by simp
  moreover have "1 < length (sortX ps)"
    using assms(1) sortX_length by simp
  moreover have "distinct (sortX ps)" "distinct (sortY ps)"
    using sortX_distinct sortY_distinct assms(2) by simp_all
  moreover have "(p\<^sub>0, p\<^sub>1) = closest' (set ps) (sortX ps) (sortY ps)"
    using closest_def assms(3) by simp
  ultimately show "p\<^sub>0 \<in> set ps" "p\<^sub>1 \<in> set ps" "p\<^sub>0 \<noteq> p\<^sub>1"
    using closest'_set by simp_all
qed

end
