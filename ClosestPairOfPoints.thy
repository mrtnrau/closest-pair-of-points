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

lemma sortedX_insort_key:
  "sortedX ps \<Longrightarrow> sortedX (insort_key fst p ps)"
  unfolding sortedX_def
  apply (induction ps)
   apply (auto)
  by (smt case_prod_conv fst_conv insertE le_cases order.trans set_insort_key)

lemma sortedX_sortX:
  "sortedX (sortX ps)"
  using sortX_def sortedX_def sortedX_insort_key
  by (induction ps) auto

lemma sortX_set:
  "set ps = set (sortX ps)"
  using sortX_def by simp

lemma sortX_length:
  "length ps = length (sortX ps)"
  using sortX_def by simp

lemma sortX_distinct:
  "distinct ps \<Longrightarrow> distinct (sortX ps)"
  using sortX_def by simp

lemma sortedY_insort_key:
  "sortedY ps \<Longrightarrow> sortedY (insort_key snd p ps)"
  unfolding sortedY_def
  apply (induction ps)
   apply (auto)
  by (smt case_prod_conv snd_conv insertE le_cases order.trans set_insort_key)

lemma sortedY_sortY:
  "sortedY (sortY ps)"
  using sortY_def sortedY_def sortedY_insort_key
  by (induction ps) auto

lemma sortY_set:
  "set ps = set (sortY ps)"
  using sortY_def by simp

lemma sortY_length:
  "length ps = length (sortY ps)"
  using sortY_def by simp

lemma sortY_distinct:
  "distinct ps \<Longrightarrow> distinct (sortY ps)"
  using sortY_def by simp

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  from assms have "sorted_wrt f (take n xs @ drop n xs)" by simp
  then show "sorted_wrt f (take n xs)" and "sorted_wrt f (drop n xs)"
    unfolding sorted_wrt_append by simp_all
qed

lemma sorted_wrt_filter:
  "sorted_wrt f xs \<Longrightarrow> sorted_wrt f (filter P xs)"
  by (induction xs) auto

lemma sorted_wrt_take_drop:
  assumes "sorted_wrt f xs"
  shows "\<forall>x \<in> set (take n xs). \<forall>y \<in> set (drop n xs). f x y"
  using assms by (metis append_take_drop_id sorted_wrt_append)

lemma sorted_wrt_take_less_hd_drop:
  assumes "sorted_wrt f xs" "n < length xs"
  shows "\<forall>x \<in> set (take n xs). f x (hd (drop n xs))"
proof -
  have "\<forall>i < n. f (xs!i) (xs!n)"
    using assms by (simp add: sorted_wrt_iff_nth_less)
  hence "\<forall>i < n. f (xs!i) (hd (drop n xs))"
    using assms(2) hd_drop_conv_nth by metis
  moreover have "\<forall>i < n. xs!i = (take n xs)!i"
    using assms(1) by simp
  ultimately have "\<forall>i < n. f ((take n xs)!i) (hd (drop n xs))"
    by metis
  moreover have "n = length (take n xs)"
    using assms(2) by simp
  ultimately show ?thesis
    by (metis in_set_conv_nth)
qed

lemma sorted_wrt_hd_drop_less_drop:
  assumes "sorted_wrt f xs" "n < length xs" "(\<And>x. f x x)"
  shows "\<forall>x \<in> set (drop n xs). f (hd (drop n xs)) x"
proof -
  let ?xs' = "drop n xs"
  have "sorted_wrt f ?xs'"
    using assms(1) by (simp add: sorted_wrt_drop)
  hence "\<forall>i < length ?xs'. f (?xs'!0) (?xs'!i)"
    using assms(2,3) sorted_wrt_nth_less by (metis linorder_neqE_nat not_less_zero)
  hence "\<forall>i < length ?xs'. f (hd ?xs') (?xs'!i)"
    by (simp add: hd_conv_nth)
  thus ?thesis
    by (metis in_set_conv_nth)
qed

lemma sortedX_take_less_hd_drop:
  assumes "sortedX ps" "n < length ps"
  shows "\<forall>p \<in> set (take n ps). fst p \<le> fst (hd (drop n ps))"
  using assms sorted_wrt_take_less_hd_drop[of "(\<lambda>(x\<^sub>0, _) (x\<^sub>1, _). x\<^sub>0 \<le> x\<^sub>1)"] sortedX_def by fastforce

lemma sortedX_hd_drop_less_drop:
  assumes "sortedX ps" "n < length ps"
  shows "\<forall>p \<in> set (drop n ps). fst (hd (drop n ps)) \<le> fst p"
  using assms sorted_wrt_hd_drop_less_drop[of "(\<lambda>(x\<^sub>0, _) (x\<^sub>1, _). x\<^sub>0 \<le> x\<^sub>1)"] sortedX_def by fastforce




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

lemma T3:
  "\<And>x. f x x \<Longrightarrow> sorted_wrt f (x # xs) \<Longrightarrow> \<forall>y \<in> set (x # xs). f x y"
  by simp

lemma T4:
  "\<And>x. f x x \<Longrightarrow> sorted_wrt f (x # xs) \<Longrightarrow> \<forall>y \<in> set (take n (x # xs)). f x y"
  using T3 by (metis in_set_takeD)

lemma T2:
  assumes "dist x x' < \<delta>" "sortedY (x # ys)" "x' \<in> set ys"
  shows "snd x' \<le> snd x + \<delta>"
proof -
  have "snd x \<le> snd x'"
    using sortedY_def assms(2,3) by auto
  moreover have "dist (snd x) (snd x') < \<delta>"
    using assms(1) dist_snd_le le_less_trans by blast
  ultimately show ?thesis
    by (simp add: dist_real_def)
qed

lemma T1:
  assumes "distinct (x # ys)" "sortedY (x # ys)" "0 < length ys" "0 < \<delta>"
  assumes "set (x # ys) = ys\<^sub>L \<union> ys\<^sub>R" "ys\<^sub>L \<inter> ys\<^sub>R = {}"
  assumes "\<forall>(x, y) \<in> set (x # ys). l - \<delta> \<le> x \<and> x \<le> l + \<delta>"
  assumes "\<forall>(x, y) \<in> ys\<^sub>L. x \<le> l" "\<forall>(x, y) \<in> ys\<^sub>R. l \<le> x"
  assumes "\<forall>x \<in> ys\<^sub>L. \<forall>y \<in> ys\<^sub>L. x \<noteq> y \<longrightarrow> \<delta> \<le> dist x y" "\<forall>x \<in> ys\<^sub>R. \<forall>y \<in> ys\<^sub>R. x \<noteq> y \<longrightarrow> \<delta> \<le> dist x y"
  assumes "x' \<in> set ys" "dist x x' < \<delta>"
  shows "x' \<in> set (take 7 ys)"
proof -
  define rectangle where "rectangle = cbox (l - \<delta>, snd x) (l + \<delta>, snd x + \<delta>)"
  define lsquare where "lsquare = cbox (l - \<delta>, snd x) (l, snd x + \<delta>)"
  define rsquare where "rsquare = cbox (l, snd x) (l + \<delta>, snd x + \<delta>)"
  define lys where "lys = filter (\<lambda>p. p \<in> lsquare \<and> p \<in> ys\<^sub>L) (x # ys)"
  define rys where "rys = filter (\<lambda>p. p \<in> rsquare \<and> p \<in> ys\<^sub>R) (x # ys)"

  note defs = rectangle_def lsquare_def rsquare_def lys_def rys_def

  have "l - \<delta> \<le> fst x'" "fst x' \<le> l + \<delta>"
    using assms(7,12) by auto
  moreover have "snd x \<le> snd x'"
    using sortedY_def assms(2,12) by auto
  moreover have "snd x' \<le> snd x + \<delta>"
    using T2 assms(2,12,13) by blast
  ultimately have 0: "x' \<in> rectangle"
    using mem_cbox_2D[of "l - \<delta>" "fst x'" "l + \<delta>" "snd x" "snd x'" "snd x + \<delta>"] defs by simp

  have 1: "rectangle = lsquare \<union> rsquare"
    using defs cbox_right_un by auto

  have "\<forall>p \<in> ys\<^sub>L. p \<in> rsquare \<longrightarrow> fst p = l"
    using rsquare_def assms(8) by auto
  hence X: "\<forall>p \<in> ys\<^sub>L. p \<in> rsquare \<longrightarrow> p \<in> lsquare"
    using rsquare_def lsquare_def by auto

  have "\<forall>p \<in> ys\<^sub>R. p \<in> lsquare \<longrightarrow> fst p = l"
    using lsquare_def assms(9) by auto
  hence Y: "\<forall>p \<in> ys\<^sub>R. p \<in> lsquare \<longrightarrow> p \<in> rsquare"
    using rsquare_def lsquare_def by auto

  have 2: "set (filter (\<lambda>p. p \<in> rectangle) (x # ys)) = set lys \<union> set rys"
  proof standard
    show "set (filter (\<lambda>p. p \<in> rectangle) (x # ys)) \<subseteq> set lys \<union> set rys"
      using 1 X Y assms(5) lys_def rys_def by auto
  next
    show "set lys \<union> set rys \<subseteq> set (filter (\<lambda>p. p \<in> rectangle) (x # ys))"
      using 1 lys_def rys_def by auto
  qed

  have "set lys \<subseteq> ys\<^sub>L"
    using defs by auto
  hence "sparse \<delta> (set lys)"
    using assms(10) sparse_def by blast
  moreover have "\<forall>p \<in> set lys. p \<in> lsquare"
    using defs by auto
  ultimately have 3: "card (set lys) \<le> 4"
    using max_points_square[of "set lys" "l - \<delta>" "snd x" \<delta>] assms(4) lsquare_def by auto

  have "set rys \<subseteq> ys\<^sub>R"
    using defs by auto
  hence "sparse \<delta> (set rys)"
    using assms(11) sparse_def by blast
  moreover have "\<forall>p \<in> set rys. p \<in> rsquare"
    using defs by auto
  ultimately have 4: "card (set rys) \<le> 4"
    using max_points_square[of "set rys" l "snd x" \<delta>] assms(4) rsquare_def by auto

  have 5: "card (set lys \<union> set rys) \<le> 8"
    using 3 4 card_Un_le[of "set lys" "set rys"] by simp

  have 6: "x' \<in> set lys \<union> set rys"
    using 0 2 assms(12) by (metis filter_set member_filter set_subset_Cons subsetCE)

  have 7: "set lys \<union> set rys \<subseteq> set (take 8 (x # ys))"
  proof (rule ccontr)
    assume *: "\<not> (set lys \<union> set rys \<subseteq> set (take 8 (x # ys)))"
    then obtain p where #: "p \<in> set (x # ys)" "p \<in> set lys \<union> set rys" "p \<notin> set (take 8 (x # ys))"
      using lys_def rys_def 2 by(smt filter_is_subset subsetCE subsetI)
    hence B: "p \<in> set (drop 8 (x # ys))"
      by (metis Un_iff append_take_drop_id set_append)

    hence "\<forall>a \<in> set (take 8 (x # ys)). \<forall>b \<in> set (drop 8 (x # ys)). snd a \<le> snd b"
      using sorted_wrt_take_drop[of "(\<lambda>(_, y\<^sub>0) (_, y\<^sub>1). y\<^sub>0 \<le> y\<^sub>1)" "x # ys" 8] assms(2) sortedY_def by fastforce
    hence C: "\<forall>q \<in> set (take 8 (x # ys)). snd q \<le> snd p"
      using B by simp

    have A: "p \<in> rectangle"
      using #(2) 1 \<open>\<forall>p \<in> set lys. p \<in> lsquare\<close> \<open>\<forall>p \<in> set rys. p \<in> rsquare\<close> by auto
    moreover have "\<forall>p \<in> set (take 8 (x # ys)). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
      using assms(7) by (metis (mono_tags, lifting) case_prod_unfold in_set_takeD)
    moreover have "\<forall>p \<in> set (take 8 (x # ys)). snd x \<le> snd p"
      using T4[of "(\<lambda>(_, y\<^sub>0) (_, y\<^sub>1). y\<^sub>0 \<le> y\<^sub>1)" x ys 8] assms(2) sortedY_def by fastforce
    moreover have "snd p \<le> snd x + \<delta>"
      using A rectangle_def by (metis mem_cbox_2D prod.collapse)
    moreover have "\<forall>p \<in> set (take 8 (x # ys)). snd p \<le> snd x + \<delta>"
      using C calculation by fastforce
    ultimately have "\<forall>q \<in> set (take 8 (x # ys)). q \<in> rectangle"
      using rectangle_def mem_cbox_2D by fastforce
    hence P: "{ p } \<union> set (take 8 (x # ys)) \<subseteq> set (filter (\<lambda>p. p \<in> rectangle) (x # ys))"
      using # A by (smt filter_set insertE insert_is_Un member_filter set_take_subset subsetCE subsetI)

    have "8 \<le> length (x # ys)"
      using #(1,3) nat_le_linear by fastforce
    hence Q: "length (take 8 (x # ys)) = 8"
      by simp

    have "finite { p }" "finite (set (take 8 (x # ys)))"
      by simp_all
    hence "card ({ p } \<union> set (take 8 (x # ys))) = card ({ p }) + card (set (take 8 (x # ys)))"
      using #(3) card_Un_disjoint by blast
    hence "card ({ p } \<union> set (take 8 (x # ys))) = 9"
      using assms(1) Q distinct_card[of "take 8 (x # ys)"] distinct_take[of "x # ys"] by fastforce
    moreover have "finite (set (filter (\<lambda>p. p \<in> rectangle) (x # ys)))"
      by simp
    ultimately have "9 \<le> card (set (filter (\<lambda>p. p \<in> rectangle) (x # ys)))"
      using P card_mono by metis
    hence "9 \<le> card (set lys \<union> set rys)"
      using 2 by simp
    thus False
      using 5 by simp
  qed 

  have "x' \<in> set (take 8 (x # ys))"
    using 6 7 by blast
  hence "x' \<in> set (take 7 ys)"
    using assms(1,12) by auto
  thus ?thesis
    by auto
qed
  

lemma find_closest_dist_take_7:
  assumes "distinct (x # ys)" "sortedY (x # ys)" "0 < length ys" "0 < \<delta>"
  assumes "set (x # ys) = ys\<^sub>L \<union> ys\<^sub>R" "ys\<^sub>L \<inter> ys\<^sub>R = {}"
  assumes "\<forall>(x, y) \<in> set (x # ys). l - \<delta> \<le> x \<and> x \<le> l + \<delta>"
  assumes "\<forall>(x, y) \<in> ys\<^sub>L. x \<le> l" "\<forall>(x, y) \<in> ys\<^sub>R. l \<le> x"
  assumes "\<forall>x \<in> ys\<^sub>L. \<forall>y \<in> ys\<^sub>L. x \<noteq> y \<longrightarrow> \<delta> \<le> dist x y" "\<forall>x \<in> ys\<^sub>R. \<forall>y \<in> ys\<^sub>R. x \<noteq> y \<longrightarrow> \<delta> \<le> dist x y"
  assumes "\<exists>x' \<in> set ys. dist x x' < \<delta>"
  shows "\<forall>x' \<in> set ys. dist x (find_closest x (take 7 ys)) \<le> dist x x'"
proof -
  have "dist x (find_closest x ys) < \<delta>"
    using assms(12) dual_order.strict_trans2 find_closest_dist by blast
  moreover have "find_closest x ys \<in> set ys"
    using assms(3) find_closest_set by blast
  ultimately have "find_closest x ys \<in> set (take 7 ys)"
    using T1[of x ys \<delta> ys\<^sub>L ys\<^sub>R l "find_closest x ys"] assms by blast
  moreover have "\<forall>p \<in> set (take 7 ys). dist x (find_closest x (take 7 ys)) \<le> dist x p"
    using find_closest_dist by blast
  ultimately have "\<forall>p \<in> set ys. dist x (find_closest x (take 7 ys)) \<le> dist x p"
    using find_closest_dist order.trans by blast
  thus ?thesis .
qed

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

lemma brute_force_closest_p0:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "p\<^sub>0 \<in> set ps"
  using assms
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: brute_force_closest.induct)
  apply (auto simp add: Let_def find_closest_set split!: prod.splits if_splits)
  done

lemma brute_force_closest_p1:
  assumes "1 < length ps" "(p\<^sub>0, p\<^sub>1) = brute_force_closest ps"
  shows "p\<^sub>1 \<in> set ps"
  using assms find_closest_set
  apply (induction ps arbitrary: p\<^sub>0 p\<^sub>1 rule: brute_force_closest.induct)
  apply (auto simp add: Let_def split!: prod.splits if_splits)
  apply (meson list.discI set_ConsD)
  done

lemma brute_force_closest_p0_ne_p1:
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
  Helper: Brute Force but only the 7 points following the one under question.
\<close>

(* combine brute_force_closest and closest_7 ? *)
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

lemma closest_7_dist:
  assumes "distinct ys" "sortedY ys" "1 < length ys" "0 < \<delta>"
  assumes "set ys = ys\<^sub>L \<union> ys\<^sub>R" "ys\<^sub>L \<inter> ys\<^sub>R = {}"
  assumes "\<forall>(x, y) \<in> set ys. l - \<delta> \<le> x \<and> x \<le> l + \<delta>"
  assumes "\<forall>(x, y )\<in> ys\<^sub>L. x \<le> l" "\<forall>(x, y) \<in> ys\<^sub>R. l \<le> x"
  assumes "\<forall>p\<^sub>0 \<in> ys\<^sub>L. \<forall>p\<^sub>1 \<in> ys\<^sub>L. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1" "\<forall>p\<^sub>0 \<in> ys\<^sub>R. \<forall>p\<^sub>1 \<in> ys\<^sub>R. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
  assumes "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
  assumes "(c\<^sub>0, c\<^sub>1) = closest_7 ys"
  shows "\<forall>p\<^sub>0 \<in> set ys. \<forall>p\<^sub>1 \<in> set ys. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1"
  using assms
proof (induction ys arbitrary: c\<^sub>0 c\<^sub>1 ys\<^sub>L ys\<^sub>R rule: closest_7.induct)
  case (3 p\<^sub>0 p\<^sub>1)

  have "(p\<^sub>0, p\<^sub>1) = closest_7 [p\<^sub>0, p\<^sub>1]"
    by simp
  moreover have "(c\<^sub>0, c\<^sub>1) = closest_7 [p\<^sub>0, p\<^sub>1]"
    using "3.prems"(13) by simp
  ultimately have "p\<^sub>0 = c\<^sub>0" "p\<^sub>1 = c\<^sub>1"
    by simp_all
  thus ?case
    by (simp add: dist_commute set_ConsD)
next
  case (4 x y z zs)

  let ?lys = "y # z # zs"
  let ?c\<^sub>0\<^sub>1 = "closest_7 ?lys"
  let ?lc\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
  let ?lc\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"
  let ?lp\<^sub>1 = "find_closest x (take 7 ?lys)"
  let ?lys\<^sub>L = "ys\<^sub>L - { x }"
  let ?lys\<^sub>R = "ys\<^sub>R - { x }"

  show ?case
  proof (cases "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ?lys \<and> p\<^sub>1 \<in> set ?lys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>")
    case True
    moreover have "distinct ?lys"
      using "4.prems"(1) by simp
    moreover have "sortedY ?lys"
      using "4.prems"(2) sorted_wrt.simps(2) sortedY_def by simp
    moreover have "1 < length ?lys"
      by simp
    moreover have "set ?lys = ?lys\<^sub>L \<union> ?lys\<^sub>R"
      using "4.prems"(1,5) by auto
    moreover have "?lys\<^sub>L \<inter> ?lys\<^sub>R = {}"
      using "4.prems"(6) by auto
    moreover have "\<forall>(x, y) \<in> set ?lys. l - \<delta> \<le> x \<and> x \<le> l + \<delta>"
      using "4.prems"(7) by simp
    moreover have "\<forall>(x, y) \<in> ?lys\<^sub>L. x \<le> l"
      using "4.prems"(8) by simp
    moreover have "\<forall>(x, y) \<in> ?lys\<^sub>R. l \<le> x"
      using "4.prems"(9) by simp
    moreover have "\<forall>p\<^sub>0 \<in> ?lys\<^sub>L. \<forall>p\<^sub>1 \<in> ?lys\<^sub>L. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using "4.prems"(10) by simp
    moreover have "\<forall>p\<^sub>0 \<in> ?lys\<^sub>R. \<forall>p\<^sub>1 \<in> ?lys\<^sub>R. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using "4.prems"(11) by simp
    moreover have "(?lc\<^sub>0, ?lc\<^sub>1) = closest_7 ?lys"
      by simp
    ultimately have *: "\<forall>p\<^sub>0 \<in> set ?lys. \<forall>p\<^sub>1 \<in> set ?lys. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist ?lc\<^sub>0 ?lc\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1"
      using "4.IH"[of ?lys\<^sub>L ?lys\<^sub>R ?lc\<^sub>0 ?lc\<^sub>1] "4.prems"(4) by fast
    hence #: "dist ?lc\<^sub>0 ?lc\<^sub>1 < \<delta>"
      using True by (meson le_less_trans)

    show ?thesis
    proof (cases "\<exists>x' \<in> set ?lys. dist x x' < \<delta>")
      case True
      hence 0: "\<forall>x' \<in> set ?lys. dist x ?lp\<^sub>1 \<le> dist x x'"
        using find_closest_dist_take_7[of x ?lys \<delta> ys\<^sub>L ys\<^sub>R l] "4.prems" by blast
      then show ?thesis
      proof cases
        assume asm: "dist ?lc\<^sub>0 ?lc\<^sub>1 \<le> dist x ?lp\<^sub>1"
        hence "(?lc\<^sub>0, ?lc\<^sub>1) = closest_7 (x # ?lys)"
          by (auto split: prod.splits)
        moreover have "c\<^sub>0 = ?lc\<^sub>0" "c\<^sub>1 = ?lc\<^sub>1"
          using "4.prems"(13) calculation by (metis prod.inject)+
        ultimately show ?thesis
          using * 0 asm by (smt dist_commute set_ConsD)
      next
        assume asm: "\<not> (dist ?lc\<^sub>0 ?lc\<^sub>1 \<le> dist x ?lp\<^sub>1)"
        hence "(x, ?lp\<^sub>1) = closest_7 (x # ?lys)"
          by (auto split: prod.splits)
        moreover have "c\<^sub>0 = x" "c\<^sub>1 = ?lp\<^sub>1"
          using "4.prems"(13) calculation by (metis prod.inject)+
        ultimately show ?thesis
          using * 0 asm by (smt dist_commute set_ConsD) 
      qed
    next
      case False
      hence 0: "\<forall>p\<^sub>0 \<in> set (x # ?lys). \<forall>p\<^sub>1 \<in> set (x # ?lys). p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist ?lc\<^sub>0 ?lc\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1"
        using * # by (smt dist_commute set_ConsD)
      hence "dist ?lc\<^sub>0 ?lc\<^sub>1 \<le> dist x ?lp\<^sub>1"
        by (smt "#" False find_closest_set length_greater_0_conv list.discI set_take_subset subsetCE take_Cons_numeral)
      hence "(?lc\<^sub>0, ?lc\<^sub>1) = closest_7 (x # ?lys)"
        by (auto split: prod.splits)
      moreover have "c\<^sub>0 = ?lc\<^sub>0" "c\<^sub>1 = ?lc\<^sub>1"
        using "4.prems"(13) calculation by (metis prod.inject)+
      ultimately show ?thesis
        using 0 by blast
    qed
  next
    case False
    hence "\<exists>x' \<in> set ?lys. dist x x' < \<delta>"
      using "4.prems"(12) by (metis dist_commute insert_iff list.set(2))
    hence "\<forall>x' \<in> set ?lys. dist x ?lp\<^sub>1 \<le> dist x x'"
      using find_closest_dist_take_7[of x ?lys \<delta> ys\<^sub>L ys\<^sub>R l] "4.prems" by blast
    moreover have "dist x ?lp\<^sub>1 < \<delta>"
      using \<open>\<exists>x'\<in>set ?lys. dist x x' < \<delta>\<close> calculation by auto
    ultimately have *: "\<forall>p\<^sub>0 \<in> set (x # ?lys). \<forall>p\<^sub>1 \<in> set (x # ?lys). p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist x ?lp\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1"
      using False by (smt dist_commute insert_iff list.simps(15))
    have "?lc\<^sub>0 \<in> set ?lys" "?lc\<^sub>1 \<in> set ?lys" "?lc\<^sub>0 \<noteq> ?lc\<^sub>1"
      using closest_7_set_p0[of ?lys ?lc\<^sub>0 ?lc\<^sub>1] apply simp
      using closest_7_set_p1[of ?lys ?lc\<^sub>0 ?lc\<^sub>1] apply simp
      using closest_7_set_p0_ne_p1[of ?lys ?lc\<^sub>0 ?lc\<^sub>1] by (metis "4.prems"(1) distinct.simps(2) le_eq_less_or_eq length_Cons lessI less_one nat.simps(3) not_less surjective_pairing)
    hence "dist x ?lp\<^sub>1 < dist ?lc\<^sub>0 ?lc\<^sub>1"
      by (smt False \<open>dist x (find_closest x (take 7 (y # z # zs))) < \<delta>\<close>)
    hence "(x, ?lp\<^sub>1) = closest_7 (x # ?lys)"
      by (auto split: prod.splits)
    moreover have "c\<^sub>0 = x" "c\<^sub>1 = ?lp\<^sub>1"
      using "4.prems"(13) calculation by (metis prod.inject)+
    ultimately show ?thesis
      using * by blast
  qed
qed auto




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

lemma divide_take:
  assumes "(xs', ys') = divide (take n) xs ys"
  shows "xs' = take n xs"
  using assms by (auto simp add: Let_def)

lemma divide_drop:
  assumes "(xs', ys') = divide (drop n) xs ys"
  shows "xs' = drop n xs"
  using assms by (auto simp add: Let_def)

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

lemma divide_sortedX_take:
  assumes "sortedX xs" "(xs', ys') = divide (take n) xs ys"
  shows "sortedX xs'"
  using assms sorted_wrt_take sortedX_def by (auto simp add: Let_def)

lemma divide_sortedX_drop:
  assumes "sortedX xs" "(xs', ys') = divide (drop n) xs ys"
  shows "sortedX xs'"
  using assms sorted_wrt_drop sortedX_def by (auto simp add: Let_def)

lemma divide_sortedY:
  assumes "sortedY ys" "(xs', ys') = divide f xs ys"
  shows "sortedY ys'"
  using assms sorted_wrt_take sortedY_def by (auto simp add: sorted_wrt_filter Let_def)

lemma divide_take_le_hd_drop:
  assumes "sortedX xs" "n < length xs" "(xs\<^sub>L, ys\<^sub>L) = divide (take n) xs ys" "(xs\<^sub>R, ys\<^sub>R) = divide (drop n) xs ys"
  shows "\<forall>p \<in> set xs\<^sub>L. fst p \<le> fst (hd xs\<^sub>R)"
  using assms divide_take divide_drop sortedX_take_less_hd_drop by blast

lemma divide_hd_drop_le_drop:
  assumes "sortedX xs" "n < length xs" "(xs\<^sub>R, ys\<^sub>R) = divide (drop n) xs ys"
  shows "\<forall>p \<in> set xs\<^sub>R. fst (hd xs\<^sub>R) \<le> fst p"
  using assms divide_take divide_drop sortedX_hd_drop_less_drop by blast




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

lemma combine_p0:
  assumes "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
  shows "p\<^sub>0 = p\<^sub>0\<^sub>L \<or> p\<^sub>0 = p\<^sub>0\<^sub>R \<or> p\<^sub>0 \<in> set ys"
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
    assume "length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>)"
    hence *: "(?c\<^sub>0, ?c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence "(p\<^sub>0, p\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using assms(1) by argo
    moreover have "?c\<^sub>0 = p\<^sub>0\<^sub>L \<or> ?c\<^sub>0 = p\<^sub>0\<^sub>R"
      by simp
    ultimately show ?thesis
      using * by blast
  next
    assume assm: "\<not> (length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>))"
    hence *: "(?p\<^sub>0, ?p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence #: "(p\<^sub>0, p\<^sub>1) = (?p\<^sub>0, ?p\<^sub>1)"
      using assms(1) by argo
    have "(?p\<^sub>0, ?p\<^sub>1) = closest_7 ?ys'"
      by auto
    hence "?p\<^sub>0 \<in> set ?ys'"
      using assm closest_7_set_p0[of ?ys' ?p\<^sub>0 ?p\<^sub>1] by linarith+
    thus ?thesis
      using * # by fastforce
  qed
qed

lemma combine_p1:
  assumes "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
  shows "p\<^sub>1 = p\<^sub>1\<^sub>L \<or> p\<^sub>1 = p\<^sub>1\<^sub>R \<or> p\<^sub>1 \<in> set ys"
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
    assume "length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>)"
    hence *: "(?c\<^sub>0, ?c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence "(p\<^sub>0, p\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using assms(1) by argo
    moreover have "?c\<^sub>1 = p\<^sub>1\<^sub>L \<or> ?c\<^sub>1 = p\<^sub>1\<^sub>R"
      by simp
    ultimately show ?thesis
      using * by blast
  next
    assume assm: "\<not> (length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>))"
    hence *: "(?p\<^sub>0, ?p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence #: "(p\<^sub>0, p\<^sub>1) = (?p\<^sub>0, ?p\<^sub>1)"
      using assms(1) by argo
    have "(?p\<^sub>0, ?p\<^sub>1) = closest_7 ?ys'"
      by auto
    hence "?p\<^sub>1 \<in> set ?ys'"
      using assm closest_7_set_p1[of ?ys' ?p\<^sub>0 ?p\<^sub>1] by linarith
    thus ?thesis
      using * # by fastforce
  qed
qed

lemma combine_p0_ne_p1:
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
    assume "length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>)"
    hence *: "(?c\<^sub>0, ?c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence "(p\<^sub>0, p\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using assms(1) by argo
    moreover have "?c\<^sub>0 \<noteq> ?c\<^sub>1"
      using assms(2,3) by auto
    ultimately show ?thesis
      using * by blast
  next
    assume assm: "\<not> (length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>))"
    hence *: "(?p\<^sub>0, ?p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence #: "(p\<^sub>0, p\<^sub>1) = (?p\<^sub>0, ?p\<^sub>1)"
      using assms(1) by argo
    have "distinct ?ys'" "2 \<le> length ?ys'"
      using assms(4) assm by auto
    moreover have "(?p\<^sub>0, ?p\<^sub>1) = closest_7 ?ys'"
      by auto
    ultimately have "?p\<^sub>0 \<noteq> ?p\<^sub>1"
      using closest_7_set_p0_ne_p1[of ?ys' ?p\<^sub>0 ?p\<^sub>1] by linarith
    thus ?thesis
      using * # by fastforce
  qed
qed

lemma AUX3:
  assumes "fst (p\<^sub>0 :: real * real) < l - \<delta>" "l + \<delta> < fst p\<^sub>1" 
  shows "2 * \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
proof -
  have "2 * \<delta> \<le> dist (fst p\<^sub>0) (fst p\<^sub>1)"
    using assms dist_real_def by auto
  also have "... \<le> dist p\<^sub>0 p\<^sub>1"
    using dist_fst_le by blast
  finally show ?thesis .
qed

lemma AUX2:
  "p \<in> set ys \<Longrightarrow> p \<notin> set (filter (\<lambda>(x, _). (l::real) - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys) \<Longrightarrow> fst p < l - \<delta> \<or> l + \<delta> < fst p"
  apply (induction ys)
   apply (auto split: if_splits)
  done

lemma AUX1:
  assumes "(p\<^sub>0 :: real * real) \<in> set ys" "p\<^sub>1 \<in> set ys" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>"
  assumes "ys\<^sub>L \<inter> ys\<^sub>R = {}" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p\<^sub>0 \<in> ys\<^sub>L. \<forall>p\<^sub>1 \<in> ys\<^sub>L. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1" "\<forall>p\<^sub>0 \<in> ys\<^sub>R. \<forall>p\<^sub>1 \<in> ys\<^sub>R. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>(x, _). l - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys"
  shows "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys'"
proof (rule ccontr)
  assume *: "\<not> (p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys')"

  have 0: "0 < \<delta>"
    using assms(3,4) le_less_trans zero_le_dist by blast

  consider (A) "p\<^sub>0 \<in> ys\<^sub>L \<and> p\<^sub>1 \<in> ys\<^sub>L" | (B) "p\<^sub>0 \<in> ys\<^sub>L \<and> p\<^sub>1 \<in> ys\<^sub>R" | (C) "p\<^sub>0 \<in> ys\<^sub>R \<and> p\<^sub>1 \<in> ys\<^sub>L" | (D) "p\<^sub>0 \<in> ys\<^sub>R \<and> p\<^sub>1 \<in> ys\<^sub>R"
    using assms(1,2,6) by auto
  thus False
  proof cases
    case A
    thus ?thesis
      using assms(3,4,7) by force
  next
    case B
    consider (B1) "p\<^sub>0 \<notin> set ys' \<and> p\<^sub>1 \<notin> set ys'"| (B2) "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<notin> set ys'" | (B3) "p\<^sub>0 \<notin> set ys' \<and> p\<^sub>1 \<in> set ys'"
      using * by blast
    then show ?thesis
    proof cases
      case B1
      hence "fst p\<^sub>0 < l - \<delta> \<or> l + \<delta> < fst p\<^sub>0" "fst p\<^sub>1 < l - \<delta> \<or> l + \<delta> < fst p\<^sub>1"
        using B AUX2 assms(1,2,11) by blast+
      hence "fst p\<^sub>0 < l - \<delta>" "l + \<delta> < fst p\<^sub>1"
        using assms(9,10) B by force+
      then show ?thesis
        using AUX3 assms(4) 0 by fastforce
    next
      case B2
      then show ?thesis sorry
    next
      case B3
      then show ?thesis sorry
    qed
  next
    case C
    then show ?thesis sorry
  next
    case D
    then show ?thesis
      using assms(3,4,8) by force
  qed
qed

lemma AUX0:
  assumes "\<exists>(p\<^sub>0 :: real * real) p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
  assumes "ys\<^sub>L \<inter> ys\<^sub>R = {}" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p\<^sub>0 \<in> ys\<^sub>L. \<forall>p\<^sub>1 \<in> ys\<^sub>L. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1" "\<forall>p\<^sub>0 \<in> ys\<^sub>R. \<forall>p\<^sub>1 \<in> ys\<^sub>R. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>(x, _). l - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys"
  shows "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys' \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
proof -
  obtain p\<^sub>0 p\<^sub>1 where *: "p\<^sub>0 \<in> set ys" "p\<^sub>1 \<in> set ys" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>"
    using assms(1) by blast
  hence "p\<^sub>0 \<in> set ys'" "p\<^sub>1 \<in> set ys'"
    using AUX1 assms(2,3,4,5,6,7,8) by blast+
  thus ?thesis
    using * by blast
qed

lemma AUX00:
  assumes "ys\<^sub>L \<inter> ys\<^sub>R = {}" "set (ys :: (real * real) list) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p\<^sub>0 \<in> ys\<^sub>L. \<forall>p\<^sub>1 \<in> ys\<^sub>L. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1" "\<forall>p\<^sub>0 \<in> ys\<^sub>R. \<forall>p\<^sub>1 \<in> ys\<^sub>R. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>(x, _). l - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys"
  shows "\<forall>x \<in> set ys. \<forall>y \<in> set ys. x \<noteq> y \<and> dist x y < \<delta> \<longrightarrow> x \<in> set ys' \<and> y \<in> set ys'"
proof (rule ccontr)
  assume "\<not> (\<forall>x \<in> set ys. \<forall>y \<in> set ys. x \<noteq> y \<and> dist x y < \<delta> \<longrightarrow> x \<in> set ys' \<and> y \<in> set ys')"
  hence "\<exists>x y. x \<in> set ys \<and> y \<in> set ys \<and> x \<noteq> y \<and> dist x y < \<delta> \<and> (x \<notin> set ys' \<or> x \<notin> set ys')"
    by (metis dist_commute)
  then obtain x y where "x \<in> set ys" "y \<in> set ys" "x \<noteq> y" "dist x y < \<delta>" and *: "x \<notin> set ys' \<or> x \<notin> set ys'"
    by blast
  hence "x \<in> set ys' \<and> y \<in> set ys'"
    using AUX1 assms by blast
  thus False
    using * by blast
qed

lemma BUX1:
  "set xs = A \<union> B \<Longrightarrow> set (filter P xs) = { x \<in> A. P x } \<union> { x \<in> B. P x}"
  apply (induction xs)
   apply (auto)
   apply (metis UnI1 insert_iff)
  by (metis UnI2 insert_iff)

lemma BUX0:
  "\<exists>x y. x \<in> set xs \<and> y \<in> set xs \<and> x \<noteq> y \<Longrightarrow> 2 \<le> length xs"
  apply (induction xs)
   apply (auto simp add: Suc_le_eq)
  done

lemma combine_dist:
  assumes "(p\<^sub>0, p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R"
  assumes "distinct ys" "sortedY ys"
  assumes "ys\<^sub>L \<inter> ys\<^sub>R = {}" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p\<^sub>0 \<in> ys\<^sub>L. \<forall>p\<^sub>1 \<in> ys\<^sub>L. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L \<le> dist p\<^sub>0 p\<^sub>1" "\<forall>p\<^sub>0 \<in> ys\<^sub>R. \<forall>p\<^sub>1 \<in> ys\<^sub>R. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R \<le> dist p\<^sub>0 p\<^sub>1"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  shows "\<forall>x \<in> set ys. \<forall>y \<in> set ys. x \<noteq> y \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist x y"
proof -
  define c\<^sub>0\<^sub>1 where "c\<^sub>0\<^sub>1 = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
  define c\<^sub>0 where "c\<^sub>0 = fst c\<^sub>0\<^sub>1"
  define c\<^sub>1 where "c\<^sub>1 = snd c\<^sub>0\<^sub>1"
  define \<delta> where "\<delta> = dist c\<^sub>0 c\<^sub>1"
  define ys' where "ys' = filter (\<lambda>(x, _). l - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys"
  define p\<^sub>0\<^sub>1 where "p\<^sub>0\<^sub>1 = closest_7 ys'"
  define lp\<^sub>0 where "lp\<^sub>0 = fst p\<^sub>0\<^sub>1"
  define lp\<^sub>1 where "lp\<^sub>1 = snd p\<^sub>0\<^sub>1"

  note defs = c\<^sub>0\<^sub>1_def c\<^sub>0_def c\<^sub>1_def \<delta>_def ys'_def p\<^sub>0\<^sub>1_def lp\<^sub>0_def lp\<^sub>1_def

  have 0: "\<forall>p\<^sub>0 \<in> ys\<^sub>L. \<forall>p\<^sub>1 \<in> ys\<^sub>L. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1" "\<forall>p\<^sub>0 \<in> ys\<^sub>R. \<forall>p\<^sub>1 \<in> ys\<^sub>R. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1"
    using assms(8,9) defs apply auto by force+

  show ?thesis
  proof (cases "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>")
    case True
    hence 1: "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys' \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
      using AUX0 0 assms defs by blast
    hence "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys' \<and> p\<^sub>0 \<noteq> p\<^sub>1"
      by blast
    hence 2: "2 \<le> length ys'"
      using BUX0[of ys'] by blast
    moreover have "distinct ys'"
      using assms(4) ys'_def by simp
    moreover have "sortedY ys'"
      using assms(5) sortedY_def sorted_wrt_filter ys'_def by blast
    moreover have "0 < \<delta>"
      using defs by (simp add: assms(2,3))
    moreover have "set ys' = { (x, y) \<in> ys\<^sub>L. l - \<delta> \<le> x \<and> x \<le> l + \<delta> } \<union> { (x, y) \<in> ys\<^sub>R. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }"
      using assms(7) BUX1 defs by auto
    moreover have "{ (x, y) \<in> ys\<^sub>L. l - \<delta> \<le> x \<and> x \<le> l + \<delta> } \<inter> { (x, y) \<in> ys\<^sub>R. l - \<delta> \<le> x \<and> x \<le> l + \<delta> } = {}"
      using assms(6) by blast
    moreover have "\<forall>(x, y) \<in> set ys'. l - \<delta> \<le> x \<and> x \<le> l + \<delta>"
      using defs by simp
    moreover have "\<forall>p\<^sub>0 \<in> { (x, y) \<in> ys\<^sub>L. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }. \<forall>p\<^sub>1 \<in> { (x, y) \<in> ys\<^sub>L. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using \<delta>_def 0 c\<^sub>0_def c\<^sub>1_def c\<^sub>0\<^sub>1_def by blast
    moreover have "\<forall>p\<^sub>0 \<in> { (x, y) \<in> ys\<^sub>R. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }. \<forall>p\<^sub>1 \<in> { (x, y) \<in> ys\<^sub>R. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using \<delta>_def 0 c\<^sub>0_def c\<^sub>1_def c\<^sub>0\<^sub>1_def by blast
    moreover have "\<forall>p \<in> { (x, y) \<in> ys\<^sub>L. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }. fst p \<le> l"
      using assms(10) by blast
    moreover have "\<forall>p \<in> { (x, y) \<in> ys\<^sub>R. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }. l \<le> fst p"
      using assms(11) by blast
    moreover have "(lp\<^sub>0, lp\<^sub>1) = closest_7 ys'"
      using defs by auto
    ultimately have "\<forall>x \<in> set ys'. \<forall>y \<in> set ys'. x \<noteq> y \<longrightarrow> dist lp\<^sub>0 lp\<^sub>1 \<le> dist x y"
      using closest_7_dist[of ys' \<delta> "{ (x, y) \<in> ys\<^sub>L. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }" "{ (x, y) \<in> ys\<^sub>R. l - \<delta> \<le> x \<and> x \<le> l + \<delta> }"] 1 by auto
    moreover have "\<forall>x \<in> set ys. \<forall>y \<in> set ys. x \<noteq> y \<and> dist x y < \<delta> \<longrightarrow> x \<in> set ys' \<and> y \<in> set ys'"
      using AUX00[of ys\<^sub>L ys\<^sub>R ys \<delta> l ys'] assms(6,7,8,9,10,11) 0 \<delta>_def ys'_def by auto
    ultimately have 3: "\<forall>x \<in> set ys. \<forall>y \<in> set ys. x \<noteq> y \<longrightarrow> dist lp\<^sub>0 lp\<^sub>1 \<le> dist x y"
      by (smt True)
    hence 4: "dist lp\<^sub>0 lp\<^sub>1 < \<delta>"
      using defs by (smt True)
    
    show ?thesis
    proof cases
      assume "length ys' < 2 \<or> \<not> (dist lp\<^sub>0 lp\<^sub>1 < \<delta>)"
      thus ?thesis
        using 2 4 by linarith
    next
      assume #: "\<not> (length ys' < 2 \<or> \<not> (dist lp\<^sub>0 lp\<^sub>1 < \<delta>))"
      hence *: "(lp\<^sub>0, lp\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
        using defs by (auto simp add: Let_def split!: prod.splits)
      moreover have "lp\<^sub>0 = p\<^sub>0" "lp\<^sub>1 = p\<^sub>1" 
        using assms(1) calculation by (metis (no_types, lifting) prod.inject)+
      ultimately show ?thesis
        using 3 by blast
    qed
  next
    case False
    hence 1: "\<forall>x \<in> set ys. \<forall>y \<in> set ys. x \<noteq> y \<longrightarrow> dist c\<^sub>0 c\<^sub>1 \<le> dist x y"
      using 0 defs by (meson leI)
    then show ?thesis
    proof cases
      assume "length ys' < 2 \<or> \<not> (dist lp\<^sub>0 lp\<^sub>1 < \<delta>)"
      hence *: "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
        using defs by (auto simp add: Let_def split!: prod.splits)
      hence "(p\<^sub>0, p\<^sub>1) = (c\<^sub>0, c\<^sub>1)"
        using assms(1) by argo
      thus ?thesis
        using * 1 by blast
    next
      assume #: "\<not> (length ys' < 2 \<or> \<not> (dist lp\<^sub>0 lp\<^sub>1 < \<delta>))"
      hence *: "(lp\<^sub>0, lp\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
        using defs by (auto simp add: Let_def split!: prod.splits)
      have "(lp\<^sub>0, lp\<^sub>1) = closest_7 ys'"
        using defs by auto
      hence "lp\<^sub>0 \<in> set ys'" "lp\<^sub>1 \<in> set ys'"
        using # defs closest_7_set_p0[of ys' lp\<^sub>0 lp\<^sub>1] closest_7_set_p1[of ys' lp\<^sub>0 lp\<^sub>1] by linarith+
      hence "lp\<^sub>0 \<in> set ys" "lp\<^sub>1 \<in> set ys"
        using filter_is_subset defs by fast+
      moreover have "lp\<^sub>0 \<noteq> lp\<^sub>1"
        using combine_p0_ne_p1 * assms(2,3,4) by blast
      ultimately have "\<delta> \<le> dist lp\<^sub>0 lp\<^sub>1"
        using 1 defs by blast
      thus ?thesis
        using # by argo
    qed
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




lemma closest'_p0_p1:
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
      using "1.prems"(1,4) brute_force_closest_p0 brute_force_closest_p1 brute_force_closest_p0_ne_p1 by simp
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

    let ?p\<^sub>0\<^sub>1 = "combine ?p\<^sub>0\<^sub>1\<^sub>L ?p\<^sub>0\<^sub>1\<^sub>R (fst (hd ?xs\<^sub>R)) ys"
    let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
    let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

    have "set ?xs\<^sub>L = set ?ys\<^sub>L"
      using "1.prems"(3) divide_set by (metis prod.collapse set_take_subset)
    moreover have "distinct ?xs\<^sub>L" "distinct ?ys\<^sub>L"
      using "1.prems"(4,5) divide_distinct_xs divide_distinct_ys by (metis distinct_take distinct_drop prod.collapse)+
    moreover have "length ?xs\<^sub>L < ?n" "1 < length ?xs\<^sub>L"
      using False divide_length_take by (metis prod.collapse not_le_imp_less)+
    moreover have "(?p\<^sub>0\<^sub>L, ?p\<^sub>1\<^sub>L) = closest' (set ?xs\<^sub>L) ?xs\<^sub>L ?ys\<^sub>L"
      by simp
    ultimately have "?p\<^sub>0\<^sub>L \<in> set ?xs\<^sub>L" "?p\<^sub>1\<^sub>L \<in> set ?xs\<^sub>L" "?p\<^sub>0\<^sub>L \<noteq> ?p\<^sub>1\<^sub>L"
      using 1 by blast+
    hence IHL: "?p\<^sub>0\<^sub>L \<in> set xs" "?p\<^sub>1\<^sub>L \<in> set xs" "?p\<^sub>0\<^sub>L \<noteq> ?p\<^sub>1\<^sub>L"
      using divide_subset by (meson prod.collapse set_take_subset subset_code(1))+

    have "set ?xs\<^sub>R = set ?ys\<^sub>R"
      using "1.prems"(3) divide_set by (metis prod.collapse set_drop_subset)
    moreover have "distinct ?xs\<^sub>R" "distinct ?ys\<^sub>R"
      using "1.prems"(4,5) divide_distinct_xs divide_distinct_ys by (metis distinct_take distinct_drop prod.collapse)+
    moreover have "length ?xs\<^sub>R < ?n" "1 < length ?xs\<^sub>R"
      using False divide_length_drop by (metis prod.collapse not_le_imp_less)+
    moreover have "(?p\<^sub>0\<^sub>R, ?p\<^sub>1\<^sub>R) = closest' (set ?xs\<^sub>R) ?xs\<^sub>R ?ys\<^sub>R"
      by simp
    ultimately have "?p\<^sub>0\<^sub>R \<in> set ?xs\<^sub>R" "?p\<^sub>1\<^sub>R \<in> set ?xs\<^sub>R" "?p\<^sub>0\<^sub>R \<noteq> ?p\<^sub>1\<^sub>R"
      using 1 by blast+
    hence IHR: "?p\<^sub>0\<^sub>R \<in> set xs" "?p\<^sub>1\<^sub>R \<in> set xs" "?p\<^sub>0\<^sub>R \<noteq> ?p\<^sub>1\<^sub>R"
      using divide_subset by (meson prod.collapse set_drop_subset subset_code(1))+

    have "(?p\<^sub>0, ?p\<^sub>1) = closest' (set xs) xs ys"
      using "1.prems" False by (auto simp add: closest'_simps Let_def)
    moreover have "?p\<^sub>0 \<in> set xs" "?p\<^sub>1 \<in> set xs" "?p\<^sub>0 \<noteq> ?p\<^sub>1"
      using combine_p0 "1.prems"(3) IHL(1) IHR(1) apply (metis (no_types, lifting) prod.collapse)
      using combine_p1 "1.prems"(3) IHL(2) IHR(2) apply (metis (no_types, lifting) prod.collapse)
      using combine_p0_ne_p1 "1.prems"(5) IHL(3) IHR(3) by (metis (no_types, lifting) prod.collapse)
    ultimately show ?thesis
      using "1.prems"(2) by (metis Pair_inject)
  qed
qed

lemma closest'_dist:
  assumes "1 < length xs" "(p\<^sub>0, p\<^sub>1) = closest' (set xs) xs ys"
  assumes "set xs = set ys" "distinct xs" "distinct ys"
  assumes "sortedX xs" "sortedY ys"
  shows "\<forall>x \<in> set xs. \<forall>y \<in> set xs. x \<noteq> y \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist x y"
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
      using "1.prems"(1,4) brute_force_closest_dist cpop_dist by metis
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

    let ?l = "fst (hd ?xs\<^sub>R)"
    let ?p\<^sub>0\<^sub>1 = "combine ?p\<^sub>0\<^sub>1\<^sub>L ?p\<^sub>0\<^sub>1\<^sub>R ?l ys"
    let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
    let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

    have LXSL: "length ?xs\<^sub>L < ?n" "1 < length ?xs\<^sub>L"
      using False divide_length_take by (metis prod.collapse not_le_imp_less)+
    moreover have XYSL: "set ?xs\<^sub>L = set ?ys\<^sub>L"
      using "1.prems"(3) divide_set by (metis prod.collapse set_take_subset)
    moreover have DXYSL: "distinct ?xs\<^sub>L" "distinct ?ys\<^sub>L"
      using "1.prems"(4,5) divide_distinct_xs divide_distinct_ys by (metis distinct_take distinct_drop prod.collapse)+
    moreover have L: "(?p\<^sub>0\<^sub>L, ?p\<^sub>1\<^sub>L) = closest' (set ?xs\<^sub>L) ?xs\<^sub>L ?ys\<^sub>L"
      by simp
    moreover have "sortedX ?xs\<^sub>L" "sortedY ?ys\<^sub>L"
      using "1.prems"(6,7) divide_sortedX_take divide_sortedY prod.collapse by blast+
    ultimately have "\<forall>x \<in> set ?xs\<^sub>L. \<forall>y \<in> set ?xs\<^sub>L. x \<noteq> y \<longrightarrow> dist ?p\<^sub>0\<^sub>L ?p\<^sub>1\<^sub>L \<le> dist x y"
      using 1 by blast
    hence IHL: "\<forall>x \<in> set ?ys\<^sub>L. \<forall>y \<in> set ?ys\<^sub>L. x \<noteq> y \<longrightarrow> dist ?p\<^sub>0\<^sub>L ?p\<^sub>1\<^sub>L \<le> dist x y"
      using XYSL by blast

    have LXSR: "length ?xs\<^sub>R < ?n" "1 < length ?xs\<^sub>R"
      using False divide_length_drop by (metis prod.collapse not_le_imp_less)+
    moreover have XYSR: "set ?xs\<^sub>R = set ?ys\<^sub>R"
      using "1.prems"(3) divide_set by (metis prod.collapse set_drop_subset)
    moreover have DXYSR: "distinct ?xs\<^sub>R" "distinct ?ys\<^sub>R"
      using "1.prems"(4,5) divide_distinct_xs divide_distinct_ys by (metis distinct_take distinct_drop prod.collapse)+
    moreover have "sortedX ?xs\<^sub>R" "sortedY ?ys\<^sub>R"
      using "1.prems"(6,7) divide_sortedX_drop divide_sortedY prod.collapse by blast+
    moreover have R: "(?p\<^sub>0\<^sub>R, ?p\<^sub>1\<^sub>R) = closest' (set ?xs\<^sub>R) ?xs\<^sub>R ?ys\<^sub>R"
      by simp
    ultimately have "\<forall>x \<in> set ?xs\<^sub>R. \<forall>y \<in> set ?xs\<^sub>R. x \<noteq> y \<longrightarrow> dist ?p\<^sub>0\<^sub>R ?p\<^sub>1\<^sub>R \<le> dist x y"
      using 1 by blast
    hence IHR: "\<forall>x \<in> set ?ys\<^sub>R. \<forall>y \<in> set ?ys\<^sub>R. x \<noteq> y \<longrightarrow> dist ?p\<^sub>0\<^sub>R ?p\<^sub>1\<^sub>R \<le> dist x y"
      using XYSR by blast

    have N2: "?n div 2 < length xs"
      using "1.prems"(1) by linarith
    have "\<forall>p \<in> set ?xs\<^sub>L. fst p \<le> ?l"
      using N2 "1.prems"(6) divide_take_le_hd_drop prod.collapse by blast
    hence YSLL: "\<forall>p \<in> set ?ys\<^sub>L. fst p \<le> ?l"
      using XYSL by blast
    have "\<forall>p \<in> set ?xs\<^sub>R. ?l \<le> fst p"
      using N2 "1.prems"(6) divide_hd_drop_le_drop prod.collapse by blast
    hence LYSR: "\<forall>p \<in> set ?ys\<^sub>R. ?l \<le> fst p"
      using XYSR by blast

    have "set ?xs\<^sub>L \<inter> set ?xs\<^sub>R = {}" "set xs = set ?xs\<^sub>L \<union> set ?xs\<^sub>R"
      using "1.prems"(4) divide_take divide_drop by (metis append_take_drop_id distinct_append set_append prod.collapse)+
    hence SYSLR: "set ?ys\<^sub>L \<inter> set ?ys\<^sub>R = {}" "set ys = set ?ys\<^sub>L \<union> set ?ys\<^sub>R"
      using "1.prems"(3) XYSL XYSR by blast+

    have "?p\<^sub>0\<^sub>L \<noteq> ?p\<^sub>1\<^sub>L" "?p\<^sub>0\<^sub>R \<noteq> ?p\<^sub>1\<^sub>R"
      using closest'_p0_p1 L R DXYSL DXYSR LXSL LXSR XYSL XYSR by blast+
    hence "\<forall>x \<in> set ys. \<forall>y \<in> set ys. x \<noteq> y \<longrightarrow> dist ?p\<^sub>0 ?p\<^sub>1 \<le> dist x y"
      using combine_dist[of ?p\<^sub>0 ?p\<^sub>1 ?p\<^sub>0\<^sub>L ?p\<^sub>1\<^sub>L ?p\<^sub>0\<^sub>R ?p\<^sub>1\<^sub>R ?l ys "set ?ys\<^sub>L" "set ?ys\<^sub>R"] "1.prems"(5,7) IHL IHR YSLL LYSR SYSLR by (smt prod.collapse)
    hence "\<forall>x \<in> set xs. \<forall>y \<in> set xs. x \<noteq> y \<longrightarrow> dist ?p\<^sub>0 ?p\<^sub>1 \<le> dist x y"
      using "1.prems"(3) by blast
    moreover have "(?p\<^sub>0, ?p\<^sub>1) = closest' (set xs) xs ys"
      using "1.prems" False by (auto simp add: closest'_simps Let_def)
    moreover have "?p\<^sub>0 = p\<^sub>0" "?p\<^sub>1 = p\<^sub>1"
      using "1.prems"(2) calculation by (metis Pair_inject)+
    ultimately show ?thesis
      by blast
  qed
qed




text \<open>
  Closest Pair of Points Algorithm
\<close>

definition closest :: "point list \<Rightarrow> (point * point)" where
  "closest ps = closest' (set ps) (sortX ps) (sortY ps)"

theorem closest_set:
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
    using closest'_p0_p1 by simp_all
qed

theorem closest_dist:
  assumes "1 < length ps" "distinct ps" "(p\<^sub>0, p\<^sub>1) = closest ps"
  shows "\<forall>x \<in> set ps. \<forall>y \<in> set ps. x \<noteq> y \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist x y"
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
  moreover have "sortedX (sortX ps)"
    using sortedX_sortX by blast
  moreover have "sortedY (sortY ps)"
    using sortedY_sortY by blast
  ultimately show "\<forall>x \<in> set ps. \<forall>y \<in> set ps. x \<noteq> y \<longrightarrow> dist p\<^sub>0 p\<^sub>1 \<le> dist x y"
    using closest'_dist[of "sortX ps" p\<^sub>0 p\<^sub>1 "sortY ps"] by presburger
qed

end
