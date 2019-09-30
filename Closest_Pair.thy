theory Closest_Pair
  imports "HOL-Analysis.Analysis"
begin

section "Closest Pair Of Points Functional Correctness"

type_synonym point = "real * real"

subsection "Splitting"

fun split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at n [] = ([], [])"
| "split_at n (x#xs) = (
    case n of
      0 \<Rightarrow> ([], x#xs)
    | Suc m \<Rightarrow>
      let (xs', ys') = split_at m xs in
      (x#xs', ys')
  )"

lemma split_at_take_drop_conv:
  "split_at n xs = (take n xs, drop n xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

declare split_at.simps [simp del]

lemma set_take_drop_i_le_j:
  "i \<le> j \<Longrightarrow> set xs = set (take j xs) \<union> set (drop i xs)"
proof (induction xs arbitrary: i j)
  case (Cons x xs)
  show ?case
  proof (cases "i = 0")
    case True
    thus ?thesis
      using set_take_subset by force
  next
    case False
    hence "set xs = set (take (j-1) xs) \<union> set (drop (i-1) xs)"
      by (simp add: Cons diff_le_mono)
    moreover have "set (take j (x#xs)) = insert x (set (take (j-1) xs))"
      using False Cons.prems by (auto simp: take_Cons')
    moreover have "set (drop i (x#xs)) = set (drop (i-1) xs)"
      using False Cons.prems by (auto simp: drop_Cons')
    ultimately show ?thesis
      by auto
  qed
qed simp

lemma set_take_drop:
  "set xs = set (take n xs) \<union> set (drop n xs)"
  using set_take_drop_i_le_j by fast


subsection "Merging and Sorting"

definition sortedX :: "point list \<Rightarrow> bool" where
  "sortedX ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1) ps"

definition sortedY :: "point list \<Rightarrow> bool" where
  "sortedY ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1) ps"

fun merge :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge f (x#xs) (y#ys) = (
    if f x \<le> f y then
      x # merge f xs (y#ys)
    else
      y # merge f (x#xs) ys
  )"
| "merge f [] ys = ys"
| "merge f xs [] = xs"

lemma length_merge:
  "length (merge f xs ys) = length xs + length ys"
  by (induction f xs ys rule: merge.induct) auto

lemma set_merge:
  "set (merge f xs ys) = set xs \<union> set ys"
  by (induction f xs ys rule: merge.induct) auto

lemma distinct_merge:
  assumes "set xs \<inter> set ys = {}" "distinct xs" "distinct ys"
  shows "distinct (merge f xs ys)"
  using assms by (induction f xs ys rule: merge.induct) (auto simp: set_merge)

lemma sorted_merge:
  assumes "P = (\<lambda>x y. f x \<le> f y)"
  shows "sorted_wrt P (merge f xs ys) \<longleftrightarrow> sorted_wrt P xs \<and> sorted_wrt P ys"
  using assms by (induction f xs ys rule: merge.induct) (auto simp: set_merge)


function msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "msort f [] = []"
| "msort f [x] = [x]"
| "msort f (x # y # xs') = ( 
    let xs = x # y # xs' in
    let n = length xs div 2 in
    let (l, r) = split_at n xs in
    merge f (msort f l) (msort f r)
  )"
  by pat_completeness auto
termination msort
  apply (relation "Wellfounded.measure (\<lambda>(_, xs). length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

lemma sorted_wrt_msort:
  "sorted_wrt (\<lambda>x y. f x \<le> f y) (msort f xs)"
  by (induction f xs rule: msort.induct) (auto simp: split_at_take_drop_conv sorted_merge)

lemma set_msort:
  "set (msort f xs) = set xs"
  apply (induction f xs rule: msort.induct)
  apply (simp_all add: set_merge split_at_take_drop_conv)
  using set_take_drop by (metis list.simps(15))

lemma length_msort:
  "length (msort f xs) = length xs"
  by (induction f xs rule: msort.induct) (auto simp: length_merge split_at_take_drop_conv)

lemma distinct_msort:
  "distinct xs \<Longrightarrow> distinct (msort f xs)"
proof (induction f xs rule: msort.induct)
  case (3 f x y xs)
  let ?xs' = "x # y # xs"
  obtain l r where lr_def: "(l, r) = split_at (length ?xs' div 2) ?xs'"
    by (metis surj_pair)
  have "distinct l" "distinct r"
    using "3.prems" split_at_take_drop_conv distinct_take distinct_drop lr_def by (metis prod.sel)+
  hence "distinct (msort f l)" "distinct (msort f r)"
    using "3.IH" lr_def by auto
  moreover have "set l \<inter> set r = {}"
    using "3.prems" split_at_take_drop_conv lr_def by (metis append_take_drop_id distinct_append prod.sel)
  ultimately show ?case
    using lr_def by (auto simp: distinct_merge set_msort split: prod.splits)
qed auto


definition sortX :: "point list \<Rightarrow> point list" where
  "sortX ps = msort fst ps"

definition sortY :: "point list \<Rightarrow> point list" where
  "sortY ps = msort snd ps"

lemma sortX:
  shows sortedX_sortX: "sortedX (sortX ps)" and
        set_sortX: "set (sortX ps) = set ps" and
        length_sortX: "length (sortX ps) = length ps" and
        distinct_sortX: "distinct ps \<Longrightarrow> distinct (sortX ps)"
  unfolding sortX_def sortedX_def
  by (auto simp: sorted_wrt_msort set_msort length_msort distinct_msort)

lemma sortY:
  shows sortedY_sortY: "sortedY (sortY ps)" and
        set_sortY: "set (sortY ps) = set ps" and
        length_sortY: "length (sortY ps) = length ps" and
        distinct_sortY: "distinct ps \<Longrightarrow> distinct (sortY ps)"
  unfolding sortY_def sortedY_def
  by (auto simp: sorted_wrt_msort set_msort length_msort distinct_msort)

lemma sorted_wrt_filter:
  "sorted_wrt f xs \<Longrightarrow> sorted_wrt f (filter P xs)"
  by (induction xs) auto

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  from assms have "sorted_wrt f (take n xs @ drop n xs)" by simp
  then show "sorted_wrt f (take n xs)" and "sorted_wrt f (drop n xs)"
    unfolding sorted_wrt_append by simp_all
qed

lemma sorted_wrt_take_drop:
  "sorted_wrt f xs \<Longrightarrow> \<forall>x \<in> set (take n xs). \<forall>y \<in> set (drop n xs). f x y"
  using sorted_wrt_append[of f "take n xs" "drop n xs"] by simp

lemma sorted_wrt_hd_less:
  assumes "sorted_wrt f xs" "\<And>x. f x x"
  shows "\<forall>x \<in> set xs. f (hd xs) x"
  using assms by (cases xs) auto

lemma sorted_wrt_hd_less_take:
  assumes "sorted_wrt f (x # xs)" "\<And>x. f x x"
  shows "\<forall>y \<in> set (take n (x # xs)). f x y"
  using assms sorted_wrt_hd_less in_set_takeD by fastforce

lemma sorted_wrt_take_less_hd_drop:
  assumes "sorted_wrt f xs" "n < length xs"
  shows "\<forall>x \<in> set (take n xs). f x (hd (drop n xs))"
  using sorted_wrt_take_drop assms by fastforce

lemma sorted_wrt_hd_drop_less_drop:
  assumes "sorted_wrt f xs" "\<And>x. f x x"
  shows "\<forall>x \<in> set (drop n xs). f (hd (drop n xs)) x"
  using assms sorted_wrt_drop sorted_wrt_hd_less by blast

lemma sortedX_take_less_hd_drop:
  assumes "sortedX ps" "n < length ps"
  shows "\<forall>p \<in> set (take n ps). fst p \<le> fst (hd (drop n ps))"
  using assms sorted_wrt_take_less_hd_drop[of "\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1"] sortedX_def by fastforce

lemma sortedX_hd_drop_less_drop:
  assumes "sortedX ps"
  shows "\<forall>p \<in> set (drop n ps). fst (hd (drop n ps)) \<le> fst p"
  using assms sorted_wrt_hd_drop_less_drop[of "\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1"] sortedX_def by fastforce


subsection "Sparsity"

definition min_dist :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "min_dist \<delta> ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1)"

lemma min_dist_identity:
  assumes "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)" "\<forall>p \<in> set ps. dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set (p\<^sub>0 # ps))"
  using assms by (simp add: dist_commute min_dist_def)

lemma min_dist_update:
  assumes "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  assumes "dist p\<^sub>0 p\<^sub>1 \<le> dist c\<^sub>0 c\<^sub>1" "\<forall>p \<in> set ps. dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "min_dist (dist p\<^sub>0 p\<^sub>1) (set (p\<^sub>0 # ps))"
  using assms apply (auto simp: dist_commute min_dist_def) by force+


subsection "Finding Closest Point"

fun find_closest :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest p\<^sub>0 [] = undefined"
| "find_closest p\<^sub>0 [p] = p"
| "find_closest p\<^sub>0 (p # ps) = (
    let c = find_closest p\<^sub>0 ps in
    if dist p\<^sub>0 p < dist p\<^sub>0 c then
      p
    else
      c
  )"

lemma find_closest_dist:
  "\<forall>p \<in> set ps. dist p\<^sub>0 (find_closest p\<^sub>0 ps) \<le> dist p\<^sub>0 p"
  by (induction p\<^sub>0 ps rule: find_closest.induct) (auto simp: Let_def)

lemma find_closest_set:
  "0 < length ps \<Longrightarrow> find_closest p\<^sub>0 ps \<in> set ps"
  by (induction p\<^sub>0 ps rule: find_closest.induct) (auto simp: Let_def)

lemma find_closest_ne:
  "0 < length ps \<Longrightarrow> p\<^sub>0 \<notin> set ps \<Longrightarrow> p\<^sub>0 \<noteq> find_closest p\<^sub>0 ps"
  by (induction p\<^sub>0 ps rule: find_closest.induct) (auto simp: Let_def)


subsection "Closest Pair Brute Force Algorithm"

fun closest_pair_bf :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_bf [] = undefined"
| "closest_pair_bf [p\<^sub>0] = undefined"
| "closest_pair_bf [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_bf (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps in
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

lemma closest_pair_bf_c0:
  "2 \<le> length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  apply (auto simp: find_closest_set Let_def split: if_splits prod.splits)
  done

lemma closest_pair_bf_c1:
  "2 \<le> length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>1 \<in> set ps"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  apply (auto simp: find_closest_set Let_def split: if_splits prod.splits)
  using find_closest_set apply fastforce
  done

lemma closest_pair_bf_c0_ne_c1:
  "2 \<le> length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  apply (auto simp add: find_closest_ne Let_def split: if_splits prod.splits)
  done

lemmas closest_pair_bf_c0_c1 = closest_pair_bf_c0
  closest_pair_bf_c1 closest_pair_bf_c0_ne_c1

lemma closest_pair_bf_dist:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ps"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  let ?ps = "p\<^sub>1 # p\<^sub>2 # ps"
  obtain c\<^sub>0' c\<^sub>1' where c\<^sub>0\<^sub>1_def: "(c\<^sub>0', c\<^sub>1') = closest_pair_bf ?ps"
    using prod.collapse by blast
  hence IH: "min_dist (dist c\<^sub>0' c\<^sub>1') (set ?ps)"
    using 4 by simp
  have *: "\<forall>p \<in> set ?ps. dist p\<^sub>0 (find_closest p\<^sub>0 ?ps) \<le> dist p\<^sub>0 p"
    using find_closest_dist by blast
  show ?case
  proof (cases "dist c\<^sub>0' c\<^sub>1' \<le> dist p\<^sub>0 (find_closest p\<^sub>0 ?ps)")
    case True
    hence "\<forall>p \<in> set ?ps. dist c\<^sub>0' c\<^sub>1' \<le> dist p\<^sub>0 p"
      using * by auto
    hence "min_dist (dist c\<^sub>0' c\<^sub>1') (set (p\<^sub>0 # ?ps))"
      using min_dist_identity IH by blast
    thus ?thesis
      using True "4.prems" c\<^sub>0\<^sub>1_def by (auto split: prod.splits)
  next
    case False
    hence "dist p\<^sub>0 (find_closest p\<^sub>0 ?ps) \<le> dist c\<^sub>0' c\<^sub>1'"
      by simp
    hence "min_dist (dist p\<^sub>0 (find_closest p\<^sub>0 ?ps)) (set (p\<^sub>0 # ?ps))"
      using min_dist_update IH * by blast
    moreover have "(c\<^sub>0, c\<^sub>1) = (p\<^sub>0, (find_closest p\<^sub>0 ?ps))"
      using False "4.prems" c\<^sub>0\<^sub>1_def by (auto split: prod.splits)
    ultimately show ?thesis
      by simp
  qed
qed (auto simp: dist_commute min_dist_def)


subsection "2D-Boxes and Points"

lemma cbox_2D: 
  "cbox (x\<^sub>0::real, y\<^sub>0::real) (x\<^sub>1, y\<^sub>1) = { (x, y). x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1}"
  by fastforce

lemma mem_cbox_2D:
  "x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1 \<longleftrightarrow> (x::real, y::real) \<in> cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1)"
  by fastforce

lemma cbox_top_un:
  assumes "y\<^sub>0 \<le> y\<^sub>1" "y\<^sub>1 \<le> y\<^sub>2"
  shows "cbox (x\<^sub>0::real, y\<^sub>0::real) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>0, y\<^sub>1) (x\<^sub>1, y\<^sub>2) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>2)"
  using assms by auto

lemma cbox_right_un:
  assumes "x\<^sub>0 \<le> x\<^sub>1" "x\<^sub>1 \<le> x\<^sub>2"
  shows "cbox (x\<^sub>0::real, y\<^sub>0::real) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>1, y\<^sub>0) (x\<^sub>2, y\<^sub>1) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>2, y\<^sub>1)"
  using assms by auto

lemma cbox_max_dist:
  assumes "p\<^sub>0 = (x, y)" "p\<^sub>1 = (x + \<delta>, y + \<delta>)"
  assumes "(x\<^sub>0, y\<^sub>0) \<in> cbox p\<^sub>0 p\<^sub>1" "(x\<^sub>1, y\<^sub>1) \<in> cbox p\<^sub>0 p\<^sub>1" "0 \<le> \<delta>"
  shows "dist (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<le> sqrt 2 * \<delta>"
proof -
  have X: "dist x\<^sub>0 x\<^sub>1 \<le> \<delta>"
    using assms dist_real_def by auto
  have Y: "dist y\<^sub>0 y\<^sub>1 \<le> \<delta>"
    using assms dist_real_def by auto

  have "dist (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) = sqrt ((dist x\<^sub>0 x\<^sub>1)\<^sup>2 + (dist y\<^sub>0 y\<^sub>1)\<^sup>2)"
    using dist_Pair_Pair by auto
  also have "... \<le> sqrt (\<delta>\<^sup>2 + (dist y\<^sub>0 y\<^sub>1)\<^sup>2)"
    using X power_mono by fastforce
  also have "... \<le> sqrt (\<delta>\<^sup>2 + \<delta>\<^sup>2)"
    using Y power_mono by fastforce
  also have "... = sqrt 2 * sqrt (\<delta>\<^sup>2)"
    using real_sqrt_mult by simp
  also have "... = sqrt 2 * \<delta>"
    using assms(5) by simp
  finally show ?thesis .
qed


subsection "Pigeonhole Argument"

lemma card_le_1_if_pairwise_eq:
  assumes "\<forall>x \<in> S. \<forall>y \<in> S. x = y"
  shows "card S \<le> 1"
proof (rule ccontr)
  assume "\<not> card S \<le> 1"
  hence "2 \<le> card S"
    by simp
  then obtain T where *: "T \<subseteq> S \<and> card T = 2"
    using ex_card by metis
  then obtain x y where "x \<in> T \<and> y \<in> T \<and> x \<noteq> y"
    using card_2_exists by metis
  then show False
    using * assms by blast
qed

lemma card_Int_if_either_in:
  assumes "\<forall>x \<in> S. \<forall>y \<in> S. x = y \<or> x \<notin> T \<or> y \<notin> T" 
  shows "card (S \<inter> T) \<le> 1"
proof (rule ccontr)
  assume "\<not> (card (S \<inter> T) \<le> 1)"
  then obtain x y where *: "x \<in> S \<inter> T \<and> y \<in> S \<inter> T \<and> x \<noteq> y"
    by (meson card_le_1_if_pairwise_eq)
  hence "x \<in> T" "y \<in> T"
    by simp_all
  moreover have "x \<notin> T \<or> y \<notin> T"
    using assms * by auto
  ultimately show False
    by blast
qed

lemma card_Int_Un_le_Sum_card_Int:
  assumes "finite S"
  shows "card (A \<inter> \<Union>S) \<le> (\<Sum>B \<in> S. card (A \<inter> B))"
  using assms
proof (induction "card S" arbitrary: S)
  case (Suc n)
  then obtain B T where *: "S = { B } \<union> T" "card T = n" "B \<notin> T"
    by (metis card_Suc_eq Suc_eq_plus1 insert_is_Un)
  hence "card (A \<inter> \<Union>S) = card (A \<inter> \<Union>({ B } \<union> T))"
    by blast
  also have "... \<le> card (A \<inter> B) + card (A \<inter> \<Union>T)"
    by (simp add: card_Un_le inf_sup_distrib1)
  also have "... \<le> card (A \<inter> B) + (\<Sum>B \<in> T. card (A \<inter> B))"
    using Suc * by simp
  also have "... \<le> (\<Sum>B \<in> S. card (A \<inter> B))"
    using Suc.prems * by simp
  finally show ?case .
qed simp

lemma pigeonhole:
  assumes "finite T" "S \<subseteq> \<Union>T" "card T < card S"
  shows "\<exists>x \<in> S. \<exists>y \<in> S. \<exists>X \<in> T. x \<noteq> y \<and> x \<in> X \<and> y \<in> X"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> S. \<exists>y \<in> S. \<exists>X \<in> T. x \<noteq> y \<and> x \<in> X \<and> y \<in> X)"
  hence *: "\<forall>X \<in> T. card (S \<inter> X) \<le> 1"
    using card_Int_if_either_in by metis
  have "card T < card (S \<inter> \<Union>T)"
    using Int_absorb2 assms by fastforce
  also have "... \<le> (\<Sum>X \<in> T. card (S \<inter> X))"
    using assms(1) card_Int_Un_le_Sum_card_Int by blast
  also have "... \<le> card T"
    using * sum_mono by fastforce
  finally show False by simp
qed

subsection "\<delta> Sparse Points within a Square"

lemma max_points_square:
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + \<delta>, y + \<delta>)" "min_dist \<delta> ps" "0 < \<delta>"
  shows "card ps \<le> 4"
proof (rule ccontr)
  assume *: "\<not> (card ps \<le> 4)"

  let ?x' = "x + \<delta> / 2"
  let ?y' = "y + \<delta> / 2"

  let ?ll = "cbox ( x ,  y ) (?x'   , ?y'   )"
  let ?lu = "cbox ( x , ?y') (?x'   ,  y + \<delta>)"
  let ?rl = "cbox (?x',  y ) ( x + \<delta>, ?y'   )"
  let ?ru = "cbox (?x', ?y') ( x + \<delta>,  y + \<delta>)"

  let ?sq = "{ ?ll, ?lu, ?rl, ?ru }"

  have card_le_4: "card ?sq \<le> 4"
    by (simp add: card_insert_le_m1)

  have "cbox (x, y) (?x', y + \<delta>) = ?ll \<union> ?lu"
    using cbox_top_un assms(3) by auto
  moreover have "cbox (?x', y) (x + \<delta>, y + \<delta>) = ?rl \<union> ?ru"
    using cbox_top_un assms(3) by auto
  moreover have "cbox (x, y) (?x', y + \<delta>) \<union> cbox (?x', y) (x + \<delta>, y + \<delta>) = cbox (x, y) (x + \<delta>, y + \<delta>)"
    using cbox_right_un assms(3) by simp
  ultimately have "?ll \<union> ?lu \<union> ?rl \<union> ?ru = cbox (x, y) (x + \<delta>, y + \<delta>)"
    by blast

  hence "ps \<subseteq> \<Union>?sq"
    using assms(1) by auto
  moreover have "card ?sq < card ps"
    using * card_insert_le_m1 card_le_4 by simp
  moreover have "finite ?sq"
    by simp
  ultimately have "\<exists>p\<^sub>0 \<in> ps. \<exists>p\<^sub>1 \<in> ps. \<exists>S \<in> ?sq. (p\<^sub>0 \<noteq> p\<^sub>1 \<and> p\<^sub>0 \<in> S \<and> p\<^sub>1 \<in> S)"
    using pigeonhole[of ?sq ps] by blast
  then obtain S p\<^sub>0 p\<^sub>1 where #: "p\<^sub>0 \<in> ps" "p\<^sub>1 \<in> ps" "S \<in> ?sq" "p\<^sub>0 \<noteq> p\<^sub>1" "p\<^sub>0 \<in> S" "p\<^sub>1 \<in> S"
    by blast

  have D: "0 \<le> \<delta> / 2"
    using assms(3) by simp
  have LL: "\<forall>p\<^sub>0 \<in> ?ll. \<forall>p\<^sub>1 \<in> ?ll. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
    using cbox_max_dist[of "(x, y)" x y "(?x', ?y')" "\<delta> / 2"] D by auto
  have LU: "\<forall>p\<^sub>0 \<in> ?lu. \<forall>p\<^sub>1 \<in> ?lu. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
    using cbox_max_dist[of "(x, ?y')" x ?y' "(?x', y + \<delta>)" "\<delta> / 2"] D by auto
  have RL: "\<forall>p\<^sub>0 \<in> ?rl. \<forall>p\<^sub>1 \<in> ?rl. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
    using cbox_max_dist[of "(?x', y)" ?x' y "(x + \<delta>, ?y')" "\<delta> / 2"] D by auto
  have RU: "\<forall>p\<^sub>0 \<in> ?ru. \<forall>p\<^sub>1 \<in> ?ru. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
    using cbox_max_dist[of "(?x', ?y')" ?x' ?y' "(x + \<delta>, y + \<delta>)" "\<delta> / 2"] D by auto

  have "\<forall>p\<^sub>0 \<in> S. \<forall>p\<^sub>1 \<in> S. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (\<delta> / 2)"
    using # LL LU RL RU by blast
  hence "dist p\<^sub>0 p\<^sub>1 \<le> (sqrt 2 / 2) * \<delta>"
    using # by simp
  moreover have "(sqrt 2 / 2) * \<delta> < \<delta>"
    using sqrt2_less_2 assms(3) by simp
  ultimately have "dist p\<^sub>0 p\<^sub>1 < \<delta>"
    by simp
  moreover have "\<delta> \<le> dist p\<^sub>0 p\<^sub>1"
    using assms(2) # min_dist_def by simp
  ultimately show False
    by simp
qed


subsection "Closest Pair Combine Algorithm"

lemma closest_pair_in_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "y\<^sub>1 \<in> set ys" "dist y\<^sub>0 y\<^sub>1 < \<delta>"
  shows "y\<^sub>1 \<in> set (take 7 ys)"
proof -
  define YS where "YS = y\<^sub>0 # ys"
  define R where "R = cbox (l - \<delta>, snd y\<^sub>0) (l + \<delta>, snd y\<^sub>0 + \<delta>)"
  define RYS where "RYS = R \<inter> set YS"
  define LSQ where "LSQ = cbox (l - \<delta>, snd y\<^sub>0) (l, snd y\<^sub>0 + \<delta>)"
  define LSQYS where "LSQYS = LSQ \<inter> ys\<^sub>L"
  define RSQ where "RSQ = cbox (l, snd y\<^sub>0) (l + \<delta>, snd y\<^sub>0 + \<delta>)"
  define RSQYS where "RSQYS = RSQ \<inter> ys\<^sub>R"
  note defs = YS_def R_def RYS_def LSQ_def LSQYS_def RSQ_def RSQYS_def

  have "R = LSQ \<union> RSQ"
    using defs cbox_right_un by auto
  moreover have "\<forall>p \<in> ys\<^sub>L. p \<in> RSQ \<longrightarrow> p \<in> LSQ"
    using RSQ_def LSQ_def assms(6) by auto
  moreover have "\<forall>p \<in> ys\<^sub>R. p \<in> LSQ \<longrightarrow> p \<in> RSQ"
    using RSQ_def LSQ_def assms(7) by auto
  ultimately have "RYS = LSQYS \<union> RSQYS"
    using LSQYS_def RSQYS_def YS_def RYS_def assms(4) by blast

  have "min_dist \<delta> LSQYS"
    using assms(8) LSQYS_def min_dist_def by simp
  hence CLSQYS: "card LSQYS \<le> 4"
    using max_points_square[of LSQYS "l - \<delta>" "snd y\<^sub>0" \<delta>] assms(3) LSQ_def LSQYS_def by auto

  have "min_dist \<delta> RSQYS"
    using assms(9) RSQYS_def min_dist_def by simp
  hence CRSQYS: "card RSQYS \<le> 4"
    using max_points_square[of RSQYS l "snd y\<^sub>0" \<delta>] assms(3) RSQ_def RSQYS_def by auto

  have CRYS: "card RYS \<le> 8"
    using CLSQYS CRSQYS card_Un_le[of LSQYS RSQYS] \<open>RYS = LSQYS \<union> RSQYS\<close> by auto

  have "RYS \<subseteq> set (take 8 YS)"
  proof (rule ccontr)
    assume "\<not> (RYS \<subseteq> set (take 8 YS))"
    then obtain p where *: "p \<in> set YS" "p \<in> RYS" "p \<notin> set (take 8 YS)" "p \<in> R"
      using RYS_def by auto

    have "\<forall>p\<^sub>0 \<in> set (take 8 YS). \<forall>p\<^sub>1 \<in> set (drop 8 YS). snd p\<^sub>0 \<le> snd p\<^sub>1"
      using sorted_wrt_take_drop[of "\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1" YS 8] assms(2) sortedY_def YS_def by fastforce
    hence "\<forall>p' \<in> set (take 8 YS). snd p' \<le> snd p"
      using append_take_drop_id set_append Un_iff *(1,3) by metis
    moreover have "snd p \<le> snd y\<^sub>0 + \<delta>"
      using \<open>p \<in> R\<close> R_def by (metis mem_cbox_2D prod.collapse)
    ultimately have "\<forall>p \<in> set (take 8 YS). snd p \<le> snd y\<^sub>0 + \<delta>"
      by fastforce
    moreover have "\<forall>p \<in> set (take 8 YS). snd y\<^sub>0 \<le> snd p"
      using sorted_wrt_hd_less_take[of "\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1" y\<^sub>0 ys 8] assms(2) sortedY_def YS_def by fastforce
    moreover have "\<forall>p \<in> set (take 8 YS). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
      using assms(5) YS_def by (meson in_set_takeD)
    ultimately have "\<forall>p \<in> set (take 8 YS). p \<in> R"
      using R_def mem_cbox_2D by fastforce

    hence "set (take 8 YS) \<subseteq> RYS"
      using RYS_def set_take_subset by fastforce
    hence NINE: "{ p } \<union> set (take 8 YS) \<subseteq> RYS"
      using * by simp

    have "8 \<le> length YS"
      using *(1,3) nat_le_linear by fastforce
    hence "length (take 8 YS) = 8"
      by simp

    have "finite { p }" "finite (set (take 8 YS))"
      by simp_all
    hence "card ({ p } \<union> set (take 8 YS)) = card ({ p }) + card (set (take 8 YS))"
      using *(3) card_Un_disjoint by blast
    hence "card ({ p } \<union> set (take 8 YS)) = 9"
      using assms(1) \<open>length (take 8 YS) = 8\<close> distinct_card[of "take 8 YS"] distinct_take[of YS] YS_def by fastforce
    moreover have "finite RYS"
      using RYS_def by simp
    ultimately have "9 \<le> card RYS"
      using NINE card_mono by metis
    thus False
      using CRYS by simp
  qed 

  have "dist (snd y\<^sub>0) (snd y\<^sub>1) < \<delta>"
    using assms(11) dist_snd_le le_less_trans by blast
  hence "snd y\<^sub>1 < snd y\<^sub>0 + \<delta>"
    by (simp add: dist_real_def)
  moreover have "l - \<delta> \<le> fst y\<^sub>1" "fst y\<^sub>1 \<le> l + \<delta>"
    using assms(5,10) by auto
  moreover have "snd y\<^sub>0 \<le> snd y\<^sub>1"
    using sortedY_def assms(2,10) by auto
  ultimately have "y\<^sub>1 \<in> R"
    using mem_cbox_2D[of "l - \<delta>" "fst y\<^sub>1" "l + \<delta>" "snd y\<^sub>0" "snd y\<^sub>1" "snd y\<^sub>0 + \<delta>"] defs by simp
  moreover have "y\<^sub>1 \<in> set YS"
    using YS_def assms(10) by simp
  ultimately have "y\<^sub>1 \<in> set (take 8 YS)"
    using RYS_def \<open>RYS \<subseteq> set (take 8 YS)\<close> by auto
  thus ?thesis
    using assms(1,10) YS_def by auto
qed
  
lemma find_closest_dist_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < length ys" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<exists>y\<^sub>1 \<in> set ys. dist y\<^sub>0 y\<^sub>1 < \<delta>"
  shows "\<forall>y\<^sub>1 \<in> set ys. dist y\<^sub>0 (find_closest y\<^sub>0 (take 7 ys)) \<le> dist y\<^sub>0 y\<^sub>1"
proof -
  have "dist y\<^sub>0 (find_closest y\<^sub>0 ys) < \<delta>"
    using assms(11) dual_order.strict_trans2 find_closest_dist by blast
  moreover have "find_closest y\<^sub>0 ys \<in> set ys"
    using assms(3) find_closest_set by blast
  ultimately have "find_closest y\<^sub>0 ys \<in> set (take 7 ys)"
    using closest_pair_in_take_7[of y\<^sub>0 ys \<delta> ys\<^sub>L ys\<^sub>R l "find_closest y\<^sub>0 ys"] assms by blast
  moreover have "\<forall>y\<^sub>1 \<in> set (take 7 ys). dist y\<^sub>0 (find_closest y\<^sub>0 (take 7 ys)) \<le> dist y\<^sub>0 y\<^sub>1"
    using find_closest_dist by blast
  ultimately have "\<forall>y\<^sub>1 \<in> set ys. dist y\<^sub>0 (find_closest y\<^sub>0 (take 7 ys)) \<le> dist y\<^sub>0 y\<^sub>1"
    using find_closest_dist order.trans by blast
  thus ?thesis .
qed

fun closest_pair_combine :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_combine [] = undefined"
| "closest_pair_combine [p\<^sub>0] = undefined"
| "closest_pair_combine [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_combine (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_combine ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

lemma closest_pair_combine_c0:
  "2 \<le> length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_combine ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine.induct)
  apply (auto simp: find_closest_set Let_def split: if_splits prod.splits)
  done

lemma closest_pair_combine_c1:
  "2 \<le> length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_combine ps \<Longrightarrow> c\<^sub>1 \<in> set ps"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine.induct)
  apply (auto simp: find_closest_set Let_def split: if_splits prod.splits)
  using find_closest_set by (meson in_set_takeD length_greater_0_conv list.discI set_ConsD)

lemma closest_pair_combine_c0_ne_c1:
  "2 \<le> length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_combine ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine.induct)
  apply (auto simp add: find_closest_ne Let_def split: if_splits prod.splits)
  apply (metis find_closest_set in_set_takeD length_greater_0_conv list.discI prod.inject set_ConsD)+
  done

lemmas closest_pair_combine_c0_c1 = closest_pair_combine_c0
  closest_pair_combine_c1 closest_pair_combine_c0_ne_c1

lemma closest_pair_combine_dist:
  assumes "distinct ys" "sortedY ys" "1 < length ys" "0 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set ys. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
  assumes "(c\<^sub>0, c\<^sub>1) = closest_pair_combine ys"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ys)"
  using assms
proof (induction ys arbitrary: c\<^sub>0 c\<^sub>1 ys\<^sub>L ys\<^sub>R rule: closest_pair_combine.induct)
  case (3 p\<^sub>0 p\<^sub>1)
  have "(p\<^sub>0, p\<^sub>1) = closest_pair_combine [p\<^sub>0, p\<^sub>1]"
    by simp
  moreover have "(c\<^sub>0, c\<^sub>1) = closest_pair_combine [p\<^sub>0, p\<^sub>1]"
    using "3.prems"(12) by simp
  ultimately have "p\<^sub>0 = c\<^sub>0" "p\<^sub>1 = c\<^sub>1"
    by simp_all
  thus ?case
    by (simp add: dist_commute min_dist_def set_ConsD)
next
  case (4 x y z zs)

  define YS where "YS = y # z # zs"
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = closest_pair_combine YS"
    using prod.collapse by blast
  define P\<^sub>1 where "P\<^sub>1 = find_closest x (take 7 YS)"
  define YS\<^sub>L where "YS\<^sub>L = ys\<^sub>L - { x }"
  define YS\<^sub>R where "YS\<^sub>R = ys\<^sub>R - { x }"
  note defs = YS_def C\<^sub>0\<^sub>1_def P\<^sub>1_def YS\<^sub>L_def YS\<^sub>R_def

  show ?case
  proof (cases "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set YS \<and> p\<^sub>1 \<in> set YS \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>")
    case True
    moreover have "distinct YS" "sortedY YS"
      using "4.prems"(1,2) sorted_wrt.simps(2) sortedY_def YS_def by simp_all
    moreover have "1 < length YS" "set YS = YS\<^sub>L \<union> YS\<^sub>R"
      using "4.prems"(1,5) YS_def YS\<^sub>L_def YS\<^sub>R_def by auto
    moreover have "\<forall>p \<in> set YS. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
      using "4.prems"(6) YS_def by simp
    moreover have "\<forall>p \<in> YS\<^sub>L. fst p \<le> l" "\<forall>p \<in> YS\<^sub>R. l \<le> fst p"
      using "4.prems"(7,8) YS\<^sub>L_def YS\<^sub>R_def by simp_all
    moreover have "min_dist \<delta> YS\<^sub>L"
      using "4.prems"(9) YS\<^sub>L_def min_dist_def by simp
    moreover have "min_dist \<delta> YS\<^sub>R"
      using "4.prems"(10) YS\<^sub>R_def min_dist_def by simp
    moreover have "(C\<^sub>0, C\<^sub>1) = closest_pair_combine YS"
      using defs by simp
    ultimately have *: "min_dist (dist C\<^sub>0 C\<^sub>1) (set YS)"
      using "4.IH"[of YS\<^sub>L YS\<^sub>R C\<^sub>0 C\<^sub>1] "4.prems"(4) defs by fast
    hence DC0C1: "dist C\<^sub>0 C\<^sub>1 < \<delta>"
      using True le_less_trans min_dist_def by metis
    show ?thesis
    proof (cases "\<exists>x' \<in> set YS. dist x x' < \<delta>")
      case True
      hence #: "\<forall>x' \<in> set YS. dist x P\<^sub>1 \<le> dist x x'"
        using find_closest_dist_take_7 "4.prems" defs by blast
      show ?thesis
      proof cases
        assume ASM: "dist C\<^sub>0 C\<^sub>1 \<le> dist x P\<^sub>1"
        hence "min_dist (dist C\<^sub>0 C\<^sub>1) (set (x # YS))"
          using * # by (auto simp: min_dist_def dist_commute)
        moreover have "(C\<^sub>0, C\<^sub>1) = closest_pair_combine (x # YS)"
          using ASM YS_def C\<^sub>0\<^sub>1_def P\<^sub>1_def by (auto simp add: Let_def split: prod.splits)
        ultimately show ?thesis
          using "4.prems"(12) YS_def by (metis fst_conv snd_conv)
      next
        assume ASM: "\<not> (dist C\<^sub>0 C\<^sub>1 \<le> dist x P\<^sub>1)"
        hence "min_dist (dist x P\<^sub>1) (set (x # YS))"
          using * # apply (auto simp: min_dist_def dist_commute) by force+
        moreover have "(x, P\<^sub>1) = closest_pair_combine (x # YS)"
          using ASM defs by (auto split: prod.splits)
        ultimately show ?thesis
          using "4.prems"(12) YS_def by (metis fst_conv snd_conv)       
      qed
    next
      case False
      have "P\<^sub>1 \<in> set YS"
        using P\<^sub>1_def YS_def find_closest_set[of "take 7 YS" x] set_take_subset[of 7 YS] by auto
      hence "dist C\<^sub>0 C\<^sub>1 < dist x P\<^sub>1"
        using DC0C1 False by auto
      hence "(C\<^sub>0, C\<^sub>1) = closest_pair_combine (x # YS)"
        using YS_def C\<^sub>0\<^sub>1_def P\<^sub>1_def by (auto simp: Let_def split: prod.splits)
      moreover have "min_dist (dist C\<^sub>0 C\<^sub>1) (set (x # YS))"
        using * DC0C1 False by (auto simp: min_dist_def dist_commute)
      ultimately show ?thesis
        using "4.prems"(12) YS_def by (metis fst_conv snd_conv)    
    qed
  next
    case False
    have "distinct YS" "2 \<le> length YS"
      using YS_def "4.prems"(1) by simp_all
    moreover have "(C\<^sub>0, C\<^sub>1) = closest_pair_combine YS"
      by (simp add: C\<^sub>0\<^sub>1_def)
    ultimately have C01: "C\<^sub>0 \<in> set YS" "C\<^sub>1 \<in> set YS" "C\<^sub>0 \<noteq> C\<^sub>1"
      using C\<^sub>0\<^sub>1_def closest_pair_combine_c0_c1 by blast+
    have 0: "\<exists>x' \<in> set YS. dist x x' < \<delta>"
      using False YS_def "4.prems"(11) by (auto simp: dist_commute)
    hence "\<forall>x' \<in> set YS. dist x P\<^sub>1 \<le> dist x x'"
      using defs find_closest_dist_take_7[of x YS \<delta> ys\<^sub>L ys\<^sub>R l] "4.prems" by blast
    moreover have "dist x P\<^sub>1 < \<delta>"
      using 0 calculation by auto
    ultimately have *: "min_dist (dist x P\<^sub>1) (set (x # YS))"
      using False apply (auto simp: min_dist_def dist_commute) by force+
    hence "dist x P\<^sub>1 < dist C\<^sub>0 C\<^sub>1"
      using C01 \<open>dist x P\<^sub>1 < \<delta>\<close> False by (meson not_less order.strict_trans2)
    hence "(x, P\<^sub>1) = closest_pair_combine (x # YS)"
      using defs by (auto split: prod.splits)
    thus ?thesis
      using "4.prems"(12) * YS_def by (metis fst_conv snd_conv)
  qed
qed auto


subsection "Combine"

fun combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let \<delta> = dist c\<^sub>0 c\<^sub>1 in
    let ys' = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) ys in
    if length ys' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_combine ys' in
      if dist p\<^sub>0 p\<^sub>1 < \<delta> then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

lemma combine_c0:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
  shows "c\<^sub>0 = p\<^sub>0\<^sub>L \<or> c\<^sub>0 = p\<^sub>0\<^sub>R \<or> c\<^sub>0 \<in> set ys"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  let ?\<delta> = "dist C\<^sub>0 C\<^sub>1"
  let ?ys' = "filter (\<lambda>p. l - ?\<delta> \<le> fst p \<and> fst p \<le> l + ?\<delta>) ys"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine ?ys'"
    using prod.collapse by blast
  note defs = C\<^sub>0\<^sub>1_def P\<^sub>0\<^sub>1_def

  show ?thesis
  proof cases
    assume "length ?ys' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>)"
    hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using defs by (auto simp: Let_def split: prod.splits)
    moreover have "C\<^sub>0 = p\<^sub>0\<^sub>L \<or> C\<^sub>0 = p\<^sub>0\<^sub>R"
      using defs prod.inject by metis
    ultimately show ?thesis
      using assms(1) by (metis prod.inject)
  next
    assume *: "\<not> (length ?ys' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>))"
    hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
      using assms(1) calculation by argo
    moreover have "P\<^sub>0 \<in> set ?ys'"
      using * defs closest_pair_combine_c0[of ?ys' P\<^sub>0 P\<^sub>1] by linarith
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma combine_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
  shows "c\<^sub>1 = p\<^sub>1\<^sub>L \<or> c\<^sub>1 = p\<^sub>1\<^sub>R \<or> c\<^sub>1 \<in> set ys"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  let ?\<delta> = "dist C\<^sub>0 C\<^sub>1"
  let ?ys' = "filter (\<lambda>p. l - ?\<delta> \<le> fst p \<and> fst p \<le> l + ?\<delta>) ys"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine ?ys'"
    using prod.collapse by blast
  note defs = C\<^sub>0\<^sub>1_def P\<^sub>0\<^sub>1_def

  show ?thesis
  proof cases
    assume "length ?ys' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>)"
    hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "C\<^sub>1 = p\<^sub>1\<^sub>L \<or> C\<^sub>1 = p\<^sub>1\<^sub>R"
      using defs prod.inject by metis
    ultimately show ?thesis
      using assms(1) by (metis prod.inject)
  next
    assume *: "\<not> (length ?ys' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>))"
    hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
      using assms(1) calculation by argo
    moreover have "P\<^sub>1 \<in> set ?ys'"
      using * defs closest_pair_combine_c1[of ?ys' P\<^sub>0 P\<^sub>1] by linarith
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma combine_c0_ne_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R" "distinct ys"
  shows "c\<^sub>0 \<noteq> c\<^sub>1"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  let ?\<delta> = "dist C\<^sub>0 C\<^sub>1"
  let ?ys' = "filter (\<lambda>p. l - ?\<delta> \<le> fst p \<and> fst p \<le> l + ?\<delta>) ys"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine ?ys'"
    using prod.collapse by blast
  note defs = C\<^sub>0\<^sub>1_def P\<^sub>0\<^sub>1_def

  show ?thesis
  proof cases
    assume "length ?ys' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>)"
    hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "C\<^sub>0 \<noteq> C\<^sub>1"
      using assms(2,3) defs prod.inject by metis
    ultimately show ?thesis
      using assms(1) by (metis prod.inject)
  next
    assume *: "\<not> (length ?ys' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>))"
    hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
      using assms(1) calculation by argo
    moreover have "distinct ?ys'" "2 \<le> length ?ys'"
      using assms(4) * by auto
    moreover have "P\<^sub>0 \<noteq> P\<^sub>1"
      using * defs calculation closest_pair_combine_c0_ne_c1[of ?ys' P\<^sub>0 P\<^sub>1] by linarith
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma set_band_filter_aux:
  assumes "p\<^sub>0 \<in> ys\<^sub>L" "p\<^sub>1 \<in> ys\<^sub>R" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) (ys :: point list)"
  shows "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys'"
proof (rule ccontr)
  assume "\<not> (p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys')"
  then consider (A) "p\<^sub>0 \<notin> set ys' \<and> p\<^sub>1 \<notin> set ys'"
              | (B) "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<notin> set ys'"
              | (C) "p\<^sub>0 \<notin> set ys' \<and> p\<^sub>1 \<in> set ys'"
    by blast
  thus False
  proof cases
    case A
    hence "fst p\<^sub>0 < l - \<delta> \<or> l + \<delta> < fst p\<^sub>0" "fst p\<^sub>1 < l - \<delta> \<or> l + \<delta> < fst p\<^sub>1"
      using assms(1,2,5,8) by auto
    hence "fst p\<^sub>0 < l - \<delta>" "l + \<delta> < fst p\<^sub>1"
      using assms(1,2,6,7) by force+
    hence "\<delta> < dist (fst p\<^sub>0) (fst p\<^sub>1)"
      using dist_real_def by simp
    hence "\<delta> < dist p\<^sub>0 p\<^sub>1"
      using dist_fst_le by (metis dual_order.strict_trans1)
    then show ?thesis
      using assms(4) by fastforce
  next
    case B
    hence "fst p\<^sub>1 < l - \<delta> \<or> l + \<delta> < fst p\<^sub>1"
      using assms(2,5,8) by auto
    hence "l + \<delta> < fst p\<^sub>1"
      using assms(2,7) by auto
    moreover have "fst p\<^sub>0 \<le> l"
      using assms(1,6) by simp
    ultimately have "\<delta> < dist (fst p\<^sub>0) (fst p\<^sub>1)"
      using dist_real_def by simp
    hence "\<delta> < dist p\<^sub>0 p\<^sub>1"
      using dist_fst_le less_le_trans by blast
    thus ?thesis
      using assms(4) by simp
  next
    case C
    hence "fst p\<^sub>0 < l - \<delta> \<or> l + \<delta> < fst p\<^sub>0"
      using assms(1,2,5,8) by auto
    hence "fst p\<^sub>0 < l - \<delta>"
      using assms(1,6) by auto
    moreover have "l \<le> fst p\<^sub>1"
      using assms(2,7) by simp
    ultimately have "\<delta> < dist (fst p\<^sub>0) (fst p\<^sub>1)"
      using dist_real_def by simp
    hence "\<delta> < dist p\<^sub>0 p\<^sub>1"
      using dist_fst_le less_le_trans by blast
    thus ?thesis
      using assms(4) by simp
  qed
qed
  
lemma set_band_filter:
  assumes "p\<^sub>0 \<in> set ys" "p\<^sub>1 \<in> set ys" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) (ys :: point list)"
  shows "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys'"
proof -
  have "p\<^sub>0 \<notin> ys\<^sub>L \<or> p\<^sub>1 \<notin> ys\<^sub>L" "p\<^sub>0 \<notin> ys\<^sub>R \<or> p\<^sub>1 \<notin> ys\<^sub>R"
    using assms(3,4,6,7) min_dist_def by force+
  then consider (A) "p\<^sub>0 \<in> ys\<^sub>L \<and> p\<^sub>1 \<in> ys\<^sub>R" | (B) "p\<^sub>0 \<in> ys\<^sub>R \<and> p\<^sub>1 \<in> ys\<^sub>L"
    using assms(1,2,5) by auto
  thus ?thesis
  proof cases
    case A
    thus ?thesis
      using set_band_filter_aux assms(3,4,5,8,9,10) by blast
  next
    case B
    moreover have "dist p\<^sub>1 p\<^sub>0 < \<delta>"
      using assms(4) dist_commute by metis
    ultimately show ?thesis
      using set_band_filter_aux assms(3)[symmetric] assms(5,8,9,10) by blast
  qed
qed

lemma set_Un_filter:
  "set xs = A \<union> B \<Longrightarrow> set (filter P xs) = { x \<in> A. P x } \<union> { x \<in> B. P x}"
  apply (induction xs arbitrary: A B)
  apply (auto)
  by blast+

lemma combine_dist:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R"
  assumes "distinct ys" "sortedY ys" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "min_dist (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ys\<^sub>L" "min_dist (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ys)"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  define \<delta> where "\<delta> = dist C\<^sub>0 C\<^sub>1"
  define YS where "YS = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) ys"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine YS"
    using prod.collapse by blast
  define YS\<^sub>L where "YS\<^sub>L = { p \<in> ys\<^sub>L. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta> }"
  define YS\<^sub>R where "YS\<^sub>R = { p \<in> ys\<^sub>R. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta> }"
  note defs = C\<^sub>0\<^sub>1_def \<delta>_def YS_def P\<^sub>0\<^sub>1_def YS\<^sub>L_def YS\<^sub>R_def

  have \<delta>_ys\<^sub>L: "min_dist \<delta> ys\<^sub>L"
    using assms(7,8) \<delta>_def C\<^sub>0\<^sub>1_def min_dist_def apply (auto split: if_splits) by force+
  have \<delta>_ys\<^sub>R: "min_dist \<delta> ys\<^sub>R"
    using assms(7,8) \<delta>_def C\<^sub>0\<^sub>1_def min_dist_def apply (auto split: if_splits) by force+

  show ?thesis
  proof (cases "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>")
    case True
    hence "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set YS \<and> p\<^sub>1 \<in> set YS \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
      using set_band_filter \<delta>_ys\<^sub>L \<delta>_ys\<^sub>R assms(6,9,10) YS_def by blast
    moreover have LYS: "2 \<le> length YS"
      using calculation by (cases YS) (auto simp add: Suc_le_eq)
    moreover have "distinct YS" "sortedY YS"
      using assms(4,5) sortedY_def sorted_wrt_filter YS_def by simp_all
    moreover have "0 < \<delta>"
      using \<delta>_def C\<^sub>0\<^sub>1_def assms(2,3) calculation(1) by auto
    moreover have "set YS = YS\<^sub>L \<union> YS\<^sub>R"
      using assms(6) set_Un_filter defs by auto
    moreover have "\<forall>p \<in> set YS. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
      using YS_def by simp
    moreover have "min_dist \<delta> YS\<^sub>L"
      using \<delta>_ys\<^sub>L YS\<^sub>L_def min_dist_def by blast
    moreover have "min_dist \<delta> YS\<^sub>R"
      using \<delta>_ys\<^sub>R YS\<^sub>R_def min_dist_def by blast
    moreover have "\<forall>p \<in> YS\<^sub>L. fst p \<le> l" "\<forall>p \<in> YS\<^sub>R. l \<le> fst p"
      using assms(9,10) YS\<^sub>L_def YS\<^sub>R_def by blast+
    moreover have "(P\<^sub>0, P\<^sub>1) = closest_pair_combine YS"
      using defs by auto
    ultimately have "min_dist (dist P\<^sub>0 P\<^sub>1) (set YS)"
      using closest_pair_combine_dist[of YS \<delta> YS\<^sub>L YS\<^sub>R] by auto
    moreover have "\<forall>p\<^sub>0 \<in> set ys. \<forall>p\<^sub>1 \<in> set ys. p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta> \<longrightarrow> p\<^sub>0 \<in> set YS \<and> p\<^sub>1 \<in> set YS"
      using set_band_filter assms(6,9,10) \<delta>_ys\<^sub>L \<delta>_ys\<^sub>R YS_def by blast
    ultimately have *: "min_dist (dist P\<^sub>0 P\<^sub>1) (set ys)"
      using True min_dist_def by smt
    
    show ?thesis
    proof cases
      assume "length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>)"
      moreover have "dist P\<^sub>0 P\<^sub>1 < \<delta>"
        using True * min_dist_def by force
      ultimately show ?thesis
        using LYS by linarith
    next
      assume "\<not> (length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>))"
      hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
        using defs by (auto simp: Let_def split: prod.splits)
      moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
        using assms(1) calculation by argo
      ultimately show ?thesis
        using * by blast
    qed
  next
    case False
    hence *: "min_dist (dist C\<^sub>0 C\<^sub>1) (set ys)"
      using \<delta>_ys\<^sub>L \<delta>_ys\<^sub>R defs min_dist_def by (meson leI)
    thus ?thesis
    proof cases
      assume "length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>)"
      hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
        using defs by (auto simp: Let_def split: prod.split)
      moreover have "(c\<^sub>0, c\<^sub>1) = (C\<^sub>0, C\<^sub>1)"
        using assms(1) calculation by argo
      ultimately show ?thesis
        using * by blast
    next
      assume ASM: "\<not> (length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>))"
      hence combine: "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
        using defs by (auto simp: Let_def split: prod.split)
      have "(P\<^sub>0, P\<^sub>1) = closest_pair_combine YS"
        using defs by auto
      hence "P\<^sub>0 \<in> set YS" "P\<^sub>1 \<in> set YS"
        using ASM defs closest_pair_combine_c0[of YS P\<^sub>0 P\<^sub>1] closest_pair_combine_c1[of YS P\<^sub>0 P\<^sub>1] by linarith+
      hence "P\<^sub>0 \<in> set ys" "P\<^sub>1 \<in> set ys"
        using filter_is_subset defs by fast+
      moreover have "P\<^sub>0 \<noteq> P\<^sub>1"
        using combine_c0_ne_c1 combine assms(2,3,4) by blast
      ultimately have "\<delta> \<le> dist P\<^sub>0 P\<^sub>1"
        using * defs min_dist_def by blast
      thus ?thesis
        using ASM by argo
    qed
  qed
qed


subsection "Closest Pair of Points Algorithm"

function closest_pair_rec :: "point list \<Rightarrow> (point list * point * point)" where
  "closest_pair_rec xs = (
    let n = length xs in
    if n \<le> 3 then
      (sortY xs, closest_pair_bf xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in

      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys) 
  )"
  by pat_completeness auto
termination closest_pair_rec
  apply (relation "Wellfounded.measure (\<lambda>xs. length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

lemma closest_pair_rec_simps:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "closest_pair_rec xs = (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let l = fst (hd xs\<^sub>R) in
    let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
    let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
    let ys = merge snd ys\<^sub>L ys\<^sub>R in
    (ys, combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys) 
  )"
  using assms by (auto simp: Let_def)

declare closest_pair_rec.simps [simp del]
declare combine.simps [simp del]

lemma closest_pair_rec_set_length_sortedY:
  assumes "(ys, cp) = closest_pair_rec xs"
  shows "set ys = set xs \<and> length ys = length xs \<and> sortedY ys"
  using assms
proof (induction xs arbitrary: ys cp rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    thus ?thesis using "1.prems" sortY(1,2,3)
      by (auto simp: closest_pair_rec.simps)
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"
    obtain YS\<^sub>L CP\<^sub>L where YSCP\<^sub>L_def: "(YS\<^sub>L, CP\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by blast
    obtain YS\<^sub>R CP\<^sub>R where YSCP\<^sub>R_def: "(YS\<^sub>R, CP\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by blast
    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define CP where "CP = combine CP\<^sub>L CP\<^sub>R L YS"
    note defs = XS\<^sub>L\<^sub>R_def L_def YSCP\<^sub>L_def YSCP\<^sub>R_def YS_def CP_def

    have "length XS\<^sub>L < length xs" "length XS\<^sub>R < length xs"
      using False defs by (auto simp: split_at_take_drop_conv)
    hence IH: "set XS\<^sub>L = set YS\<^sub>L" "set XS\<^sub>R = set YS\<^sub>R"
              "length XS\<^sub>L = length YS\<^sub>L" "length XS\<^sub>R = length YS\<^sub>R"
              "sortedY YS\<^sub>L" "sortedY YS\<^sub>R"
      using "1.IH" defs by metis+

    have "set xs = set XS\<^sub>L \<union> set XS\<^sub>R"
      using defs by (auto simp: set_take_drop split_at_take_drop_conv)
    hence SET: "set xs = set YS"
      using set_merge IH(1,2) defs by fast

    have "length xs = length XS\<^sub>L + length XS\<^sub>R"
      using defs by (auto simp: split_at_take_drop_conv)
    hence LENGTH: "length xs = length YS"
      using IH(3,4) length_merge defs by metis

    have SORTED: "sortedY YS"
      using IH(5,6) by (simp add: defs sortedY_def sorted_merge)

    have "(YS, CP) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)
    hence "(ys, cp) = (YS, CP)"
      using "1.prems" by argo
    thus ?thesis
      using SET LENGTH SORTED by simp
  qed
qed

lemma closest_pair_rec_distinct:
  assumes "distinct xs" "(ys, cp) = closest_pair_rec xs"
  shows "distinct ys"
  using assms
proof (induction xs arbitrary: ys cp rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    thus ?thesis using "1.prems" sortY(4)
      by (auto simp: closest_pair_rec.simps)
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"
    obtain YS\<^sub>L CP\<^sub>L where YSCP\<^sub>L_def: "(YS\<^sub>L, CP\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by blast
    obtain YS\<^sub>R CP\<^sub>R where YSCP\<^sub>R_def: "(YS\<^sub>R, CP\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by blast
    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define CP where "CP = combine CP\<^sub>L CP\<^sub>R L YS"
    note defs = XS\<^sub>L\<^sub>R_def L_def YSCP\<^sub>L_def YSCP\<^sub>R_def YS_def CP_def

    have "length XS\<^sub>L < length xs" "length XS\<^sub>R < length xs"
      using False defs by (auto simp: split_at_take_drop_conv)
    moreover have "distinct XS\<^sub>L" "distinct XS\<^sub>R"
      using "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    ultimately have IH: "distinct YS\<^sub>L" "distinct YS\<^sub>R" 
      using "1.IH" defs by blast+

    have "set XS\<^sub>L \<inter> set XS\<^sub>R = {}"
      using "1.prems"(1) defs by (auto simp: split_at_take_drop_conv set_take_disj_set_drop_if_distinct)
    moreover have "set XS\<^sub>L = set YS\<^sub>L" "set XS\<^sub>R = set YS\<^sub>R"
      using closest_pair_rec_set_length_sortedY defs by blast+
    ultimately have "set YS\<^sub>L \<inter> set YS\<^sub>R = {}"
      by blast
    hence DISTINCT: "distinct YS"
      using distinct_merge IH defs by blast

    have "(YS, CP) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)
    hence "(ys, cp) = (YS, CP)"
      using "1.prems" by argo
    thus ?thesis
      using DISTINCT by blast
  qed
qed

lemma closest_pair_rec_c0_c1:
  assumes "1 < length xs" "distinct xs" "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  shows "c\<^sub>0 \<in> set xs \<and> c\<^sub>1 \<in> set xs \<and> c\<^sub>0 \<noteq> c\<^sub>1"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(c\<^sub>0, c\<^sub>1) = closest_pair_bf xs"
      using "1.prems"(3) closest_pair_rec.simps by simp
    moreover have "2 \<le> length xs"
      using "1.prems"(1) by simp
    ultimately show ?thesis
      using "1.prems"(2) closest_pair_bf_c0_c1 by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where YSC\<^sub>0\<^sub>1\<^sub>L_def: "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where YSC\<^sub>0\<^sub>1\<^sub>R_def: "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by metis

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      using prod.collapse by blast
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs" "distinct XS\<^sub>L"
      using False "1.prems"(2) defs by (auto simp: split_at_take_drop_conv)
    hence "C\<^sub>0\<^sub>L \<in> set XS\<^sub>L" "C\<^sub>1\<^sub>L \<in> set XS\<^sub>L" and IHL1: "C\<^sub>0\<^sub>L \<noteq> C\<^sub>1\<^sub>L"
      using "1.IH" defs by metis+
    hence IHL2: "C\<^sub>0\<^sub>L \<in> set xs" "C\<^sub>1\<^sub>L \<in> set xs"
      using split_at_take_drop_conv in_set_takeD fst_conv defs by metis+

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs" "distinct XS\<^sub>R"
      using False "1.prems"(2) defs by (auto simp: split_at_take_drop_conv)
    hence "C\<^sub>0\<^sub>R \<in> set XS\<^sub>R" "C\<^sub>1\<^sub>R \<in> set XS\<^sub>R" and IHR1: "C\<^sub>0\<^sub>R \<noteq> C\<^sub>1\<^sub>R"
      using "1.IH" defs by metis+
    hence IHR2: "C\<^sub>0\<^sub>R \<in> set xs" "C\<^sub>1\<^sub>R \<in> set xs"
      using split_at_take_drop_conv in_set_dropD snd_conv defs by metis+

    have *: "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)
    have YS: "set xs = set YS" "distinct YS"
      using "1.prems"(2) closest_pair_rec_set_length_sortedY closest_pair_rec_distinct * by blast+

    have "C\<^sub>0 \<in> set xs"
      using combine_c0 IHL2(1) IHR2(1) YS defs by blast
    moreover have "C\<^sub>1 \<in> set xs"
      using combine_c1 IHL2(2) IHR2(2) YS defs by blast
    moreover have "C\<^sub>0 \<noteq> C\<^sub>1"
      using combine_c0_ne_c1 IHL1 IHR1 YS defs by blast
    ultimately show ?thesis
      using "1.prems"(3) * by (metis Pair_inject)
  qed
qed

lemma closest_pair_rec_dist:
  assumes "1 < length xs" "distinct xs" "sortedX xs" "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set xs)"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(c\<^sub>0, c\<^sub>1) = closest_pair_bf xs"
      using "1.prems"(4) closest_pair_rec.simps by simp
    thus ?thesis
      using "1.prems"(1,4) closest_pair_bf_dist by metis
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where YSC\<^sub>0\<^sub>1\<^sub>L_def: "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where YSC\<^sub>0\<^sub>1\<^sub>R_def: "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by metis

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      using prod.collapse by blast
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have XSLR: "XS\<^sub>L = take (?n div 2) xs" "XS\<^sub>R = drop (?n div 2) xs"
      using defs by (auto simp: split_at_take_drop_conv)

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>L" "sortedX XS\<^sub>L"
      using "1.prems"(2,3) XSLR by (auto simp: sortedX_def sorted_wrt_take)
    ultimately have L: "min_dist (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set XS\<^sub>L)"
                       "set XS\<^sub>L = set YS\<^sub>L" "C\<^sub>0\<^sub>L \<noteq> C\<^sub>1\<^sub>L"
      using 1 closest_pair_rec_set_length_sortedY closest_pair_rec_c0_c1 YSC\<^sub>0\<^sub>1\<^sub>L_def by blast+
    hence IHL: "min_dist (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set YS\<^sub>L)"
      by argo

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>R" "sortedX XS\<^sub>R"
      using "1.prems"(2,3) XSLR by (auto simp: sortedX_def sorted_wrt_drop)
    ultimately have R: "min_dist (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set XS\<^sub>R)"
                       "set XS\<^sub>R = set YS\<^sub>R" "C\<^sub>0\<^sub>R \<noteq> C\<^sub>1\<^sub>R"
      using 1 closest_pair_rec_set_length_sortedY closest_pair_rec_c0_c1 YSC\<^sub>0\<^sub>1\<^sub>R_def by blast+
    hence IHR: "min_dist (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set YS\<^sub>R)"
      by argo

    have *: "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs by (auto simp: Let_def split: prod.split)

    have "set xs = set YS" "distinct YS" "sortedY YS"
      using "1.prems"(2) closest_pair_rec_set_length_sortedY closest_pair_rec_distinct * by blast+
    moreover have "\<forall>p \<in> set YS\<^sub>L. fst p \<le> L"
      using False "1.prems"(3) XSLR L_def L(2) sortedX_take_less_hd_drop by simp
    moreover have "\<forall>p \<in> set YS\<^sub>R. L \<le> fst p"
      using False "1.prems"(3) XSLR L_def R(2) sortedX_hd_drop_less_drop by simp
    moreover have "set YS = set YS\<^sub>L \<union> set YS\<^sub>R"
      using set_merge defs by fast
    moreover have "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      by (auto simp add: defs)
    ultimately have "min_dist (dist C\<^sub>0 C\<^sub>1) (set xs)"
      using combine_dist IHL IHR L(3) R(3) by presburger
    moreover have "(YS, C\<^sub>0, C\<^sub>1) = (ys, c\<^sub>0, c\<^sub>1)"
      using "1.prems"(4) * by simp
    ultimately show ?thesis
      by blast
  qed
qed

definition closest_pair :: "point list \<Rightarrow> (point * point)" where
  "closest_pair ps = (let (ys, c) = closest_pair_rec (sortX ps) in c)"

theorem closest_pair_c0_c1:
  assumes "1 < length ps" "distinct ps" "(c\<^sub>0, c\<^sub>1) = closest_pair ps"
  shows "c\<^sub>0 \<in> set ps" "c\<^sub>1 \<in> set ps" "c\<^sub>0 \<noteq> c\<^sub>1"
  using assms sortX closest_pair_rec_c0_c1[of "sortX ps"] unfolding closest_pair_def
  by (auto split: prod.splits)

theorem closest_pair_dist:
  assumes "1 < length ps" "distinct ps" "(c\<^sub>0, c\<^sub>1) = closest_pair ps"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms sortX closest_pair_rec_dist[of "sortX ps"] unfolding closest_pair_def
  by (auto split: prod.splits)

end
