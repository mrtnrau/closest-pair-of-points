theory Closest_Pair
  imports "HOL-Analysis.Analysis"
begin

section "Closest Pair Of Points Functional Correctness"

type_synonym point = "real * real"

subsection "Splitting"

fun split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at _ [] = ([], [])"
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
      using False Cons.prems by (auto simp add: take_Cons')
    moreover have "set (drop i (x#xs)) = set (drop (i-1) xs)"
      using False Cons.prems by (auto simp add: drop_Cons')
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
| "merge _ [] ys = ys"
| "merge _ xs [] = xs"

lemma length_merge:
  "length (merge f xs ys) = length xs + length ys"
  by (induction f xs ys rule: merge.induct) auto

lemma set_merge:
  "set (merge f xs ys) = set xs \<union> set ys"
  by (induction f xs ys rule: merge.induct) auto

lemma distinct_merge:
  assumes "set xs \<inter> set ys = {}" "distinct xs" "distinct ys"
  shows "distinct (merge f xs ys)"
  using assms by (induction f xs ys rule: merge.induct) (auto simp add: set_merge)

lemma sorted_merge:
  assumes "P = (\<lambda>x y. f x \<le> f y)"
  shows "sorted_wrt P (merge f xs ys) \<longleftrightarrow> sorted_wrt P xs \<and> sorted_wrt P ys"
  using assms by (induction f xs ys rule: merge.induct) (auto simp add: set_merge)


function msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "msort _ [] = []"
| "msort _ [x] = [x]"
| "msort f (x # y # xs) = (  
    let (l, r) = split_at (length (x # y # xs) div 2) (x # y # xs) in
    merge f (msort f l) (msort f r)
  )"
  by pat_completeness auto
termination msort
  apply (relation "Wellfounded.measure (\<lambda>(_, xs). length xs)")
  apply (auto simp add: split_at_take_drop_conv Let_def)
  done

lemma sorted_wrt_msort:
  "sorted_wrt (\<lambda>x y. f x \<le> f y) (msort f xs)"
  by (induction f xs rule: msort.induct) (auto simp add: split_at_take_drop_conv sorted_merge)

lemma set_msort:
  "set (msort f xs) = set xs"
  apply (induction f xs rule: msort.induct)
  apply (simp_all add: set_merge split_at_take_drop_conv)
  using set_take_drop by (metis list.simps(15))

lemma length_msort:
  "length (msort f xs) = length xs"
  by (induction f xs rule: msort.induct) (auto simp add: length_merge split_at_take_drop_conv)

lemma distinct_msort:
  "distinct xs \<Longrightarrow> distinct (msort f xs)"
proof (induction f xs rule: msort.induct)
  case (3 f x y xs)
  let ?lr = "split_at (length (x # y # xs) div 2) (x # y # xs)"
  let ?l = "fst ?lr"
  let ?r = "snd ?lr"
  have "distinct ?l" "distinct ?r"
    using "3.prems" split_at_take_drop_conv by (metis distinct_take distinct_drop fst_conv snd_conv)+
  hence "distinct (msort f ?l)" "distinct (msort f ?r)"
    using "3.IH" by (metis eq_fst_iff eq_snd_iff)+
  moreover have "set ?l \<inter> set ?r = {}"
    using "3.prems" split_at_take_drop_conv by (metis append_take_drop_id distinct_append fst_conv snd_conv)
  ultimately show ?case
    by (auto simp add: distinct_merge set_msort split: prod.splits)
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
  by (auto simp add: sorted_wrt_msort set_msort length_msort distinct_msort)

lemma sortY:
  shows sortedY_sortY: "sortedY (sortY ps)" and
        set_sortY: "set (sortY ps) = set ps" and
        length_sortY: "length (sortY ps) = length ps" and
        distinct_sortY: "distinct ps \<Longrightarrow> distinct (sortY ps)"
  unfolding sortY_def sortedY_def
  by (auto simp add: sorted_wrt_msort set_msort length_msort distinct_msort)

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

definition sparse :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "sparse \<delta> ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1)"

lemma sparse_identity:
  assumes "sparse (dist c\<^sub>0 c\<^sub>1) (set ps)" "\<forall>p \<in> set ps. dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set (p\<^sub>0 # ps))"
  using assms by (simp add: dist_commute sparse_def)

lemma sparse_update:
  assumes "sparse (dist c\<^sub>0 c\<^sub>1) (set ps)"
  assumes "dist p\<^sub>0 p\<^sub>1 \<le> dist c\<^sub>0 c\<^sub>1" "\<forall>p \<in> set ps. dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "sparse (dist p\<^sub>0 p\<^sub>1) (set (p\<^sub>0 # ps))"
  using assms apply (auto simp add: dist_commute sparse_def) by force+


subsection "Brute Force Algorithm"

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
  by (induction p\<^sub>0 ps rule: find_closest.induct) (auto simp add: Let_def)

lemma find_closest_set:
  "0 < length ps \<Longrightarrow> find_closest p\<^sub>0 ps \<in> set ps"
  by (induction p\<^sub>0 ps rule: find_closest.induct) (auto simp add: Let_def)

lemma find_closest_ne:
  "0 < length ps \<Longrightarrow> p\<^sub>0 \<notin> set ps \<Longrightarrow> find_closest p\<^sub>0 ps \<noteq> p\<^sub>0"
  by (induction p\<^sub>0 ps rule: find_closest.induct) (auto simp add: Let_def)


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
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: bf_closest_pair.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  thus ?case using find_closest_set[of "p\<^sub>1 # p\<^sub>2 # ps" p\<^sub>0]
    by (auto simp add: Let_def split!: if_splits prod.splits)
qed auto

lemma bf_closest_pair_c1:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps \<Longrightarrow> c\<^sub>1 \<in> set ps"
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: bf_closest_pair.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  thus ?case using find_closest_set[of "p\<^sub>1 # p\<^sub>2 # ps" p\<^sub>0]
    by (auto simp add: Let_def split!: if_splits prod.splits)
qed auto

lemma bf_closest_pair_c0_ne_c1:
  "1 < length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: bf_closest_pair.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  thus ?case using find_closest_ne[of "p\<^sub>2 # ps" p\<^sub>0]
    by (auto simp add: Let_def split!: prod.splits if_splits)
qed auto

lemmas bf_closest_pair_c0_c1 = bf_closest_pair_c0 bf_closest_pair_c1 bf_closest_pair_c0_ne_c1

lemma bf_closest_pair_dist:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = bf_closest_pair ps"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: bf_closest_pair.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)

  let ?ps = "p\<^sub>1 # p\<^sub>2 # ps"
  let ?c = "bf_closest_pair ?ps"
  let ?c\<^sub>0 = "fst ?c"
  let ?c\<^sub>1 = "snd ?c"

  have IH: "sparse (dist ?c\<^sub>0 ?c\<^sub>1) (set (p\<^sub>1 # p\<^sub>2 # ps))"
    using 4 by simp
  have *: "\<forall>p \<in> set ?ps. dist p\<^sub>0 (find_closest p\<^sub>0 ?ps) \<le> dist p\<^sub>0 p"
    using find_closest_dist by blast

  show ?case
  proof (cases "dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist p\<^sub>0 (find_closest p\<^sub>0 ?ps)")
    case True
    hence "\<forall>p \<in> set ?ps. dist ?c\<^sub>0 ?c\<^sub>1 \<le> dist p\<^sub>0 p"
      using * by auto
    hence "sparse (dist ?c\<^sub>0 ?c\<^sub>1) (set (p\<^sub>0 # ?ps))"
      using sparse_identity IH by blast
    moreover have "(c\<^sub>0, c\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using True "4.prems" by (auto split: prod.splits)
    ultimately show ?thesis
      by blast
  next
    case False
    hence "dist p\<^sub>0 (find_closest p\<^sub>0 ?ps) \<le> dist ?c\<^sub>0 ?c\<^sub>1"
      by simp
    hence "sparse (dist p\<^sub>0 (find_closest p\<^sub>0 ?ps)) (set (p\<^sub>0 # ?ps))"
      using sparse_update IH * by blast
    moreover have "(c\<^sub>0, c\<^sub>1) = (p\<^sub>0, (find_closest p\<^sub>0 ?ps))"
      using False "4.prems" by (auto split: prod.splits)
    ultimately show ?thesis
      by simp
  qed
qed (auto simp add: dist_commute sparse_def)


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

lemma card_le_1_pairs_identical:
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

lemma card_S_inter_T:
  assumes "\<forall>x \<in> S. \<forall>y \<in> S. x = y \<or> x \<notin> T \<or> y \<notin> T" 
  shows "card (S \<inter> T) \<le> 1"
proof (rule ccontr)
  assume "\<not> (card (S \<inter> T) \<le> 1)"
  then obtain x y where *: "x \<in> S \<inter> T \<and> y \<in> S \<inter> T \<and> x \<noteq> y"
    by (meson card_le_1_pairs_identical)
  hence "x \<in> T" "y \<in> T"
    by simp_all
  moreover have "x \<notin> T \<or> y \<notin> T"
    using assms * by auto
  ultimately show False
    by blast
qed

lemma card_Int_Un_le_Sum:
  assumes "finite S"
  shows "card (A \<inter> \<Union>S) \<le> (\<Sum>B \<in> S. card (A \<inter> B))"
  using assms
proof (induction "card S" arbitrary: S)
  case (Suc n)
  then obtain B T where *: "S = { B } \<union> T" "card T = n" "B \<notin> T"
    by (metis card_Suc_eq Suc_eq_plus1 insert_is_Un)
  hence "card (A \<inter> \<Union>S) = card (A \<inter> \<Union>({ B } \<union> T))"
    using * by blast
  also have "... \<le> card (A \<inter> B) + card (A \<inter> \<Union>T)"
    by (simp add: card_Un_le inf_sup_distrib1)
  also have "... \<le> card (A \<inter> B) + (\<Sum>B \<in> T. card (A \<inter> B))"
    using Suc * by simp
  also have "... \<le> (\<Sum>B \<in> S. card (A \<inter> B))"
    using Suc.prems * by simp
  finally show ?case .
qed simp

(* 
   Short but ?not? usable: 
     How to instantiate f if each point p in P should be mapped to a specific 
     Box B especially for the pigeonhole lemma below?
*) 
lemma (* TODO *)
  assumes "P \<subseteq> \<Union>(f ` P)" "card (f ` P) < card P"
  shows "\<exists>x \<in> P. \<exists>y \<in> P. \<exists>B \<in> (f ` P). x \<noteq> y \<and> B = f x \<and> B = f y"
  using assms pigeonhole by (metis inj_onI rev_image_eqI)

lemma pigeonhole:
  assumes "finite T" "S \<subseteq> \<Union>T" "card T < card S"
  shows "\<exists>x \<in> S. \<exists>y \<in> S. \<exists>X \<in> T. x \<noteq> y \<and> x \<in> X \<and> y \<in> X"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> S. \<exists>y \<in> S. \<exists>X \<in> T. x \<noteq> y \<and> x \<in> X \<and> y \<in> X)"
  hence *: "\<forall>X \<in> T. card (S \<inter> X) \<le> 1"
    using card_S_inter_T by metis
  have "card T < card (S \<inter> \<Union>T)"
    using Int_absorb2 assms by fastforce
  also have "... \<le> (\<Sum>X \<in> T. card (S \<inter> X))"
    using assms(1) card_Int_Un_le_Sum by blast
  also have "... \<le> card T"
    using * sum_mono by fastforce
  finally show False by simp
qed


subsection "\<delta> Sparse Points within a Square"

lemma max_points_square:
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + \<delta>, y + \<delta>)" "sparse \<delta> ps" "0 < \<delta>"
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
    using assms(2) # sparse_def by simp
  ultimately show False
    by simp
qed


subsection "The Runtime Argument"

lemma closest_pair_in_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "sparse \<delta> ys\<^sub>L" "sparse \<delta> ys\<^sub>R"
  assumes "y\<^sub>1 \<in> set ys" "dist y\<^sub>0 y\<^sub>1 < \<delta>"
  shows "y\<^sub>1 \<in> set (take 7 ys)"
proof -
  define YS where "YS = y\<^sub>0 # ys"
  define RECT where "RECT = cbox (l - \<delta>, snd y\<^sub>0) (l + \<delta>, snd y\<^sub>0 + \<delta>)"
  define LSQ where "LSQ = cbox (l - \<delta>, snd y\<^sub>0) (l, snd y\<^sub>0 + \<delta>)"
  define RSQ where "RSQ = cbox (l, snd y\<^sub>0) (l + \<delta>, snd y\<^sub>0 + \<delta>)"
  define LSQYS where "LSQYS = filter (\<lambda>p. p \<in> LSQ \<and> p \<in> ys\<^sub>L) YS"
  define RSQYS where "RSQYS = filter (\<lambda>p. p \<in> RSQ \<and> p \<in> ys\<^sub>R) YS"
  note defs = YS_def RECT_def LSQ_def RSQ_def LSQYS_def RSQYS_def

  have "RECT = LSQ \<union> RSQ"
    using defs cbox_right_un by auto

  have overlap\<^sub>L: "\<forall>p \<in> ys\<^sub>L. p \<in> RSQ \<longrightarrow> p \<in> LSQ"
    using RSQ_def LSQ_def assms(6) by auto
  have overlap\<^sub>R: "\<forall>p \<in> ys\<^sub>R. p \<in> LSQ \<longrightarrow> p \<in> RSQ"
    using RSQ_def LSQ_def assms(7) by auto
  have set_eq_filter_rect_squares: "set (filter (\<lambda>p. p \<in> RECT) YS) = set LSQYS \<union> set RSQYS"
  proof standard
    have "set (filter (\<lambda>p. p \<in> LSQ) YS) \<subseteq> set LSQYS \<union> set RSQYS"
      using overlap\<^sub>L overlap\<^sub>R YS_def LSQYS_def RSQYS_def assms(4) by auto
    moreover have "set (filter (\<lambda>p. p \<in> RSQ) YS) \<subseteq> set LSQYS \<union> set RSQYS"
      using overlap\<^sub>L overlap\<^sub>R YS_def LSQYS_def RSQYS_def assms(4) by auto
    ultimately show "set (filter (\<lambda>p. p \<in> RECT) YS) \<subseteq> set LSQYS \<union> set RSQYS"
      using \<open>RECT = LSQ \<union> RSQ\<close> by auto
  next
    show "set LSQYS \<union> set RSQYS \<subseteq> set (filter (\<lambda>p. p \<in> RECT) YS)"
      using \<open>RECT = LSQ \<union> RSQ\<close> LSQYS_def RSQYS_def YS_def by auto
  qed

  have "sparse \<delta> (set LSQYS)"
    using assms(8) LSQYS_def sparse_def by simp
  moreover have "\<forall>p \<in> set LSQYS. p \<in> LSQ"
    using LSQYS_def by auto
  ultimately have card_lys: "card (set LSQYS) \<le> 4"
    using max_points_square[of "set LSQYS" "l - \<delta>" "snd y\<^sub>0" \<delta>] assms(3) LSQ_def by auto
  have "sparse \<delta> (set RSQYS)"
    using assms(9) RSQYS_def sparse_def by simp
  moreover have "\<forall>p \<in> set RSQYS. p \<in> RSQ"
    using RSQYS_def by auto
  ultimately have card_rys: "card (set RSQYS) \<le> 4"
    using max_points_square[of "set RSQYS" l "snd y\<^sub>0" \<delta>] assms(3) RSQ_def by auto
  have card_lys_rys: "card (set LSQYS \<union> set RSQYS) \<le> 8"
    using card_lys card_rys card_Un_le[of "set LSQYS" "set RSQYS"] by simp

  have "set LSQYS \<union> set RSQYS \<subseteq> set (take 8 YS)"
  proof (rule ccontr)
    assume "\<not> (set LSQYS \<union> set RSQYS \<subseteq> set (take 8 YS))"
    then obtain p where *: "p \<in> set YS" "p \<in> set LSQYS \<union> set RSQYS" "p \<notin> set (take 8 YS)"
      using LSQYS_def RSQYS_def set_eq_filter_rect_squares filter_is_subset by auto
    hence "p \<in> RECT"
      using \<open>RECT = LSQ \<union> RSQ\<close> \<open>\<forall>p \<in> set LSQYS. p \<in> LSQ\<close> \<open>\<forall>p \<in> set RSQYS. p \<in> RSQ\<close> by auto

    have "\<forall>p\<^sub>0 \<in> set (take 8 YS). \<forall>p\<^sub>1 \<in> set (drop 8 YS). snd p\<^sub>0 \<le> snd p\<^sub>1"
      using sorted_wrt_take_drop[of "\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1" YS 8] assms(2) sortedY_def YS_def by fastforce
    hence "\<forall>p' \<in> set (take 8 YS). snd p' \<le> snd p"
      using append_take_drop_id set_append Un_iff *(1,3) by metis
    moreover have "snd p \<le> snd y\<^sub>0 + \<delta>"
      using \<open>p \<in> RECT\<close> RECT_def by (metis mem_cbox_2D prod.collapse)
    ultimately have "\<forall>p \<in> set (take 8 YS). snd p \<le> snd y\<^sub>0 + \<delta>"
      by fastforce
    moreover have "\<forall>p \<in> set (take 8 YS). snd y\<^sub>0 \<le> snd p"
      using sorted_wrt_hd_less_take[of "\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1" y\<^sub>0 ys 8] assms(2) sortedY_def YS_def by fastforce
    moreover have "\<forall>p \<in> set (take 8 YS). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
      using assms(5) YS_def by (meson in_set_takeD)
    ultimately have "\<forall>p \<in> set (take 8 YS). p \<in> RECT"
      using RECT_def mem_cbox_2D by fastforce

    hence "set (take 8 YS) \<subseteq> set (filter (\<lambda>p. p \<in> RECT) YS)"
      using set_take_subset by fastforce
    hence nine_point_set: "{ p } \<union> set (take 8 YS) \<subseteq> set (filter (\<lambda>p. p \<in> RECT) YS)"
      using *(1) \<open>p \<in> RECT\<close> by simp

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
    moreover have "finite (set (filter (\<lambda>p. p \<in> RECT) YS))"
      by simp
    ultimately have "9 \<le> card (set (filter (\<lambda>p. p \<in> RECT) YS))"
      using nine_point_set card_mono by metis
    hence "9 \<le> card (set LSQYS \<union> set RSQYS)"
      using set_eq_filter_rect_squares by simp
    thus False
      using card_lys_rys by simp
  qed 

  have "snd y\<^sub>0 \<le> snd y\<^sub>1"
    using assms(2,10) sortedY_def by simp
  moreover have "dist (snd y\<^sub>0) (snd y\<^sub>1) < \<delta>"
    using assms(11) dist_snd_le le_less_trans by blast
  ultimately have "snd y\<^sub>1 \<le> snd y\<^sub>0 + \<delta>"
    by (simp add: dist_real_def)
  moreover have "l - \<delta> \<le> fst y\<^sub>1" "fst y\<^sub>1 \<le> l + \<delta>"
    using assms(5,10) by auto
  moreover have "snd y\<^sub>0 \<le> snd y\<^sub>1"
    using sortedY_def assms(2,10) by auto
  ultimately have "y\<^sub>1 \<in> RECT"
    using mem_cbox_2D[of "l - \<delta>" "fst y\<^sub>1" "l + \<delta>" "snd y\<^sub>0" "snd y\<^sub>1" "snd y\<^sub>0 + \<delta>"] defs by simp
  moreover have "y\<^sub>1 \<in> set YS"
    using YS_def assms(10) by simp
  ultimately have "y\<^sub>1 \<in> set LSQYS \<union> set RSQYS"
    using set_eq_filter_rect_squares filter_set by auto
  hence "y\<^sub>1 \<in> set (take 8 YS)"
    using \<open>set LSQYS \<union> set RSQYS \<subseteq> set (take 8 YS)\<close> by blast
  thus ?thesis
    using assms(1,10) YS_def by auto
qed
  
lemma find_closest_dist_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < length ys" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "sparse \<delta> ys\<^sub>L" "sparse \<delta> ys\<^sub>R"
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


subsection "Informed Brute Force Algorithm"

fun closest_pair_7 :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_7 [] = undefined"
| "closest_pair_7 [_] = undefined"
| "closest_pair_7 [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_7 (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_7 ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

lemma closest_pair_7_c0:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_7 ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_7.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  thus ?case using find_closest_set[of "take 7 (p\<^sub>1 # p\<^sub>2 # ps)" p\<^sub>0]
    by (auto simp add: Let_def split!: if_splits prod.splits)
qed auto

lemma closest_pair_7_c1:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_7 ps \<Longrightarrow> c\<^sub>1 \<in> set ps"
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_7.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  thus ?case using find_closest_set[of "take 7 (p\<^sub>1 # p\<^sub>2 # ps)" p\<^sub>0] in_set_takeD
    apply (auto simp add: Let_def split!: if_splits prod.splits)
    by fast
qed auto

lemma closest_pair_7_c0_ne_c1:
  "1 < length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_7 ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_7.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  thus ?case using find_closest_ne[of "take 6 (p\<^sub>2 # ps)" p\<^sub>0] in_set_takeD
    apply (auto simp add: Let_def split!: prod.splits if_splits)
    by fast
qed auto

lemmas closest_pair_7_c0_c1 = closest_pair_7_c0 closest_pair_7_c1 closest_pair_7_c0_ne_c1

lemma closest_7_dist:
  assumes "distinct ys" "sortedY ys" "1 < length ys" "0 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set ys. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "sparse \<delta> ys\<^sub>L" "sparse \<delta> ys\<^sub>R"
  assumes "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
  assumes "(c\<^sub>0, c\<^sub>1) = closest_pair_7 ys"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set ys)"
  using assms
proof (induction ys arbitrary: c\<^sub>0 c\<^sub>1 ys\<^sub>L ys\<^sub>R rule: closest_pair_7.induct)
  case (3 p\<^sub>0 p\<^sub>1)
  have "(p\<^sub>0, p\<^sub>1) = closest_pair_7 [p\<^sub>0, p\<^sub>1]"
    by simp
  moreover have "(c\<^sub>0, c\<^sub>1) = closest_pair_7 [p\<^sub>0, p\<^sub>1]"
    using "3.prems"(12) by simp
  ultimately have "p\<^sub>0 = c\<^sub>0" "p\<^sub>1 = c\<^sub>1"
    by simp_all
  thus ?case
    by (simp add: dist_commute sparse_def set_ConsD)
next
  case (4 x y z zs)

  define YS where "YS = y # z # zs"
  define C\<^sub>0\<^sub>1 where "C\<^sub>0\<^sub>1 = closest_pair_7 YS"
  define C\<^sub>0 where "C\<^sub>0 = fst C\<^sub>0\<^sub>1"
  define C\<^sub>1 where "C\<^sub>1 = snd C\<^sub>0\<^sub>1"
  define P\<^sub>1 where "P\<^sub>1 = find_closest x (take 7 YS)"
  define YS\<^sub>L where "YS\<^sub>L = ys\<^sub>L - { x }"
  define YS\<^sub>R where "YS\<^sub>R = ys\<^sub>R - { x }"
  note defs = YS_def C\<^sub>0\<^sub>1_def C\<^sub>0_def C\<^sub>1_def P\<^sub>1_def YS\<^sub>L_def YS\<^sub>R_def

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
    moreover have "sparse \<delta> YS\<^sub>L"
      using "4.prems"(9) YS\<^sub>L_def sparse_def by simp
    moreover have "sparse \<delta> YS\<^sub>R"
      using "4.prems"(10) YS\<^sub>R_def sparse_def by simp
    moreover have "(C\<^sub>0, C\<^sub>1) = closest_pair_7 YS"
      using defs by simp
    ultimately have *: "sparse (dist C\<^sub>0 C\<^sub>1) (set YS)"
      using "4.IH"[of YS\<^sub>L YS\<^sub>R C\<^sub>0 C\<^sub>1] "4.prems"(4) defs by fast
    hence DC0C1: "dist C\<^sub>0 C\<^sub>1 < \<delta>"
      using True le_less_trans sparse_def by metis
    show ?thesis
    proof (cases "\<exists>x' \<in> set YS. dist x x' < \<delta>")
      case True
      hence #: "\<forall>x' \<in> set YS. dist x P\<^sub>1 \<le> dist x x'"
        using find_closest_dist_take_7 "4.prems" defs by blast
      show ?thesis
      proof cases
        assume ASM: "dist C\<^sub>0 C\<^sub>1 \<le> dist x P\<^sub>1"
        hence "sparse (dist C\<^sub>0 C\<^sub>1) (set (x # YS))"
          using * # by (auto simp add: sparse_def dist_commute)
        moreover have "(C\<^sub>0, C\<^sub>1) = closest_pair_7 (x # YS)"
          using ASM YS_def C\<^sub>0_def C\<^sub>1_def C\<^sub>0\<^sub>1_def P\<^sub>1_def by (auto simp add: Let_def split: prod.splits)
        ultimately show ?thesis
          using "4.prems"(12) YS_def by (metis fst_conv snd_conv)
      next
        assume ASM: "\<not> (dist C\<^sub>0 C\<^sub>1 \<le> dist x P\<^sub>1)"
        hence "sparse (dist x P\<^sub>1) (set (x # YS))"
          using * # apply (auto simp add: sparse_def dist_commute) by force+
        moreover have "(x, P\<^sub>1) = closest_pair_7 (x # YS)"
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
      hence "(C\<^sub>0, C\<^sub>1) = closest_pair_7 (x # YS)"
        using YS_def C\<^sub>0_def C\<^sub>1_def C\<^sub>0\<^sub>1_def P\<^sub>1_def by (auto simp add: Let_def split: prod.splits)
      moreover have "sparse (dist C\<^sub>0 C\<^sub>1) (set (x # YS))"
        using * DC0C1 False by (auto simp add: sparse_def dist_commute)
      ultimately show ?thesis
        using "4.prems"(12) YS_def by (metis fst_conv snd_conv)    
    qed
  next
    case False
    have "distinct YS" "1 < length YS"
      using YS_def "4.prems"(1) by simp_all
    hence C01: "C\<^sub>0 \<in> set YS" "C\<^sub>1 \<in> set YS" "C\<^sub>0 \<noteq> C\<^sub>1"
      using C\<^sub>0_def C\<^sub>1_def C\<^sub>0\<^sub>1_def closest_pair_7_c0_c1 prod.collapse by blast+
    have 0: "\<exists>x' \<in> set YS. dist x x' < \<delta>"
      using False YS_def "4.prems"(11) by (auto simp add: dist_commute)
    hence "\<forall>x' \<in> set YS. dist x P\<^sub>1 \<le> dist x x'"
      using defs find_closest_dist_take_7[of x YS \<delta> ys\<^sub>L ys\<^sub>R l] "4.prems" by blast
    moreover have "dist x P\<^sub>1 < \<delta>"
      using 0 calculation by auto
    ultimately have *: "sparse (dist x P\<^sub>1) (set (x # YS))"
      using False apply (auto simp add: sparse_def dist_commute) by force+
    hence "dist x P\<^sub>1 < dist C\<^sub>0 C\<^sub>1"
      using C01 \<open>dist x P\<^sub>1 < \<delta>\<close> False by (meson not_less order.strict_trans2)
    hence "(x, P\<^sub>1) = closest_pair_7 (x # YS)"
      using defs by (auto split: prod.splits)
    thus ?thesis
      using "4.prems"(12) * YS_def by (metis fst_conv snd_conv)
  qed
qed auto


subsection "Combine"

fun combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ys' = filter (\<lambda>p. l - dist c\<^sub>0 c\<^sub>1 \<le> fst p \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1) ys in
    if length ys' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_7 ys' in
      if dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1 then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

lemma combine_c0:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
  shows "c\<^sub>0 = p\<^sub>0\<^sub>L \<or> c\<^sub>0 = p\<^sub>0\<^sub>R \<or> c\<^sub>0 \<in> set ys"
proof -
  let ?c\<^sub>0\<^sub>1 = "(if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
  let ?c\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
  let ?c\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"
  let ?\<delta> = "dist ?c\<^sub>0 ?c\<^sub>1"
  let ?ys' = "filter (\<lambda>p. l - ?\<delta> \<le> fst p \<and> fst p \<le> l + ?\<delta>) ys"
  let ?p\<^sub>0\<^sub>1 = "closest_pair_7 ?ys'"
  let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
  let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

  show ?thesis
  proof cases
    assume "length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>)"
    hence *: "(?c\<^sub>0, ?c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence "(c\<^sub>0, c\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using assms(1) by argo
    moreover have "?c\<^sub>0 = p\<^sub>0\<^sub>L \<or> ?c\<^sub>0 = p\<^sub>0\<^sub>R"
      by simp
    ultimately show ?thesis
      using * by blast
  next
    assume ASM: "\<not> (length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>))"
    hence *: "(?p\<^sub>0, ?p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence #: "(c\<^sub>0, c\<^sub>1) = (?p\<^sub>0, ?p\<^sub>1)"
      using assms(1) by argo
    have "(?p\<^sub>0, ?p\<^sub>1) = closest_pair_7 ?ys'"
      by auto
    hence "?p\<^sub>0 \<in> set ?ys'"
      using ASM closest_pair_7_c0[of ?ys' ?p\<^sub>0 ?p\<^sub>1] by linarith
    thus ?thesis
      using * # by fastforce
  qed
qed

lemma combine_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
  shows "c\<^sub>1 = p\<^sub>1\<^sub>L \<or> c\<^sub>1 = p\<^sub>1\<^sub>R \<or> c\<^sub>1 \<in> set ys"
proof -
  let ?c\<^sub>0\<^sub>1 = "(if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
  let ?c\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
  let ?c\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"
  let ?\<delta> = "dist ?c\<^sub>0 ?c\<^sub>1"
  let ?ys' = "filter (\<lambda>p. l - ?\<delta> \<le> fst p \<and> fst p \<le> l + ?\<delta>) ys"
  let ?p\<^sub>0\<^sub>1 = "closest_pair_7 ?ys'"
  let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
  let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

  show ?thesis
  proof cases
    assume "length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>)"
    hence *: "(?c\<^sub>0, ?c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence "(c\<^sub>0, c\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using assms(1) by argo
    moreover have "?c\<^sub>1 = p\<^sub>1\<^sub>L \<or> ?c\<^sub>1 = p\<^sub>1\<^sub>R"
      by simp
    ultimately show ?thesis
      using * by blast
  next
    assume ASM: "\<not> (length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>))"
    hence *: "(?p\<^sub>0, ?p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence #: "(c\<^sub>0, c\<^sub>1) = (?p\<^sub>0, ?p\<^sub>1)"
      using assms(1) by argo
    have "(?p\<^sub>0, ?p\<^sub>1) = closest_pair_7 ?ys'"
      by auto
    hence "?p\<^sub>1 \<in> set ?ys'"
      using ASM closest_pair_7_c1[of ?ys' ?p\<^sub>0 ?p\<^sub>1] by linarith
    thus ?thesis
      using * # by fastforce
  qed
qed

lemma combine_c0_ne_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R" "distinct ys"
  shows "c\<^sub>0 \<noteq> c\<^sub>1"
proof -
  let ?c\<^sub>0\<^sub>1 = "(if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
  let ?c\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
  let ?c\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"
  let ?\<delta> = "dist ?c\<^sub>0 ?c\<^sub>1"
  let ?ys' = "filter (\<lambda>p. l - ?\<delta> \<le> fst p \<and> fst p \<le> l + ?\<delta>) ys"
  let ?p\<^sub>0\<^sub>1 = "closest_pair_7 ?ys'"
  let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
  let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

  show ?thesis
  proof cases
    assume "length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>)"
    hence *: "(?c\<^sub>0, ?c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence "(c\<^sub>0, c\<^sub>1) = (?c\<^sub>0, ?c\<^sub>1)"
      using assms(1) by argo
    moreover have "?c\<^sub>0 \<noteq> ?c\<^sub>1"
      using assms(2,3) by auto
    ultimately show ?thesis
      using * by blast
  next
    assume assm: "\<not> (length ?ys' < 2 \<or> \<not> (dist ?p\<^sub>0 ?p\<^sub>1 < ?\<delta>))"
    hence *: "(?p\<^sub>0, ?p\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    hence #: "(c\<^sub>0, c\<^sub>1) = (?p\<^sub>0, ?p\<^sub>1)"
      using assms(1) by argo
    have "distinct ?ys'" "2 \<le> length ?ys'"
      using assms(4) assm by auto
    moreover have "(?p\<^sub>0, ?p\<^sub>1) = closest_pair_7 ?ys'"
      by auto
    ultimately have "?p\<^sub>0 \<noteq> ?p\<^sub>1"
      using closest_pair_7_c0_ne_c1[of ?ys' ?p\<^sub>0 ?p\<^sub>1] by linarith
    thus ?thesis
      using * # by fastforce
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
    hence "\<delta> \<le> dist (fst p\<^sub>0) (fst p\<^sub>1)"
      using dist_real_def by simp
    hence "\<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using dist_fst_le order.trans by blast
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
  assumes "sparse \<delta> ys\<^sub>L" "sparse \<delta> ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) (ys :: point list)"
  shows "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys'"
proof -
  have "p\<^sub>0 \<notin> ys\<^sub>L \<or> p\<^sub>1 \<notin> ys\<^sub>L" "p\<^sub>0 \<notin> ys\<^sub>R \<or> p\<^sub>1 \<notin> ys\<^sub>R"
    using assms(3,4,6,7) sparse_def by force+
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
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R"
  assumes "distinct ys" "sortedY ys" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "sparse (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ys\<^sub>L" "sparse (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set ys)"
proof -
  define C\<^sub>0\<^sub>1 where "C\<^sub>0\<^sub>1 = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
  define C\<^sub>0 where "C\<^sub>0 = fst C\<^sub>0\<^sub>1"
  define C\<^sub>1 where "C\<^sub>1 = snd C\<^sub>0\<^sub>1"
  define \<delta> where "\<delta> = dist C\<^sub>0 C\<^sub>1"
  define YS where "YS = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) ys"
  define P\<^sub>0\<^sub>1 where "P\<^sub>0\<^sub>1 = closest_pair_7 YS"
  define P\<^sub>0 where "P\<^sub>0 = fst P\<^sub>0\<^sub>1"
  define P\<^sub>1 where "P\<^sub>1 = snd P\<^sub>0\<^sub>1"
  define YS\<^sub>L where "YS\<^sub>L = { p \<in> ys\<^sub>L. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta> }"
  define YS\<^sub>R where "YS\<^sub>R = { p \<in> ys\<^sub>R. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta> }"
  note defs = C\<^sub>0\<^sub>1_def C\<^sub>0_def C\<^sub>1_def \<delta>_def YS_def P\<^sub>0\<^sub>1_def P\<^sub>0_def P\<^sub>1_def YS\<^sub>L_def YS\<^sub>R_def

  have \<delta>_ys\<^sub>L: "sparse \<delta> ys\<^sub>L"
    using assms(7,8) \<delta>_def C\<^sub>0_def C\<^sub>1_def C\<^sub>0\<^sub>1_def sparse_def apply (auto) by force+
  have \<delta>_ys\<^sub>R: "sparse \<delta> ys\<^sub>R"
    using assms(7,8) \<delta>_def C\<^sub>0_def C\<^sub>1_def C\<^sub>0\<^sub>1_def sparse_def apply (auto) by force+

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
      using \<delta>_def C\<^sub>0_def C\<^sub>1_def C\<^sub>0\<^sub>1_def by (simp add: assms(2,3))
    moreover have "set YS = YS\<^sub>L \<union> YS\<^sub>R"
      using assms(6) set_Un_filter defs by auto
    moreover have "\<forall>p \<in> set YS. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
      using YS_def by simp
    moreover have "sparse \<delta> YS\<^sub>L"
      using \<delta>_ys\<^sub>L YS\<^sub>L_def sparse_def by blast
    moreover have "sparse \<delta> YS\<^sub>R"
      using \<delta>_ys\<^sub>R YS\<^sub>R_def sparse_def by blast
    moreover have "\<forall>p \<in> YS\<^sub>L. fst p \<le> l" "\<forall>p \<in> YS\<^sub>R. l \<le> fst p"
      using assms(9,10) YS\<^sub>L_def YS\<^sub>R_def by blast+
    moreover have "(P\<^sub>0, P\<^sub>1) = closest_pair_7 YS"
      using defs by auto
    ultimately have "sparse (dist P\<^sub>0 P\<^sub>1) (set YS)"
      using closest_7_dist[of YS \<delta> YS\<^sub>L YS\<^sub>R] by auto
    moreover have "\<forall>p\<^sub>0 \<in> set ys. \<forall>p\<^sub>1 \<in> set ys. p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta> \<longrightarrow> p\<^sub>0 \<in> set YS \<and> p\<^sub>1 \<in> set YS"
      using set_band_filter assms(6,9,10) \<delta>_ys\<^sub>L \<delta>_ys\<^sub>R YS_def by blast
    ultimately have *: "sparse (dist P\<^sub>0 P\<^sub>1) (set ys)"
      using True sparse_def by smt
    
    show ?thesis
    proof cases
      assume "length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>)"
      moreover have "dist P\<^sub>0 P\<^sub>1 < \<delta>"
        using True * sparse_def by force
      ultimately show ?thesis
        using LYS by linarith
    next
      assume "\<not> (length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>))"
      hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
        by (auto simp add: defs Let_def split!: prod.splits)
      moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
        using assms(1) calculation by argo
      ultimately show ?thesis
        using * by blast
    qed
  next
    case False
    hence *: "sparse (dist C\<^sub>0 C\<^sub>1) (set ys)"
      using \<delta>_ys\<^sub>L \<delta>_ys\<^sub>R defs sparse_def by (meson leI)
    thus ?thesis
    proof cases
      assume "length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>)"
      hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
        by (auto simp add: defs Let_def split!: prod.splits)
      moreover have "(c\<^sub>0, c\<^sub>1) = (C\<^sub>0, C\<^sub>1)"
        using assms(1) calculation by argo
      ultimately show ?thesis
        using * by blast
    next
      assume ASM: "\<not> (length YS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>))"
      hence combine: "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
        by (auto simp add: defs Let_def split!: prod.splits)
      have "(P\<^sub>0, P\<^sub>1) = closest_pair_7 YS"
        using defs by auto
      hence "P\<^sub>0 \<in> set YS" "P\<^sub>1 \<in> set YS"
        using ASM defs closest_pair_7_c0[of YS P\<^sub>0 P\<^sub>1] closest_pair_7_c1[of YS P\<^sub>0 P\<^sub>1] by linarith+
      hence "P\<^sub>0 \<in> set ys" "P\<^sub>1 \<in> set ys"
        using filter_is_subset defs by fast+
      moreover have "P\<^sub>0 \<noteq> P\<^sub>1"
        using combine_c0_ne_c1 combine assms(2,3,4) by blast
      ultimately have "\<delta> \<le> dist P\<^sub>0 P\<^sub>1"
        using * defs sparse_def by blast
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
      (sortY xs, bf_closest_pair xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in

      let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
      (ys, combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys) 
  )"
  by pat_completeness auto
termination closest_pair_rec
  apply (relation "Wellfounded.measure (\<lambda>xs. length xs)")
  apply (auto simp add: split_at_take_drop_conv Let_def)
  done

lemma closest_pair_rec_simps:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "closest_pair_rec xs = (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let l = fst (hd xs\<^sub>R) in
    let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
    let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
    let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
    (ys, combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys) 
  )"
  using assms by (auto simp add: Let_def)

declare closest_pair_rec.simps [simp del]


lemma closest_pair_rec_ys:
  assumes "distinct xs" "(ys, cp) = closest_pair_rec xs"
  shows "set ys = set xs \<and> distinct ys \<and> sortedY ys"
  using assms
proof (induction xs arbitrary: ys cp rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    thus ?thesis using "1.prems" sortY
      by (auto simp add: closest_pair_rec.simps)
  next
    case False

    let ?xs = "split_at (?n div 2) xs"
    let ?xs\<^sub>L = "fst ?xs"
    let ?xs\<^sub>R = "snd ?xs"
    let ?l = "fst (hd ?xs\<^sub>R)"

    let ?cp\<^sub>L = "closest_pair_rec ?xs\<^sub>L"
    let ?ys\<^sub>L = "fst ?cp\<^sub>L"
    let ?c\<^sub>L = "snd ?cp\<^sub>L"
    let ?cp\<^sub>R = "closest_pair_rec ?xs\<^sub>R"
    let ?ys\<^sub>R = "fst ?cp\<^sub>R"
    let ?c\<^sub>R = "snd ?cp\<^sub>R"

    let ?ys = "merge (\<lambda>p. snd p) ?ys\<^sub>L ?ys\<^sub>R"
    let ?cp = "combine ?c\<^sub>L ?c\<^sub>R ?l ?ys"

    have "length ?xs\<^sub>L < length xs" "length ?xs\<^sub>R < length xs"
      using False by (auto simp add: split_at_take_drop_conv)
    moreover have "distinct ?xs\<^sub>L" "distinct ?xs\<^sub>R"
      using "1.prems"(1) by (auto simp add: split_at_take_drop_conv)
    ultimately have IH: "set ?xs\<^sub>L = set ?ys\<^sub>L" "set ?xs\<^sub>R = set ?ys\<^sub>R" 
                        "distinct ?ys\<^sub>L" "distinct ?ys\<^sub>R" 
                        "sortedY ?ys\<^sub>L" "sortedY ?ys\<^sub>R"
      using "1.IH" prod.collapse by blast+

    have "set xs = set ?xs\<^sub>L \<union> set ?xs\<^sub>R"
      by (auto simp add: set_take_drop split_at_take_drop_conv)
    hence SET: "set xs = set ?ys"
      using set_merge IH(1,2) by fast
    have "set ?xs\<^sub>L \<inter> set ?xs\<^sub>R = {}"
      using "1.prems"(1) by (auto simp add: split_at_take_drop_conv set_take_disj_set_drop_if_distinct)
    hence "set ?ys\<^sub>L \<inter> set ?ys\<^sub>R = {}"
      using IH(1,2) by blast
    hence DISTINCT: "distinct ?ys"
      using distinct_merge IH(3,4) by blast
    have SORTED: "sortedY ?ys"
      using IH(5,6) by (simp add: sortedY_def sorted_merge)

    have "(?ys, ?cp) = closest_pair_rec xs"
      using False closest_pair_rec_simps by (auto simp add: Let_def split: prod.splits)
    hence "(ys, cp) = (?ys, ?cp)"
      using "1.prems" by argo
    thus ?thesis
      using SET DISTINCT SORTED by blast
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
    hence "(c\<^sub>0, c\<^sub>1) = bf_closest_pair xs"
      using "1.prems"(3) closest_pair_rec.simps by simp
    thus ?thesis
      using "1.prems"(1,2) bf_closest_pair_c0_c1 by simp
  next
    case False

    let ?xs = "split_at (?n div 2) xs"
    let ?xs\<^sub>L = "fst ?xs"
    let ?xs\<^sub>R = "snd ?xs"
    let ?l = "fst (hd ?xs\<^sub>R)"

    let ?cp\<^sub>L = "closest_pair_rec ?xs\<^sub>L"
    let ?ys\<^sub>L = "fst ?cp\<^sub>L"
    let ?c\<^sub>L = "snd ?cp\<^sub>L"
    let ?c\<^sub>0\<^sub>L = "fst ?c\<^sub>L"
    let ?c\<^sub>1\<^sub>L = "snd ?c\<^sub>L"
    let ?cp\<^sub>R = "closest_pair_rec ?xs\<^sub>R"
    let ?ys\<^sub>R = "fst ?cp\<^sub>R"
    let ?c\<^sub>R = "snd ?cp\<^sub>R"
    let ?c\<^sub>0\<^sub>R = "fst ?c\<^sub>R"
    let ?c\<^sub>1\<^sub>R = "snd ?c\<^sub>R"

    let ?ys = "merge (\<lambda>p. snd p) ?ys\<^sub>L ?ys\<^sub>R"
    let ?cp = "combine ?c\<^sub>L ?c\<^sub>R ?l ?ys"
    let ?c\<^sub>0 = "fst ?cp"
    let ?c\<^sub>1 = "snd ?cp"

    have "1 < length ?xs\<^sub>L" "length ?xs\<^sub>L < length xs" "distinct ?xs\<^sub>L"
      using False "1.prems"(2) by (auto simp add: split_at_take_drop_conv)
    hence "?c\<^sub>0\<^sub>L \<in> set ?xs\<^sub>L" "?c\<^sub>1\<^sub>L \<in> set ?xs\<^sub>L" and IHL1: "?c\<^sub>0\<^sub>L \<noteq> ?c\<^sub>1\<^sub>L"
      using "1.IH" prod.collapse by metis+
    hence IHL2: "?c\<^sub>0\<^sub>L \<in> set xs" "?c\<^sub>1\<^sub>L \<in> set xs"
      using split_at_take_drop_conv in_set_takeD fst_conv by metis+

    have "1 < length ?xs\<^sub>R" "length ?xs\<^sub>R< length xs" "distinct ?xs\<^sub>R"
      using False "1.prems"(2) by (auto simp add: split_at_take_drop_conv)
    hence "?c\<^sub>0\<^sub>R \<in> set ?xs\<^sub>R" "?c\<^sub>1\<^sub>R \<in> set ?xs\<^sub>R" and IHR1: "?c\<^sub>0\<^sub>R\<noteq> ?c\<^sub>1\<^sub>R"
      using "1.IH" prod.collapse by metis+
    hence IHR2: "?c\<^sub>0\<^sub>R \<in> set xs" "?c\<^sub>1\<^sub>R \<in> set xs"
      using split_at_take_drop_conv in_set_dropD snd_conv by metis+

    have *: "(?ys, ?c\<^sub>0, ?c\<^sub>1) = closest_pair_rec xs"
      using False by (auto simp add: closest_pair_rec_simps Let_def split: prod.split)
    have YS: "set xs = set ?ys" "distinct ?ys"
      using "1.prems"(2) closest_pair_rec_ys * by blast+

    have "?c\<^sub>0 \<in> set xs"
      using combine_c0 IHL2(1) IHR2(1) YS prod.collapse by (metis (no_types, lifting))
    moreover have "?c\<^sub>1 \<in> set xs"
      using combine_c1 IHL2(2) IHR2(2) YS prod.collapse by (metis (no_types, lifting))
    moreover have "?c\<^sub>0 \<noteq> ?c\<^sub>1"
      using combine_c0_ne_c1 IHL1 IHR1 YS prod.collapse by (metis (no_types, lifting))
    ultimately show ?thesis
      using "1.prems"(3) * by (metis Pair_inject)
  qed
qed

lemma closest_pair_rec_dist:
  assumes "1 < length xs" "distinct xs" "sortedX xs" "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set xs)"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(c\<^sub>0, c\<^sub>1) = bf_closest_pair xs"
      using "1.prems"(4) closest_pair_rec.simps by simp
    thus ?thesis
      using "1.prems"(1,4) bf_closest_pair_dist by metis
  next
    case False

    define XS where "XS = split_at (?n div 2) xs"
    define XS\<^sub>L where "XS\<^sub>L = fst XS"
    define XS\<^sub>R where "XS\<^sub>R = snd XS"
    define L where "L = fst (hd XS\<^sub>R)"
    note divide_defs = XS_def XS\<^sub>L_def XS\<^sub>R_def L_def

    define CP\<^sub>L where "CP\<^sub>L = closest_pair_rec XS\<^sub>L"
    define YS\<^sub>L where "YS\<^sub>L = fst CP\<^sub>L"
    define C\<^sub>L where "C\<^sub>L = snd CP\<^sub>L"
    define C\<^sub>0\<^sub>L where "C\<^sub>0\<^sub>L = fst C\<^sub>L"
    define C\<^sub>1\<^sub>L where "C\<^sub>1\<^sub>L = snd C\<^sub>L"
    define CP\<^sub>R where "CP\<^sub>R = closest_pair_rec XS\<^sub>R"
    define YS\<^sub>R where "YS\<^sub>R = fst CP\<^sub>R"
    define C\<^sub>R where "C\<^sub>R = snd CP\<^sub>R"
    define C\<^sub>0\<^sub>R where "C\<^sub>0\<^sub>R = fst C\<^sub>R"
    define C\<^sub>1\<^sub>R where "C\<^sub>1\<^sub>R = snd C\<^sub>R"
    note conquer_defs = CP\<^sub>L_def YS\<^sub>L_def C\<^sub>L_def C\<^sub>0\<^sub>L_def C\<^sub>1\<^sub>L_def CP\<^sub>R_def YS\<^sub>R_def C\<^sub>R_def C\<^sub>0\<^sub>R_def C\<^sub>1\<^sub>R_def

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define C where "C = combine C\<^sub>L C\<^sub>R L YS"
    define C\<^sub>0 where "C\<^sub>0 = fst C"
    define C\<^sub>1 where "C\<^sub>1 = snd C"
    note combine_defs = YS_def C_def C\<^sub>0_def C\<^sub>1_def

    have XSLR: "XS\<^sub>L = take (?n div 2) xs" "XS\<^sub>R = drop (?n div 2) xs"
      using divide_defs by (auto simp add: split_at_take_drop_conv)

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>L" "sortedX XS\<^sub>L"
      using "1.prems"(2,3) XSLR by (auto simp add: sortedX_def sorted_wrt_take)
    moreover have "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using XSLR by (auto simp add: divide_defs conquer_defs)
    ultimately have L: "sparse (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set XS\<^sub>L)"
                       "set XS\<^sub>L = set YS\<^sub>L" "C\<^sub>0\<^sub>L \<noteq> C\<^sub>1\<^sub>L"
      using 1 closest_pair_rec_ys closest_pair_rec_c0_c1 by blast+
    hence IHL: "sparse (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set YS\<^sub>L)"
      by argo

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>R" "sortedX XS\<^sub>R"
      using "1.prems"(2,3) XSLR by (auto simp add: sortedX_def sorted_wrt_drop)
    moreover have "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using XSLR by (auto simp add: divide_defs conquer_defs)
    ultimately have R: "sparse (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set XS\<^sub>R)"
                       "set XS\<^sub>R = set YS\<^sub>R" "C\<^sub>0\<^sub>R \<noteq> C\<^sub>1\<^sub>R"
      using 1 closest_pair_rec_ys closest_pair_rec_c0_c1 by blast+
    hence IHR: "sparse (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set YS\<^sub>R)"
      by argo

    have *: "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False by (auto simp add: closest_pair_rec_simps Let_def divide_defs conquer_defs combine_defs split: prod.split)

    have "set xs = set YS" "distinct YS" "sortedY YS"
      using "1.prems"(2) closest_pair_rec_ys * by blast+
    moreover have "\<forall>p \<in> set YS\<^sub>L. fst p \<le> L"
      using False "1.prems"(3) XSLR L_def L(2) sortedX_take_less_hd_drop by simp
    moreover have "\<forall>p \<in> set YS\<^sub>R. L \<le> fst p"
      using False "1.prems"(3) XSLR L_def R(2) sortedX_hd_drop_less_drop by simp
    moreover have "set YS = set YS\<^sub>L \<union> set YS\<^sub>R"
      using set_merge combine_defs by fast
    moreover have "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      by (auto simp add: divide_defs conquer_defs combine_defs)
    ultimately have "sparse (dist C\<^sub>0 C\<^sub>1) (set xs)"
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
  shows "sparse (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms sortX closest_pair_rec_dist[of "sortX ps"] unfolding closest_pair_def
  by (auto split: prod.splits)

end
