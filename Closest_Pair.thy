theory Closest_Pair
  imports "HOL-Analysis.Analysis"
begin

section "Closest Pair Of Points Functional Correctness"


(*
  TODO:
    - optimize dist computations
    - polish proofs
*)

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


subsection "Minimal Distance"

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


subsection "Closest Pair Brute Force Algorithm"

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
  using find_closest_set by metis

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
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  apply (auto simp: Let_def find_closest_set split: if_splits prod.splits)
  done

lemma closest_pair_bf_c1:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>1 \<in> set ps" 
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  apply (auto simp: Let_def find_closest_set split: if_splits prod.splits)
  using find_closest_set apply fastforce
  done

lemma closest_pair_bf_c0_ne_c1:
  "1 < length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
  apply (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  apply (auto simp: Let_def find_closest_ne split!: if_splits prod.splits)
  done

lemmas closest_pair_bf_c0_c1 = closest_pair_bf_c0 closest_pair_bf_c1 closest_pair_bf_c0_ne_c1

lemma closest_pair_bf_dist:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ps"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_bf.induct)
  case (4 p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  let ?ps = "p\<^sub>1 # p\<^sub>2 # ps"
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = closest_pair_bf ?ps"
    using prod.collapse by blast
  hence IH: "min_dist (dist C\<^sub>0 C\<^sub>1) (set ?ps)"
    using 4 by simp
  have *: "\<forall>p \<in> set ?ps. dist p\<^sub>0 (find_closest p\<^sub>0 ?ps) \<le> dist p\<^sub>0 p"
    using find_closest_dist by blast
  show ?case
  proof (cases "dist C\<^sub>0 C\<^sub>1 \<le> dist p\<^sub>0 (find_closest p\<^sub>0 ?ps)")
    case True
    hence "\<forall>p \<in> set ?ps. dist C\<^sub>0 C\<^sub>1 \<le> dist p\<^sub>0 p"
      using * by auto
    hence "min_dist (dist C\<^sub>0 C\<^sub>1) (set (p\<^sub>0 # ?ps))"
      using min_dist_identity IH by blast
    thus ?thesis
      using True "4.prems" C\<^sub>0\<^sub>1_def by (auto split: prod.splits)
  next
    case False
    hence "dist p\<^sub>0 (find_closest p\<^sub>0 ?ps) \<le> dist C\<^sub>0 C\<^sub>1"
      by simp
    hence "min_dist (dist p\<^sub>0 (find_closest p\<^sub>0 ?ps)) (set (p\<^sub>0 # ?ps))"
      using min_dist_update IH * by blast
    moreover have "(c\<^sub>0, c\<^sub>1) = (p\<^sub>0, (find_closest p\<^sub>0 ?ps))"
      using False "4.prems" C\<^sub>0\<^sub>1_def by (auto split: prod.splits)
    ultimately show ?thesis
      by simp
  qed
qed (auto simp: dist_commute min_dist_def)


subsection "Combination Algorithm"

fun find_closest_\<delta> :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_\<delta> p \<delta> [] = undefined"
| "find_closest_\<delta> p \<delta> [c] = c"
| "find_closest_\<delta> p \<delta> (c\<^sub>0 # cs) = (
    if \<delta> \<le> \<bar>snd c\<^sub>0 - snd p\<bar> then
      c\<^sub>0
    else
      let c\<^sub>1 = find_closest_\<delta> p \<delta> cs in
      if dist p c\<^sub>0 \<le> dist p c\<^sub>1 then
        c\<^sub>0
      else
        c\<^sub>1
  )"

lemma find_closest_\<delta>_set:
  "0 < length ps \<Longrightarrow> find_closest_\<delta> p \<delta> ps \<in> set ps"
  by (induction p \<delta> ps rule: find_closest_\<delta>.induct) (auto simp: Let_def)

lemma find_closest_\<delta>_ne:
  "0 < length ps \<Longrightarrow> p \<notin> set ps \<Longrightarrow> p \<noteq> find_closest_\<delta> p \<delta> ps"
  using find_closest_\<delta>_set by metis

lemma find_closest_\<delta>_dist:
  assumes "sortedY (p\<^sub>0 # ps)" "\<exists>p\<^sub>1 \<in> set ps. dist p\<^sub>0 p\<^sub>1 < \<delta>"
  shows "\<forall>p\<^sub>1 \<in> set ps. dist p\<^sub>0 (find_closest_\<delta> p\<^sub>0 \<delta> ps) \<le> dist p\<^sub>0 p\<^sub>1"
  using assms
proof (induction p\<^sub>0 \<delta> ps rule: find_closest_\<delta>.induct)
  case (3 p \<delta> c\<^sub>0 c\<^sub>1 cs)
  let ?cs = "c\<^sub>0 # c\<^sub>1 # cs"
  have *: "\<not> \<delta> \<le> snd c\<^sub>0 - snd p"
  proof (rule ccontr)
    assume *: "\<not> \<not> \<delta> \<le> snd c\<^sub>0 - snd p"
    have "\<forall>c \<in> set ?cs. snd p \<le> snd c"
      using "3.prems"(1) unfolding sortedY_def by simp
    moreover have "\<forall>c \<in> set ?cs. \<delta> \<le> snd c - snd p"
      using "3.prems"(1) * unfolding sortedY_def by auto
    ultimately have "\<forall>c \<in> set ?cs. \<delta> \<le> dist (snd p) (snd c)"
      using dist_real_def by simp
    hence "\<forall>c \<in> set ?cs. \<delta> \<le> dist p c"
      using dist_snd_le order_trans by blast
    thus False
      using "3.prems"(2) by fastforce
  qed
  show ?case
  proof (cases "\<exists>p\<^sub>1 \<in> set (c\<^sub>1 # cs). dist p p\<^sub>1 < \<delta>")
    case True
    thus ?thesis
      using * 3 unfolding sortedY_def by (auto simp: Let_def)
  next
    case False
    thus ?thesis
      using False "3.prems"(2) by (auto simp: Let_def)
  qed
qed auto

fun closest_pair_combine :: "real \<Rightarrow> point list \<Rightarrow> point * point" where
  "closest_pair_combine \<delta> [] = undefined"
| "closest_pair_combine \<delta> [p] = undefined"
| "closest_pair_combine \<delta> [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_combine \<delta> (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_combine \<delta> ps in
    let c = find_closest_\<delta> p\<^sub>0 (min \<delta> (dist c\<^sub>0 c\<^sub>1)) ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 c then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, c)
  )"

declare find_closest_\<delta>.simps [simp del]

lemma closest_pair_combine_c0:
  "2 \<le> length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_combine \<delta> ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
  apply (induction \<delta> ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine.induct)
  apply (auto simp: find_closest_\<delta>_set Let_def split: if_splits prod.splits)
  done

lemma closest_pair_combine_c1:
  "2 \<le> length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_combine \<delta> ps \<Longrightarrow> c\<^sub>1 \<in> set ps"
  apply (induction \<delta> ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine.induct)
  apply (auto simp: find_closest_\<delta>_set Let_def split: if_splits prod.splits)
  using find_closest_\<delta>_set apply fastforce
  done

lemma closest_pair_combine_c0_ne_c1:
  "2 \<le> length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_combine \<delta> ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
  apply (induction \<delta> ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine.induct)
  apply (auto simp add: find_closest_\<delta>_ne Let_def split: if_splits prod.splits)
  done

lemma closest_pair_combine_dist:
  assumes "2 \<le> length ps" "sortedY ps" "distinct ps" "(c\<^sub>0, c\<^sub>1) = closest_pair_combine \<delta> ps"
  assumes "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ps \<and> p\<^sub>1 \<in> set ps \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  using assms
proof (induction \<delta> ps arbitrary: c\<^sub>0 c\<^sub>1 rule: closest_pair_combine.induct)
  case (3 \<delta> p\<^sub>0 p\<^sub>1)
  thus ?case
    by (auto simp: min_dist_def dist_commute)
next
  case (4 \<delta> p\<^sub>0 p\<^sub>1 p\<^sub>2 ps)
  let ?ps = "p\<^sub>1 # p\<^sub>2 # ps"
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = closest_pair_combine \<delta> ?ps"
    using "4.prems"(4) by (auto split: prod.splits)
  let ?c = "find_closest_\<delta> p\<^sub>0 (min \<delta> (dist C\<^sub>0 C\<^sub>1)) ?ps"
  show ?case
  proof (cases "\<exists>p\<^sub>0 p\<^sub>1'. p\<^sub>0 \<in> set ?ps \<and> p\<^sub>1' \<in> set ?ps \<and> p\<^sub>0 \<noteq> p\<^sub>1' \<and> dist p\<^sub>0 p\<^sub>1' < \<delta>")
    case True
    hence IH: "min_dist (dist C\<^sub>0 C\<^sub>1) (set ?ps)"
      using 4 C\<^sub>0\<^sub>1_def unfolding sortedY_def by simp
    hence 1: "dist C\<^sub>0 C\<^sub>1 < \<delta>"
      using True min_dist_def by (meson le_less_trans)
    show ?thesis
    proof cases
      assume *: "\<exists>p \<in> set ?ps. dist p\<^sub>0 p < min \<delta> (dist C\<^sub>0 C\<^sub>1)"
      hence 2: "\<forall>p \<in> set ?ps. dist p\<^sub>0 ?c \<le> dist p\<^sub>0 p"
        using find_closest_\<delta>_dist "4.prems"(2) by simp
      hence "\<forall>p \<in> set (p\<^sub>0 # ?ps). p \<noteq> p\<^sub>0 \<longrightarrow> dist p\<^sub>0 ?c \<le> dist p\<^sub>0 p"
        by simp
      moreover have 3: "dist p\<^sub>0 ?c < min \<delta> (dist C\<^sub>0 C\<^sub>1)"
        using * 2 by auto
      ultimately have "min_dist (dist p\<^sub>0 ?c) (set (p\<^sub>0 # ?ps))"
        by (smt IH dist_commute insert_iff list.set(2) min_dist_def)
      moreover have "(p\<^sub>0, ?c) = closest_pair_combine \<delta> (p\<^sub>0 # ?ps)"
        using 3 C\<^sub>0\<^sub>1_def by (auto split: prod.split)
      ultimately show ?thesis
        by (metis "4.prems"(4) Pair_inject)
    next
      assume *: "\<not> (\<exists>p \<in> set ?ps. dist p\<^sub>0 p < min \<delta> (dist C\<^sub>0 C\<^sub>1))"
      hence "\<not> (\<exists>p \<in> set ?ps. dist p\<^sub>0 p < dist C\<^sub>0 C\<^sub>1)"
        using 1 by linarith
      hence 2: "dist C\<^sub>0 C\<^sub>1 \<le> dist p\<^sub>0 ?c"
        by (smt find_closest_\<delta>_set length_greater_0_conv list.discI)
      have "min_dist (dist C\<^sub>0 C\<^sub>1) (set (p\<^sub>0 # ?ps))"
        using 1 by (smt * IH min_dist_identity)
      moreover have "(C\<^sub>0, C\<^sub>1) = closest_pair_combine \<delta> (p\<^sub>0 # ?ps)"
        using * C\<^sub>0\<^sub>1_def 2 by (auto split:  prod.splits)
      ultimately show ?thesis
        by (metis "4.prems"(4) Pair_inject)
    qed
  next
    case False
    have "C\<^sub>0 \<in> set ?ps" "C\<^sub>1 \<in> set ?ps" "C\<^sub>0 \<noteq> C\<^sub>1"
      using closest_pair_combine_c0[of ?ps C\<^sub>0 C\<^sub>1 \<delta>]
            closest_pair_combine_c1[of ?ps C\<^sub>0 C\<^sub>1 \<delta>]
            closest_pair_combine_c0_ne_c1[of ?ps C\<^sub>0 C\<^sub>1 \<delta>]
            C\<^sub>0\<^sub>1_def "4.prems"(3)
      by auto
    hence 1: "\<delta> \<le> dist C\<^sub>0 C\<^sub>1"
      using False le_less_linear by blast
    hence "min \<delta> (dist C\<^sub>0 C\<^sub>1) = \<delta>"
      by simp
    moreover have *: "\<exists>p \<in> set ?ps. dist p\<^sub>0 p < \<delta>"
      using False "4.prems"(5) by (metis dist_commute set_ConsD)
    ultimately have 2: "\<forall>p \<in> set ?ps. dist p\<^sub>0 ?c \<le> dist p\<^sub>0 p"
      using find_closest_\<delta>_dist "4.prems"(2) by simp
    hence "\<forall>p \<in> set (p\<^sub>0 # ?ps). p \<noteq> p\<^sub>0 \<longrightarrow> dist p\<^sub>0 ?c \<le> dist p\<^sub>0 p"
      by simp
    moreover have 3: "dist p\<^sub>0 ?c < \<delta>"
      using * 2 by auto
    ultimately have "min_dist (dist p\<^sub>0 ?c) (set (p\<^sub>0 # ?ps))"
      using min_dist_def False by (smt dist_commute insert_iff list.set(2))
    moreover have "(p\<^sub>0, ?c) = closest_pair_combine \<delta> (p\<^sub>0 # ?ps)"
      using 1 3 C\<^sub>0\<^sub>1_def by (auto split: prod.split)
    ultimately show ?thesis
      using "4.prems"(4) by (metis Pair_inject)
  qed
qed auto

declare closest_pair_combine.simps [simp del]


subsection "Combine Phase"

fun combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let \<delta> = dist c\<^sub>0 c\<^sub>1 in
    let ps' = filter (\<lambda>p. \<bar>fst p - l\<bar> \<le> \<delta>) ps in
    if length ps' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_combine \<delta> ps' in
      if dist p\<^sub>0 p\<^sub>1 < \<delta> then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

lemma combine_c0:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "c\<^sub>0 = p\<^sub>0\<^sub>L \<or> c\<^sub>0 = p\<^sub>0\<^sub>R \<or> c\<^sub>0 \<in> set ps"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  let ?\<delta> = "dist C\<^sub>0 C\<^sub>1"
  let ?ps' = "filter (\<lambda>p. \<bar>fst p - l\<bar> \<le> ?\<delta>) ps"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine ?\<delta> ?ps'"
    using prod.collapse by blast
  note defs = C\<^sub>0\<^sub>1_def P\<^sub>0\<^sub>1_def

  show ?thesis
  proof cases
    assume "length ?ps' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>)"
    hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "C\<^sub>0 = p\<^sub>0\<^sub>L \<or> C\<^sub>0 = p\<^sub>0\<^sub>R"
      using defs prod.inject by metis
    ultimately show ?thesis
      using assms(1) by (metis prod.inject)
  next
    assume *: "\<not> (length ?ps' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>))"
    hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
      using assms(1) calculation by argo
    moreover have "P\<^sub>0 \<in> set ?ps'"
      using * defs closest_pair_combine_c0[of ?ps' P\<^sub>0 P\<^sub>1 ?\<delta>] by linarith
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma combine_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "c\<^sub>1 = p\<^sub>1\<^sub>L \<or> c\<^sub>1 = p\<^sub>1\<^sub>R \<or> c\<^sub>1 \<in> set ps"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  let ?\<delta> = "dist C\<^sub>0 C\<^sub>1"
  let ?ps' = "filter (\<lambda>p. \<bar>fst p - l\<bar> \<le> ?\<delta>) ps"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine ?\<delta> ?ps'"
    using prod.collapse by blast
  note defs = C\<^sub>0\<^sub>1_def P\<^sub>0\<^sub>1_def

  show ?thesis
  proof cases
    assume "length ?ps' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>)"
    hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "C\<^sub>1 = p\<^sub>1\<^sub>L \<or> C\<^sub>1 = p\<^sub>1\<^sub>R"
      using defs prod.inject by metis
    ultimately show ?thesis
      using assms(1) by (metis prod.inject)
  next
    assume *: "\<not> (length ?ps' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>))"
    hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
      using assms(1) calculation by argo
    moreover have "P\<^sub>1 \<in> set ?ps'"
      using * defs closest_pair_combine_c1[of ?ps' P\<^sub>0 P\<^sub>1 ?\<delta>] by linarith
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma combine_c0_ne_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R" "distinct ps"
  shows "c\<^sub>0 \<noteq> c\<^sub>1"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  let ?\<delta> = "dist C\<^sub>0 C\<^sub>1"
  let ?ps' = "filter (\<lambda>p. \<bar>fst p - l\<bar> \<le> ?\<delta>) ps"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine ?\<delta> ?ps'"
    using prod.collapse by blast
  note defs = C\<^sub>0\<^sub>1_def P\<^sub>0\<^sub>1_def

  show ?thesis
  proof cases
    assume "length ?ps' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>)"
    hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "C\<^sub>0 \<noteq> C\<^sub>1"
      using assms(2,3) defs prod.inject by metis
    ultimately show ?thesis
      using assms(1) by (metis prod.inject)
  next
    assume *: "\<not> (length ?ps' < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < ?\<delta>))"
    hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
      using defs by (auto simp: Let_def split!: prod.splits)
    moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
      using assms(1) calculation by argo
    moreover have "distinct ?ps'" "2 \<le> length ?ps'"
      using assms(4) * by auto
    moreover have "P\<^sub>0 \<noteq> P\<^sub>1"
      using * defs calculation closest_pair_combine_c0_ne_c1[of ?ps' P\<^sub>0 P\<^sub>1 ?\<delta>] by linarith
    ultimately show ?thesis
      by fastforce
  qed
qed

lemma set_band_filter_aux:
  assumes "p\<^sub>0 \<in> ps\<^sub>L" "p\<^sub>1 \<in> ps\<^sub>R" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "ps' = filter (\<lambda>p. \<bar>fst p - l\<bar> \<le> \<delta>) (ps :: point list)"
  shows "p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps'"
proof (rule ccontr)
  assume "\<not> (p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps')"
  then consider (A) "p\<^sub>0 \<notin> set ps' \<and> p\<^sub>1 \<notin> set ps'"
              | (B) "p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<notin> set ps'"
              | (C) "p\<^sub>0 \<notin> set ps' \<and> p\<^sub>1 \<in> set ps'"
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
  assumes "p\<^sub>0 \<in> set ps" "p\<^sub>1 \<in> set ps" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "min_dist \<delta> ps\<^sub>L" "min_dist \<delta> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "ps' = filter (\<lambda>p. \<bar>fst p - l\<bar> \<le> \<delta>) (ps :: point list)"
  shows "p\<^sub>0 \<in> set ps' \<and> p\<^sub>1 \<in> set ps'"
proof -
  have "p\<^sub>0 \<notin> ps\<^sub>L \<or> p\<^sub>1 \<notin> ps\<^sub>L" "p\<^sub>0 \<notin> ps\<^sub>R \<or> p\<^sub>1 \<notin> ps\<^sub>R"
    using assms(3,4,6,7) min_dist_def by force+
  then consider (A) "p\<^sub>0 \<in> ps\<^sub>L \<and> p\<^sub>1 \<in> ps\<^sub>R" | (B) "p\<^sub>0 \<in> ps\<^sub>R \<and> p\<^sub>1 \<in> ps\<^sub>L"
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

lemma combine_dist:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R"
  assumes "distinct ps" "sortedY ps" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "min_dist (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ps\<^sub>L" "min_dist (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
proof -
  obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    using prod.collapse by blast
  define \<delta> where "\<delta> = dist C\<^sub>0 C\<^sub>1"
  define PS where "PS = filter (\<lambda>p. \<bar>fst p - l\<bar> \<le> \<delta>) ps"
  obtain P\<^sub>0 P\<^sub>1 where P\<^sub>0\<^sub>1_def: "(P\<^sub>0, P\<^sub>1) = closest_pair_combine \<delta> PS"
    using prod.collapse by blast
  note defs = C\<^sub>0\<^sub>1_def \<delta>_def PS_def P\<^sub>0\<^sub>1_def

  have \<delta>_ps\<^sub>L: "min_dist \<delta> ps\<^sub>L"
    using assms(7,8) \<delta>_def C\<^sub>0\<^sub>1_def min_dist_def apply (auto split: if_splits) by force+
  have \<delta>_ps\<^sub>R: "min_dist \<delta> ps\<^sub>R"
    using assms(7,8) \<delta>_def C\<^sub>0\<^sub>1_def min_dist_def apply (auto split: if_splits) by force+

  show ?thesis
  proof (cases "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ps \<and> p\<^sub>1 \<in> set ps \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>")
    case True
    hence "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set PS \<and> p\<^sub>1 \<in> set PS \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
      using set_band_filter \<delta>_ps\<^sub>L \<delta>_ps\<^sub>R assms(6,9,10) PS_def by blast
    moreover have LPS: "2 \<le> length PS"
      using calculation by (cases PS) (auto simp add: Suc_le_eq)
    moreover have "distinct PS" "sortedY PS"
      using assms(4,5) sortedY_def sorted_wrt_filter PS_def by simp_all
    moreover have "(P\<^sub>0, P\<^sub>1) = closest_pair_combine \<delta> PS"
      using defs by auto
    ultimately have "min_dist (dist P\<^sub>0 P\<^sub>1) (set PS)"
      using closest_pair_combine_dist by auto
    moreover have "\<forall>p\<^sub>0 \<in> set ps. \<forall>p\<^sub>1 \<in> set ps. p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta> \<longrightarrow> p\<^sub>0 \<in> set PS \<and> p\<^sub>1 \<in> set PS"
      using set_band_filter assms(6,9,10) \<delta>_ps\<^sub>L \<delta>_ps\<^sub>R PS_def by blast
    ultimately have *: "min_dist (dist P\<^sub>0 P\<^sub>1) (set ps)"
      using True min_dist_def by smt
    
    show ?thesis
    proof cases
      assume "length PS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>)"
      moreover have "dist P\<^sub>0 P\<^sub>1 < \<delta>"
        using True * min_dist_def by force
      ultimately show ?thesis
        using LPS by linarith
    next
      assume "\<not> (length PS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>))"
      hence "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
        using defs by (auto simp: Let_def split!: prod.split)
      moreover have "(c\<^sub>0, c\<^sub>1) = (P\<^sub>0, P\<^sub>1)"
        using assms(1) calculation by argo
      ultimately show ?thesis
        using * by blast
    qed
  next
    case False
    hence *: "min_dist (dist C\<^sub>0 C\<^sub>1) (set ps)"
      using \<delta>_ps\<^sub>L \<delta>_ps\<^sub>R defs min_dist_def by (meson leI)
    thus ?thesis
    proof cases
      assume "length PS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>)"
      hence "(C\<^sub>0, C\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
        using defs by (auto simp: Let_def split!: prod.split)
      moreover have "(c\<^sub>0, c\<^sub>1) = (C\<^sub>0, C\<^sub>1)"
        using assms(1) calculation by argo
      ultimately show ?thesis
        using * by blast
    next
      assume ASM: "\<not> (length PS < 2 \<or> \<not> (dist P\<^sub>0 P\<^sub>1 < \<delta>))"
      hence combine: "(P\<^sub>0, P\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
        using defs by (auto simp: Let_def split!: prod.split)
      have "(P\<^sub>0, P\<^sub>1) = closest_pair_combine \<delta> PS"
        using defs by auto
      hence "P\<^sub>0 \<in> set PS" "P\<^sub>1 \<in> set PS"
        using ASM defs closest_pair_combine_c0[of PS P\<^sub>0 P\<^sub>1 \<delta>]
                       closest_pair_combine_c1[of PS P\<^sub>0 P\<^sub>1 \<delta>]
        by linarith+
      hence "P\<^sub>0 \<in> set ps" "P\<^sub>1 \<in> set ps"
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
    thus ?thesis
      using "1.prems"(1,2) closest_pair_bf_c0_c1 by simp
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
