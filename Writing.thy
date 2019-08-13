theory Writing
  imports
    "HOL-Analysis.Analysis"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Real_Approx_By_Float"
    "Landau_Symbols.Landau_More"
    "HOL-Library.Going_To_Filter"
    "Akra_Bazzi.Akra_Bazzi_Method"
    "Akra_Bazzi.Akra_Bazzi_Approximation"
begin


type_synonym point = "real * real"

section "Functional Correctness"

subsection "Merging and Sorting"

fun merge :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge f (x#xs) (y#ys) = (
    if f x \<le> f y then
      x # merge f xs (y#ys)
    else
      y # merge f (x#xs) ys
  )"
| "merge f [] ys = ys"
| "merge f xs [] = xs"

fun split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at n [] = ([], [])"
| "split_at n (x#xs) = (
    case n of
      0 \<Rightarrow> ([], x#xs)
    | Suc m \<Rightarrow>
      let (xs', ys') = split_at m xs in
      (x#xs', ys')
  )"

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
termination sorry

definition sortedX :: "point list \<Rightarrow> bool" where
  "sortedX ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1) ps"

definition sortedY :: "point list \<Rightarrow> bool" where
  "sortedY ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1) ps"

definition sortX :: "point list \<Rightarrow> point list" where
  "sortX ps = msort fst ps"

definition sortY :: "point list \<Rightarrow> point list" where
  "sortY ps = msort snd ps"


subsection "Sparsity"

definition min_dist :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "min_dist \<delta> ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1)"

lemma min_dist_identity:
  assumes "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)" "\<forall>p \<in> set ps. dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set (p\<^sub>0 # ps))"
  sorry

lemma min_dist_update:
  assumes "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  assumes "dist p\<^sub>0 p\<^sub>1 \<le> dist c\<^sub>0 c\<^sub>1" "\<forall>p \<in> set ps. dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>0 p"
  shows "min_dist (dist p\<^sub>0 p\<^sub>1) (set (p\<^sub>0 # ps))"
  sorry


subsection "Find Closest Neighbor"

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
  "min_dist (dist p\<^sub>0 (find_closest p\<^sub>0 ps)) (set ps)"
  sorry

lemma find_closest_set:
  "0 < length ps \<Longrightarrow> find_closest p\<^sub>0 ps \<in> set ps"
  sorry

lemma find_closest_ne:
  "0 < length ps \<Longrightarrow> p\<^sub>0 \<notin> set ps \<Longrightarrow> p\<^sub>0 \<noteq> find_closest p\<^sub>0 ps"
  sorry


subsection "Brute Force Closest Pair"

fun bf_closest_pair :: "point list \<Rightarrow> (point * point)" where
  "bf_closest_pair [] = undefined"
| "bf_closest_pair [p\<^sub>0] = undefined"
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
  sorry

lemma bf_closest_pair_c1:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps \<Longrightarrow> c\<^sub>1 \<in> set ps"
  sorry

lemma bf_closest_pair_c0_ne_c1:
  "1 < length ps \<Longrightarrow> distinct ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps \<Longrightarrow> c\<^sub>0 \<noteq> c\<^sub>1"
  sorry

lemma bf_closest_pair_dist:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = bf_closest_pair ps"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  sorry


subsection "Points in 2D Space"

lemma cbox_2D: 
  "cbox (x\<^sub>0::real, y\<^sub>0::real) (x\<^sub>1, y\<^sub>1) = { (x, y). x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1}"
  sorry

lemma cbox_max_dist:
  assumes "p\<^sub>0 = (x, y)" "p\<^sub>1 = (x + \<delta>, y + \<delta>)"
  assumes "(x\<^sub>0, y\<^sub>0) \<in> cbox p\<^sub>0 p\<^sub>1" "(x\<^sub>1, y\<^sub>1) \<in> cbox p\<^sub>0 p\<^sub>1" "0 \<le> \<delta>"
  shows "dist (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<le> sqrt 2 * \<delta>"
  sorry

lemma pigeonhole:
  assumes "finite T" "S \<subseteq> \<Union>T" "card T < card S"
  shows "\<exists>x \<in> S. \<exists>y \<in> S. \<exists>X \<in> T. x \<noteq> y \<and> x \<in> X \<and> y \<in> X"
  sorry

lemma max_points_square:
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + \<delta>, y + \<delta>)" "min_dist \<delta> ps" "0 < \<delta>"
  shows "card ps \<le> 4"
  sorry


subsection "Applying the Sparsity Information"

lemma closest_pair_in_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "y\<^sub>1 \<in> set ys" "dist y\<^sub>0 y\<^sub>1 < \<delta>"
  shows "y\<^sub>1 \<in> set (take 7 ys)"
  sorry

lemma find_closest_dist_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < length ys" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<exists>y\<^sub>1 \<in> set ys. dist y\<^sub>0 y\<^sub>1 < \<delta>"
  shows "\<forall>y\<^sub>1 \<in> set ys. dist y\<^sub>0 (find_closest y\<^sub>0 (take 7 ys)) \<le> dist y\<^sub>0 y\<^sub>1"
  sorry

fun closest_pair_7 :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_7 [] = undefined"
| "closest_pair_7 [p\<^sub>0] = undefined"
| "closest_pair_7 [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_7 (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = bf_closest_pair ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

lemma closest_pair_7_c0:
  "1 < length ps \<Longrightarrow> (c\<^sub>0, c\<^sub>1) = closest_pair_7 ps \<Longrightarrow> c\<^sub>0 \<in> set ps"
  sorry

lemma closest_pair_7_c1:
  assumes "1 < length ps" "(c\<^sub>0, c\<^sub>1) = closest_pair_7 ps"
  shows "c\<^sub>1 \<in> set ps"
  sorry

lemma closest_pair_7_c0_ne_c1:
  assumes "1 < length ps" "distinct ps" "(c\<^sub>0, c\<^sub>1) = closest_pair_7 ps"
  shows "c\<^sub>0 \<noteq> c\<^sub>1"
  sorry

lemma closest_7_dist:
  assumes "distinct ys" "sortedY ys" "1 < length ys" "0 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set ys. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
  assumes "(c\<^sub>0, c\<^sub>1) = closest_pair_7 ys"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ys)"
  sorry


subsection "Closest Pair"

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
  sorry

lemma combine_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
  shows "c\<^sub>1 = p\<^sub>1\<^sub>L \<or> c\<^sub>1 = p\<^sub>1\<^sub>R \<or> c\<^sub>1 \<in> set ys"
  sorry

lemma combine_c0_ne_c1:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R" "distinct ys"
  shows "c\<^sub>0 \<noteq> c\<^sub>1"
  sorry

lemma set_band_filter_aux:
  assumes "p\<^sub>0 \<in> ys\<^sub>L" "p\<^sub>1 \<in> ys\<^sub>R" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) (ys :: point list)"
  shows "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys'"
  sorry
  
lemma set_band_filter:
  assumes "p\<^sub>0 \<in> set ys" "p\<^sub>1 \<in> set ys" "p\<^sub>0 \<noteq> p\<^sub>1" "dist p\<^sub>0 p\<^sub>1 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "ys' = filter (\<lambda>p. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>) (ys :: point list)"
  shows "p\<^sub>0 \<in> set ys' \<and> p\<^sub>1 \<in> set ys'"
  sorry

lemma combine_dist:
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys" "p\<^sub>0\<^sub>L \<noteq> p\<^sub>1\<^sub>L" "p\<^sub>0\<^sub>R \<noteq> p\<^sub>1\<^sub>R"
  assumes "distinct ys" "sortedY ys" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "min_dist (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ys\<^sub>L" "min_dist (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ys\<^sub>R"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ys)"
  sorry

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
termination sorry

lemma closest_pair_rec_set_length_sortedY:
  assumes "(ys, cp) = closest_pair_rec xs"
  shows "set ys = set xs \<and> length ys = length xs \<and> sortedY ys"
  sorry

lemma closest_pair_rec_distinct:
  assumes "distinct xs" "(ys, cp) = closest_pair_rec xs"
  shows "distinct ys"
  sorry

lemma closest_pair_rec_c0_c1:
  assumes "1 < length xs" "distinct xs" "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  shows "c\<^sub>0 \<in> set xs \<and> c\<^sub>1 \<in> set xs \<and> c\<^sub>0 \<noteq> c\<^sub>1"
  sorry

lemma closest_pair_rec_dist:
  assumes "1 < length xs" "distinct xs" "sortedX xs" "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set xs)"
  sorry

definition closest_pair :: "point list \<Rightarrow> (point * point)" where
  "closest_pair ps = (let (ys, c) = closest_pair_rec (sortX ps) in c)"

theorem closest_pair_c0_c1:
  assumes "1 < length ps" "distinct ps" "(c\<^sub>0, c\<^sub>1) = closest_pair ps"
  shows "c\<^sub>0 \<in> set ps" "c\<^sub>1 \<in> set ps" "c\<^sub>0 \<noteq> c\<^sub>1"
  sorry

theorem closest_pair_dist:
  assumes "1 < length ps" "distinct ps" "(c\<^sub>0, c\<^sub>1) = closest_pair ps"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ps)"
  sorry


section "Time Analysis"

subsection "Approach: Simple Example"

fun t_length :: "'a list \<Rightarrow> nat" where
  "t_length [] = 0"
| "t_length (x#xs) = 1 + t_length xs"

lemma t_length:
  "t_length xs = length xs"
  sorry

definition length_cost :: "nat \<Rightarrow> real" where
  "length_cost n = n"

lemma t_length_conv_length_cost:
  "t_length xs = length_cost (length xs)"
  sorry

lemma t_length_bigo:
  "t_length \<in> O[length going_to at_top](length_cost o length)"
  sorry

(* filter, take, split_at, merge, msort, sortX, sortY *)

(* find_closest, bf_closest_pair, closest_pair_7, combine *)

subsection "Closest Pair"

function t_closest_pair_rec :: "point list \<Rightarrow> nat" where
  "t_closest_pair_rec xs = (
    let n = length xs in
    let t_l = t_length xs in
    if n \<le> 3 then
      t_l + t_sortY xs + t_bf_closest_pair xs
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let t_s = t_split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
      let t_cl = t_closest_pair_rec xs\<^sub>L in
      let t_cr = t_closest_pair_rec xs\<^sub>R in

      let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
      let t_m = t_merge (\<lambda>p. snd p) (ys\<^sub>L, ys\<^sub>R) in
      let t_c = t_combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys in
      t_l + t_s + t_cl + t_cr + t_m + t_c
  )"
  by pat_completeness auto
termination sorry

function closest_pair_rec_cost :: "nat \<Rightarrow> real" where
  "n \<le> 3 \<Longrightarrow> closest_pair_rec_cost n = length_cost n + sortY_cost n + bf_closest_pair_cost n"
| "3 < n \<Longrightarrow> closest_pair_rec_cost n = length_cost n + split_at_cost n + 
    closest_pair_rec_cost (nat \<lfloor>real n / 2\<rfloor>) + closest_pair_rec_cost (nat \<lceil>real n / 2\<rceil>) +
    merge_cost n + combine_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

lemma t_closest_pair_rec_conv_closest_pair_rec_cost:
  "t_closest_pair_rec ps \<le> closest_pair_rec_cost (length ps)"
  sorry

theorem closest_pair_rec_cost:
  "closest_pair_rec_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  by (master_theorem) sorry

theorem t_closest_pair_rec_bigo:
  "t_closest_pair_rec \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  sorry

definition t_closest_pair :: "point list \<Rightarrow> nat" where
  "t_closest_pair ps = t_sortX ps + t_closest_pair_rec (sortX ps)"

definition closest_pair_cost :: "nat \<Rightarrow> real" where
  "closest_pair_cost n = sortX_cost n + closest_pair_rec_cost n"

lemma t_closest_pair_conv_closest_pair_cost:
  "t_closest_pair ps \<le> closest_pair_cost (length ps)"
  sorry

theorem closest_pair_cost:
  "closest_pair_cost \<in> O(\<lambda>n. n * ln n)"
  sorry

theorem t_closest_pair_bigo:
  "t_closest_pair \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  sorry


section "Code Export and Performance Tests"

end