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

section "Implementations"

subsection "Find_closest naive"

fun find_closest :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest p [] = undefined"
| "find_closest p [c] = c"
| "find_closest p (c\<^sub>0 # cs) = (
    let c\<^sub>1 = find_closest p cs in
    if dist p c\<^sub>0 \<le> dist p c\<^sub>1 then c\<^sub>1
    else c\<^sub>0
  )"

subsection "Find_closest optimized"

fun find_closest_\<delta> :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_\<delta> p \<delta> [] = undefined"
| "find_closest_\<delta> p \<delta> [c] = c"
| "find_closest_\<delta> p \<delta> (c\<^sub>0 # cs) = (
    if \<delta> \<le> snd c\<^sub>0 - snd p then c\<^sub>0
    else
      let c\<^sub>1 = find_closest_\<delta> p \<delta> cs in
      if dist p c\<^sub>0 \<le> dist p c\<^sub>1 then c\<^sub>0
      else c\<^sub>1
  )"

subsection "Approach A"

fun closest_pair_combine_A :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_combine_A [] = undefined"
| "closest_pair_combine_A [p] = undefined"
| "closest_pair_combine_A [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_combine_A (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_combine_A ps in
    let c = find_closest p\<^sub>0 (take 7 ps) in
    \<comment>\<open> let c = find_closest_\<delta> p\<^sub>0 (min \<delta> (dist c\<^sub>0 c\<^sub>1)) ps in *) \<close>
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 c then (c\<^sub>0, c\<^sub>1)
    else (p\<^sub>0, c) 
  )"

subsection "Approach B"

fun closest_pair_combine_B :: "real \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> point * point" where
  "closest_pair_combine_B \<delta> [] _ = undefined"
| "closest_pair_combine_B \<delta> _ [] = undefined"
| "closest_pair_combine_B \<delta> [p] [c] = (p, c)"
| "closest_pair_combine_B \<delta> (p # ps) [c] = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_combine_B \<delta> ps [c] in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p c then (c\<^sub>0, c\<^sub>1)
    else (p, c) 
  )"
| "closest_pair_combine_B \<delta> [p] (c # cs) = (
    if snd c < snd p then
      closest_pair_combine_B \<delta> [p] cs
    else
      (p, find_closest p (take 4 (c # cs)))
      \<comment>\<open> (p, find_closest_\<delta> p \<delta> (c # cs)) \<close>
  )"
| "closest_pair_combine_B \<delta> (p\<^sub>0 # ps) (c # cs) = (
    if snd c < snd p\<^sub>0 then
      closest_pair_combine_B \<delta> (p\<^sub>0 # ps) cs
    else
      let (c\<^sub>0, c\<^sub>1) = closest_pair_combine_B \<delta> ps (c # cs) in
      let p\<^sub>1 = find_closest p\<^sub>0 (take 4 (c # cs)) in
      \<comment>\<open> let p\<^sub>1 = find_closest_\<delta> p\<^sub>0 (min \<delta> (dist c\<^sub>0 c\<^sub>1)) (c # cs) in \<close>
      if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then (c\<^sub>0, c\<^sub>1)
      else (p\<^sub>0, p\<^sub>1)
  )"

fun closest_pair_combine_B_it :: "real \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> point * point" where
  "closest_pair_combine_B_it \<delta> c\<^sub>0 c\<^sub>1 (p # ps) (c # cs) = (
    if snd c < snd p then
      closest_pair_combine_B_it \<delta> c\<^sub>0 c\<^sub>1 (p # ps) cs
    else
      let p' = find_closest p (take 4 (c # cs)) in
      \<comment>\<open> let p' = find_closest_\<delta> p \<delta> (c # cs) in \<close>
      let \<delta>' = min \<delta> (dist p p') in
      if \<delta> \<le> \<delta>' then
        closest_pair_combine_B_it \<delta> c\<^sub>0 c\<^sub>1 ps (c # cs)
      else
        closest_pair_combine_B_it \<delta>' p p' ps (c # cs)
  )"
| "closest_pair_combine_B_it \<delta> c\<^sub>0 c\<^sub>1 _ _ = (c\<^sub>0, c\<^sub>1)"

section "Functional Correctness"

subsection "Defining Sparsity"

definition min_dist :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "min_dist \<delta> ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> \<delta> \<le> dist p\<^sub>0 p\<^sub>1)"

subsection "The Geometric Argument"

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

lemma closest_pair_in_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "y\<^sub>1 \<in> set ys" "dist y\<^sub>0 y\<^sub>1 < \<delta>"
  shows "y\<^sub>1 \<in> set (take 7 ys)"
  sorry

subsection "Finding the closest pair given Sparsity"

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

lemma find_closest_dist:
  "\<forall>p \<in> set ps. dist p\<^sub>0 (find_closest p\<^sub>0 ps) \<le> dist p\<^sub>0 p"
  sorry

lemma find_closest_dist_take_7:
  assumes "distinct (y\<^sub>0 # ys)" "sortedY (y\<^sub>0 # ys)" "0 < length ys" "0 < \<delta>" "set (y\<^sub>0 # ys) = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set (y\<^sub>0 # ys). l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<exists>y\<^sub>1 \<in> set ys. dist y\<^sub>0 y\<^sub>1 < \<delta>"
  shows "\<forall>y\<^sub>1 \<in> set ys. dist y\<^sub>0 (find_closest y\<^sub>0 (take 7 ys)) \<le> dist y\<^sub>0 y\<^sub>1"
  sorry

lemma closest_pair_combine_dist:
  assumes "distinct ys" "sortedY ys" "1 < length ys" "0 < \<delta>" "set ys = ys\<^sub>L \<union> ys\<^sub>R"
  assumes "\<forall>p \<in> set ys. l - \<delta> \<le> fst p \<and> fst p \<le> l + \<delta>"
  assumes "\<forall>p \<in> ys\<^sub>L. fst p \<le> l" "\<forall>p \<in> ys\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ys\<^sub>L" "min_dist \<delta> ys\<^sub>R"
  assumes "\<exists>p\<^sub>0 p\<^sub>1. p\<^sub>0 \<in> set ys \<and> p\<^sub>1 \<in> set ys \<and> p\<^sub>0 \<noteq> p\<^sub>1 \<and> dist p\<^sub>0 p\<^sub>1 < \<delta>"
  assumes "(c\<^sub>0, c\<^sub>1) = closest_pair_combine ys"
  shows "min_dist (dist c\<^sub>0 c\<^sub>1) (set ys)"
  sorry

subsection "The Combine Step"

fun combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ys' = filter (\<lambda>p. l - dist c\<^sub>0 c\<^sub>1 \<le> fst p \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1) ys in
    if length ys' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_combine ys' in
      if dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1 then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

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

subsection "The Complete Divide and Conquer Algorithm"

fun closest_pair_rec :: "point list \<Rightarrow> (point list * point * point)" where
  "closest_pair_rec xs = (
    let n = length xs in
    if n \<le> 3 then
      (sortY xs, bf_closest_pair xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in

      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys) 
  )"

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

end