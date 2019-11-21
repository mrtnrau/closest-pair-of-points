theory Closest_Pair_Code
imports
  Closest_Pair
  "HOL-Library.Code_Target_Numeral"
begin

section "Closest Pair Of Points Code Export"

subsection "length"

fun length_it' :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "length_it' acc [] = acc"
| "length_it' acc (x#xs) = length_it' (acc+1) xs"

definition length_it :: "'a list \<Rightarrow> nat" where
  "length_it xs = length_it' 0 xs"

lemma length_conv_length_it':
  "length xs + acc = length_it' acc xs"
  by (induction acc xs rule: length_it'.induct) auto

lemma length_conv_length_it[code_unfold]:
  "length xs = length_it xs"
  unfolding length_it_def using length_conv_length_it' add_0_right by metis


subsection "filter"

fun filter_it' :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_it' acc P [] = rev acc"
| "filter_it' acc P (x#xs) = (
    if P x then
      filter_it' (x#acc) P xs
    else
      filter_it' acc P xs
  )"

definition filter_it :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter_it P xs = filter_it' [] P xs"

lemma filter_conv_filter_it':
  "rev acc @ filter P xs = filter_it' acc P xs"
  by (induction acc P xs rule: filter_it'.induct) auto

lemma filter_conv_filter_it[code_unfold]:
  "filter P xs = filter_it P xs"
  unfolding filter_it_def using filter_conv_filter_it' append_Nil rev.simps(1) by metis


subsection "rev"

fun rev_it' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_it' acc [] = acc"
| "rev_it' acc (x#xs) = rev_it' (x#acc) xs"

definition rev_it :: "'a list \<Rightarrow> 'a list" where
  "rev_it xs = rev_it' [] xs"

lemma rev_conv_rev_it':
  "rev xs @ acc = rev_it' acc xs"
  by (induction acc xs rule: rev_it'.induct) auto

lemma rev_conv_rev_it[code_unfold]:
  "rev xs = rev_it xs"
  unfolding rev_it_def using rev_conv_rev_it' append_Nil2 by metis


subsection "split_at"

fun split_at_it' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at_it' acc n [] = (rev acc, [])"
| "split_at_it' acc n (x#xs) = (
    case n of
      0 \<Rightarrow> (rev acc, x#xs)
    | Suc m \<Rightarrow> split_at_it' (x#acc) m xs
  )"

definition split_at_it :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list)" where
  "split_at_it n xs = split_at_it' [] n xs"

lemma split_at_conv_split_at_it':
  assumes "(ts, ds) = split_at n xs" "(tsi, dsi) = split_at_it' acc n xs"
  shows "rev acc @ ts = tsi"
    and "ds = dsi"
  using assms
  apply (induction acc n xs arbitrary: ts rule: split_at_it'.induct)
  apply (auto simp: split_at.simps split: prod.splits nat.splits)
  done

lemma split_at_conv_split_at_it_prod:
  assumes "(ts, ds) = split_at n xs" "(ts', ds') = split_at_it n xs"
  shows "(ts, ds) = (ts', ds')"
  using assms unfolding split_at_it_def 
  using split_at_conv_split_at_it' rev.simps(1) append_Nil by fast+

lemma split_at_conv_split_at_it[code_unfold]:
  "split_at n xs = split_at_it n xs"
  using split_at_conv_split_at_it_prod surj_pair by metis


subsection "merge"

lemma merge_xs_Nil[simp]:
  "merge f xs [] = xs"
  by (cases xs) auto

fun merge_it' :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge_it' f acc [] [] = rev acc"
| "merge_it' f acc (x#xs) [] = merge_it' f (x#acc) xs []"
| "merge_it' f acc [] (y#ys) = merge_it' f (y#acc) ys []"
| "merge_it' f acc (x#xs) (y#ys) = (
    if f x \<le> f y then
      merge_it' f (x#acc) xs (y#ys)
    else
      merge_it' f (y#acc) (x#xs) ys
  )"

definition merge_it :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "merge_it f xs ys = merge_it' f [] xs ys"

lemma merge_conv_merge_it':
  "rev acc @ merge f xs ys = merge_it' f acc xs ys"
  by (induction f acc xs ys rule: merge_it'.induct) auto

lemma merge_conv_merge_it[code_unfold]:
  "merge f xs ys = merge_it f xs ys"
  unfolding merge_it_def using merge_conv_merge_it' rev.simps(1) append_Nil by metis


subsection "dist"

fun dist_code :: "point \<Rightarrow> point \<Rightarrow> int" where
  "dist_code p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

lemma dist_eq_sqrt_dist_code:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 = sqrt (dist_code p\<^sub>0 p\<^sub>1)"
  by (auto simp: dist_prod_def dist_real_def split: prod.splits) 

lemma dist_eq_dist_code_lt:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 < dist p\<^sub>2 p\<^sub>3 \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 < dist_code p\<^sub>2 p\<^sub>3"
  using dist_eq_sqrt_dist_code real_sqrt_less_iff by presburger

lemma dist_eq_dist_code_le:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>2 p\<^sub>3 \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 \<le> dist_code p\<^sub>2 p\<^sub>3"
  using dist_eq_sqrt_dist_code real_sqrt_le_iff by presburger

lemma dist_eq_dist_code_abs_1:
  fixes p\<^sub>0 :: point
  shows "\<bar>c\<bar> \<le> dist p\<^sub>0 p\<^sub>1 \<longleftrightarrow> c\<^sup>2 \<le> dist_code p\<^sub>0 p\<^sub>1"
  using dist_eq_sqrt_dist_code
  by (metis of_int_le_of_int_power_cancel_iff real_sqrt_abs real_sqrt_le_iff)

lemma dist_eq_dist_code_abs_2:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 \<le> \<bar>c\<bar> \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 \<le> c\<^sup>2"
  using dist_eq_sqrt_dist_code
  by (metis of_int_power_le_of_int_cancel_iff real_sqrt_abs real_sqrt_le_iff)

lemma dist_fst_abs:
  fixes p :: point and l :: int
  shows "dist p (l, snd p) = \<bar>fst p - l\<bar>"
proof -
  have "dist p (l, snd p) = sqrt ((real_of_int (fst p) - l)\<^sup>2)"
    by (simp add: dist_prod_def dist_real_def prod.case_eq_if)
  thus ?thesis
    by simp
qed

declare dist_code.simps [simp del]


subsection "find_closest"

fun find_closest_code :: "point \<Rightarrow> point list \<Rightarrow> (int * point)" where
  "find_closest_code p [] = undefined"
| "find_closest_code p [p\<^sub>0] = (dist_code p p\<^sub>0, p\<^sub>0)"
| "find_closest_code p (p\<^sub>0 # ps) = (
    let (\<delta>\<^sub>1, p\<^sub>1) = find_closest_code p ps in
    let \<delta>\<^sub>0 = dist_code p p\<^sub>0 in
    if \<delta>\<^sub>0 < \<delta>\<^sub>1 then
      (\<delta>\<^sub>0, p\<^sub>0)
    else
      (\<delta>\<^sub>1, p\<^sub>1)
  )"

lemma find_closest_code_dist_eq:
  "0 < length ps \<Longrightarrow> (\<delta>, c) = find_closest_code p ps \<Longrightarrow> \<delta> = dist_code p c"
  by (induction p ps rule: find_closest_code.induct)
     (auto simp: Let_def split: prod.splits if_splits)

lemma find_closest_code_eq:
  "0 < length ps \<Longrightarrow> c = find_closest p ps \<Longrightarrow> (\<delta>', c') = find_closest_code p ps \<Longrightarrow> c = c'"
proof (induction p ps arbitrary: c \<delta>' c' rule: find_closest.induct)
  case (3 p p\<^sub>0 p\<^sub>2 ps)
  define \<delta>\<^sub>0 \<delta>\<^sub>0' where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist p p\<^sub>0" "\<delta>\<^sub>0' = dist_code p p\<^sub>0"
  obtain \<delta>\<^sub>1 p\<^sub>1 \<delta>\<^sub>1' p\<^sub>1' where \<delta>\<^sub>1_def: "\<delta>\<^sub>1 = dist p p\<^sub>1" "p\<^sub>1 = find_closest p (p\<^sub>2 # ps)"
    "(\<delta>\<^sub>1', p\<^sub>1') = find_closest_code p (p\<^sub>2 # ps)"
    using prod.collapse by blast+
  note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
  have *: "p\<^sub>1 = p\<^sub>1'"
    using "3.IH" defs by simp
  hence "\<delta>\<^sub>0 < \<delta>\<^sub>1 \<longleftrightarrow> \<delta>\<^sub>0' < \<delta>\<^sub>1'"
    using find_closest_code_dist_eq[of "p\<^sub>2 # ps" \<delta>\<^sub>1' p\<^sub>1' p]
          dist_eq_dist_code_lt defs
    by simp
  thus ?case
    using "3.prems"(2,3) * defs by (auto split: prod.splits)
qed auto

declare find_closest_code.simps [simp del]


subsection "closest_pair_bf"

fun closest_pair_bf_code :: "point list \<Rightarrow> (int * point * point)" where
  "closest_pair_bf_code [] = undefined"
| "closest_pair_bf_code [p\<^sub>0] = undefined"
| "closest_pair_bf_code [p\<^sub>0, p\<^sub>1] = (dist_code p\<^sub>0 p\<^sub>1, p\<^sub>0, p\<^sub>1)"
| "closest_pair_bf_code (p\<^sub>0 # ps) = (
    let (\<delta>\<^sub>c, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code ps in
    let (\<delta>\<^sub>p, p\<^sub>1) = find_closest_code p\<^sub>0 ps in
    if \<delta>\<^sub>c \<le> \<delta>\<^sub>p then
      (\<delta>\<^sub>c, c\<^sub>0, c\<^sub>1)
    else
      (\<delta>\<^sub>p, p\<^sub>0, p\<^sub>1) 
  )"

lemma closest_pair_bf_code_dist_eq:
  "1 < length ps \<Longrightarrow> (\<delta>, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code ps \<Longrightarrow> \<delta> = dist_code c\<^sub>0 c\<^sub>1"
proof (induction ps arbitrary: \<delta> c\<^sub>0 c\<^sub>1 rule: closest_pair_bf_code.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  obtain \<delta>\<^sub>c c\<^sub>0 c\<^sub>1 where \<delta>\<^sub>c_def: "(\<delta>\<^sub>c, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code ?ps"
    by (metis prod_cases3)
  obtain \<delta>\<^sub>p p\<^sub>1 where \<delta>\<^sub>p_def: "(\<delta>\<^sub>p, p\<^sub>1) = find_closest_code p\<^sub>0 ?ps"
    using prod.collapse by blast
  note defs = \<delta>\<^sub>c_def \<delta>\<^sub>p_def
  have "\<delta>\<^sub>c = dist_code c\<^sub>0 c\<^sub>1"
    using "4.IH" defs by simp
  moreover have "\<delta>\<^sub>p = dist_code p\<^sub>0 p\<^sub>1"
    using find_closest_code_dist_eq defs by blast
  ultimately show ?case
    using "4.prems"(2) defs by (auto split: prod.splits if_splits)
qed auto

lemma closest_pair_bf_code_eq:
  assumes "1 < length ps" 
  assumes "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ps" "(\<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_bf_code ps"
  shows "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
  using assms
proof (induction ps arbitrary: c\<^sub>0 c\<^sub>1 \<delta>' c\<^sub>0' c\<^sub>1' rule: closest_pair_bf_code.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  obtain c\<^sub>0 c\<^sub>1 \<delta>\<^sub>c' c\<^sub>0' c\<^sub>1' where \<delta>\<^sub>c_def: "(c\<^sub>0, c\<^sub>1) = closest_pair_bf ?ps"
    "(\<delta>\<^sub>c', c\<^sub>0', c\<^sub>1') = closest_pair_bf_code ?ps"
    by (metis prod_cases3)
  obtain p\<^sub>1 \<delta>\<^sub>p' p\<^sub>1' where \<delta>\<^sub>p_def: "p\<^sub>1 = find_closest p\<^sub>0 ?ps"
    "(\<delta>\<^sub>p', p\<^sub>1') = find_closest_code p\<^sub>0 ?ps"
    using prod.collapse by blast
  note defs = \<delta>\<^sub>c_def \<delta>\<^sub>p_def
  have A: "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
    using "4.IH" defs by simp
  moreover have B: "p\<^sub>1 = p\<^sub>1'"
    using find_closest_code_eq defs by blast
  moreover have "\<delta>\<^sub>c' = dist_code c\<^sub>0' c\<^sub>1'"
    using defs closest_pair_bf_code_dist_eq[of ?ps] by simp
  moreover have "\<delta>\<^sub>p' = dist_code p\<^sub>0 p\<^sub>1'"
    using defs find_closest_code_dist_eq by blast
  ultimately have "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 \<longleftrightarrow> \<delta>\<^sub>c' \<le> \<delta>\<^sub>p'"
    by (simp add: dist_eq_dist_code_le)
  thus ?case
    using "4.prems"(2,3) defs A B by (auto simp: Let_def split: prod.splits)
qed auto


subsection "find_closest_\<delta>"

fun find_closest_\<delta>_code :: "point \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> (int * point)" where
  "find_closest_\<delta>_code _ _ [] = undefined"
| "find_closest_\<delta>_code p _ [p\<^sub>0] = (dist_code p p\<^sub>0, p\<^sub>0)"
| "find_closest_\<delta>_code p \<delta> (p\<^sub>0 # ps) = (
    let \<delta>\<^sub>0 = dist_code p p\<^sub>0 in
    if \<delta> \<le> (snd p\<^sub>0 - snd p)\<^sup>2 then
      (\<delta>\<^sub>0, p\<^sub>0)
    else
      let (\<delta>\<^sub>1, p\<^sub>1) = find_closest_\<delta>_code p (min \<delta> \<delta>\<^sub>0) ps in
      if \<delta>\<^sub>0 \<le> \<delta>\<^sub>1 then
        (\<delta>\<^sub>0, p\<^sub>0)
      else
        (\<delta>\<^sub>1, p\<^sub>1)
  )"

lemma find_closest_\<delta>_code_dist_eq:
  "0 < length ps \<Longrightarrow> (\<delta>\<^sub>c, c) = find_closest_\<delta>_code p \<delta> ps \<Longrightarrow> \<delta>\<^sub>c = dist_code p c"
proof (induction p \<delta> ps arbitrary: \<delta>\<^sub>c c rule: find_closest_\<delta>_code.induct)
  case (3 p \<delta> p\<^sub>0 p\<^sub>2 ps)
  show ?case
  proof cases
    assume "\<delta> \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
    thus ?thesis
      using "3.prems"(2) by simp
  next
    assume A: "\<not> \<delta> \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
    define \<delta>\<^sub>0 where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist_code p p\<^sub>0"
    obtain \<delta>\<^sub>1 p\<^sub>1 where \<delta>\<^sub>1_def: "(\<delta>\<^sub>1, p\<^sub>1) = find_closest_\<delta>_code p (min \<delta> \<delta>\<^sub>0) (p\<^sub>2 # ps)"
      by (metis surj_pair)
    note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
    have "\<delta>\<^sub>1 = dist_code p p\<^sub>1"
      using "3.IH"[of \<delta>\<^sub>0 \<delta>\<^sub>1 p\<^sub>1] A defs by simp
    thus ?thesis
      using defs "3.prems" by (auto simp: Let_def split: if_splits prod.splits)
  qed
qed simp_all

declare find_closest_\<delta>.simps [simp add]

lemma find_closest_\<delta>_code_eq:
  assumes "0 < length ps" "\<delta> = dist c\<^sub>0 c\<^sub>1" "\<delta>' = dist_code c\<^sub>0 c\<^sub>1" "sortedY (p # ps)"
  assumes "c = find_closest_\<delta> p \<delta> ps" "(\<delta>\<^sub>c', c') = find_closest_\<delta>_code p \<delta>' ps"
  shows "c = c'"
  using assms
proof (induction p \<delta> ps arbitrary: \<delta>' c\<^sub>0 c\<^sub>1 c \<delta>\<^sub>c' c' rule: find_closest_\<delta>.induct)
  case (3 p \<delta> p\<^sub>0 p\<^sub>2 ps)
  define \<delta>\<^sub>0 \<delta>\<^sub>0' where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist p p\<^sub>0" "\<delta>\<^sub>0' = dist_code p p\<^sub>0"
  obtain p\<^sub>1 \<delta>\<^sub>1' p\<^sub>1' where \<delta>\<^sub>1_def: "p\<^sub>1 = find_closest_\<delta> p (min \<delta> \<delta>\<^sub>0) (p\<^sub>2 # ps)"
    "(\<delta>\<^sub>1', p\<^sub>1') = find_closest_\<delta>_code p (min \<delta>' \<delta>\<^sub>0') (p\<^sub>2 # ps)"
    by (metis surj_pair)
  note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
  show ?case
  proof cases
    assume *: "\<delta> \<le> snd p\<^sub>0 - snd p"
    hence "\<delta>' \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
      using "3.prems"(2,3) dist_eq_dist_code_abs_2 by fastforce
    thus ?thesis
      using * "3.prems"(5,6) by simp
  next
    assume *: "\<not> \<delta> \<le> snd p\<^sub>0 - snd p"
    moreover have "0 \<le> snd p\<^sub>0 - snd p"
      using "3.prems"(4) sortedY_def by simp
    ultimately have A: "\<not> \<delta>' \<le> (snd p\<^sub>0 - snd p)\<^sup>2"
      using "3.prems"(2,3) dist_eq_dist_code_abs_2 by (smt of_int_nonneg)
    have "min \<delta> \<delta>\<^sub>0 = \<delta> \<longleftrightarrow> min \<delta>' \<delta>\<^sub>0' = \<delta>'" "min \<delta> \<delta>\<^sub>0 = \<delta>\<^sub>0 \<longleftrightarrow> min \<delta>' \<delta>\<^sub>0' = \<delta>\<^sub>0'"
      using "3.prems"(2,3) defs(1,2) dist_eq_dist_code_le by smt+
    moreover have "sortedY (p # p\<^sub>2 # ps)"
      using "3.prems"(4) sortedY_def by simp
    ultimately have B: "p\<^sub>1 = p\<^sub>1'"
      using "3.IH" "3.prems"(2,3) * defs by (smt length_greater_0_conv list.discI)
    have "\<delta>\<^sub>1' = dist_code p p\<^sub>1'"
      using find_closest_\<delta>_code_dist_eq defs by blast
    hence "\<delta>\<^sub>0 \<le> dist p p\<^sub>1 \<longleftrightarrow> \<delta>\<^sub>0' \<le> \<delta>\<^sub>1'"
      using defs(1,2) dist_eq_dist_code_le by (simp add: B)
    thus ?thesis
      using "3.prems"(5,6) * A B defs by (auto simp: Let_def split: prod.splits)
  qed
qed auto


subsection "closest_pair_combine"

fun closest_pair_combine_code :: "(int * point * point) \<Rightarrow> point list \<Rightarrow> (int * point * point)" where
  "closest_pair_combine_code (\<delta>, c\<^sub>0, c\<^sub>1) [] = (\<delta>, c\<^sub>0, c\<^sub>1)"
| "closest_pair_combine_code (\<delta>, c\<^sub>0, c\<^sub>1) [p] = (\<delta>, c\<^sub>0, c\<^sub>1)"
| "closest_pair_combine_code (\<delta>, c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = (
    let (\<delta>', p\<^sub>1) = find_closest_\<delta>_code p\<^sub>0 \<delta> ps in
    if \<delta> \<le> \<delta>' then
      closest_pair_combine_code (\<delta>, c\<^sub>0, c\<^sub>1) ps
    else
      closest_pair_combine_code (\<delta>', p\<^sub>0, p\<^sub>1) ps
  )"

lemma closest_pair_combine_code_dist_eq:
  assumes "\<delta> = dist_code c\<^sub>0 c\<^sub>1" "(\<Delta>, C\<^sub>0, C\<^sub>1) = closest_pair_combine_code (\<delta>, c\<^sub>0, c\<^sub>1) ps"
  shows "\<Delta> = dist_code C\<^sub>0 C\<^sub>1"
  using assms
proof (induction "(\<delta>, c\<^sub>0, c\<^sub>1)" ps arbitrary: \<delta> c\<^sub>0 c\<^sub>1 \<Delta> C\<^sub>0 C\<^sub>1 rule: closest_pair_combine_code.induct)
  case (3 \<delta> c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  obtain \<delta>' p\<^sub>1 where \<delta>'_def: "(\<delta>', p\<^sub>1) = find_closest_\<delta>_code p\<^sub>0 \<delta> (p\<^sub>2 # ps)"
    by (metis surj_pair)
  hence A: "\<delta>' = dist_code p\<^sub>0 p\<^sub>1"
    using find_closest_\<delta>_code_dist_eq by blast
  show ?case
  proof (cases "\<delta> \<le> \<delta>'")
    case True
    obtain \<Delta>' C\<^sub>0' C\<^sub>1' where \<Delta>'_def: "(\<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_combine_code (\<delta>, c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      by (metis prod_cases4)
    note defs = \<delta>'_def \<Delta>'_def
    hence "\<Delta>' = dist_code C\<^sub>0' C\<^sub>1'"
      using "3.hyps"(1)[of "(\<delta>', p\<^sub>1)" \<delta>' p\<^sub>1] "3.prems"(1) True \<delta>'_def by blast
    moreover have "\<Delta> = \<Delta>'" "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs True "3.prems"(2) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  next
    case False
    obtain \<Delta>' C\<^sub>0' C\<^sub>1' where \<Delta>'_def: "(\<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_combine_code (\<delta>', p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      by (metis prod_cases4)
    note defs = \<delta>'_def \<Delta>'_def
    hence "\<Delta>' = dist_code C\<^sub>0' C\<^sub>1'"
      using "3.hyps"(2)[of "(\<delta>', p\<^sub>1)" \<delta>' p\<^sub>1] A False \<delta>'_def by blast
    moreover have "\<Delta> = \<Delta>'" "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using defs False "3.prems"(2) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  qed
qed auto

declare closest_pair_combine.simps [simp add]

lemma closest_pair_combine_code_eq:
  assumes "\<delta> = dist c\<^sub>0 c\<^sub>1" "\<delta>' = dist_code c\<^sub>0 c\<^sub>1" "sortedY ps"
  assumes "(C\<^sub>0, C\<^sub>1) = closest_pair_combine (c\<^sub>0, c\<^sub>1) ps"
  assumes "(\<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_combine_code (\<delta>', c\<^sub>0, c\<^sub>1) ps"
  shows "C\<^sub>0 = C\<^sub>0' \<and> C\<^sub>1 = C\<^sub>1'"
  using assms
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: \<delta> \<delta>' c\<^sub>0 c\<^sub>1 C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' rule: closest_pair_combine.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  obtain p\<^sub>1 \<delta>\<^sub>p' p\<^sub>1' where \<delta>\<^sub>p_def: "p\<^sub>1 = find_closest_\<delta> p\<^sub>0 \<delta> (p\<^sub>2 # ps)"
    "(\<delta>\<^sub>p', p\<^sub>1') = find_closest_\<delta>_code p\<^sub>0 \<delta>' (p\<^sub>2 # ps)"
    by (metis surj_pair)
  hence A: "\<delta>\<^sub>p' = dist_code p\<^sub>0 p\<^sub>1'"
    using find_closest_\<delta>_code_dist_eq by blast
  have B: "p\<^sub>1 = p\<^sub>1'"
    using "3.prems"(1,2,3) \<delta>\<^sub>p_def find_closest_\<delta>_code_eq by blast
  show ?case
  proof (cases "\<delta> \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    hence C: "\<delta>' \<le> \<delta>\<^sub>p'"
      by (simp add: "3.prems"(1,2) A B dist_eq_dist_code_le)
    obtain C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<Delta>\<^sub>i' C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i' where \<Delta>\<^sub>i_def:
      "(C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) = closest_pair_combine (c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      "(\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') = closest_pair_combine_code (\<delta>', c\<^sub>0, c\<^sub>1) (p\<^sub>2 # ps)"
      by (metis prod_cases3)
    note defs = \<delta>\<^sub>p_def \<Delta>\<^sub>i_def
    have "sortedY (p\<^sub>2 # ps)"
      using "3.prems"(3) sortedY_def by simp
    hence "C\<^sub>0\<^sub>i = C\<^sub>0\<^sub>i' \<and> C\<^sub>1\<^sub>i = C\<^sub>1\<^sub>i'"
      using "3.hyps"(1) "3.prems"(1,2) True defs by blast
    moreover have "C\<^sub>0 = C\<^sub>0\<^sub>i" "C\<^sub>1 = C\<^sub>1\<^sub>i"
      using defs(1,3) True "3.prems"(1,4) apply (auto split: prod.splits) by (metis Pair_inject)+
    moreover have "\<Delta>' = \<Delta>\<^sub>i'" "C\<^sub>0' = C\<^sub>0\<^sub>i'" "C\<^sub>1' = C\<^sub>1\<^sub>i'"
      using defs(2,4) C "3.prems"(5) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  next
    case False
    hence C: "\<not> \<delta>' \<le> \<delta>\<^sub>p'"
      by (simp add: "3.prems"(1,2) A B dist_eq_dist_code_le)
    obtain C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<Delta>\<^sub>i' C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i' where \<Delta>\<^sub>i_def:
      "(C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) = closest_pair_combine (p\<^sub>0, p\<^sub>1) (p\<^sub>2 # ps)"
      "(\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') = closest_pair_combine_code (\<delta>\<^sub>p', p\<^sub>0, p\<^sub>1') (p\<^sub>2 # ps)"
      by (metis prod_cases3)
    note defs = \<delta>\<^sub>p_def \<Delta>\<^sub>i_def
    have "sortedY (p\<^sub>2 # ps)"
      using "3.prems"(3) sortedY_def by simp
    hence "C\<^sub>0\<^sub>i = C\<^sub>0\<^sub>i' \<and> C\<^sub>1\<^sub>i = C\<^sub>1\<^sub>i'"
      using "3.prems"(1) "3.hyps"(2) A B False defs by blast
    moreover have "C\<^sub>0 = C\<^sub>0\<^sub>i" "C\<^sub>1 = C\<^sub>1\<^sub>i"
      using defs(1,3) False "3.prems"(1,4) apply (auto split: prod.splits) by (metis Pair_inject)+
    moreover have "\<Delta>' = \<Delta>\<^sub>i'" "C\<^sub>0' = C\<^sub>0\<^sub>i'" "C\<^sub>1' = C\<^sub>1\<^sub>i'"
      using defs(2,4) C "3.prems"(5) apply (auto split: prod.splits) by (metis Pair_inject)+
    ultimately show ?thesis
      by simp
  qed
qed auto


subsection "combine"

fun combine_code :: "(int * point * point) \<Rightarrow> (int * point * point) \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> (int * point * point)" where
  "combine_code (\<delta>\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (\<delta>\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = (
    let (\<delta>, c\<^sub>0, c\<^sub>1) = if \<delta>\<^sub>L < \<delta>\<^sub>R then (\<delta>\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (\<delta>\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ps' = filter (\<lambda>p. (fst p - l)\<^sup>2 \<le> \<delta>) ps in
    closest_pair_combine_code (\<delta>, c\<^sub>0, c\<^sub>1) ps'
  )"

lemma combine_code_dist_eq:
  assumes "\<delta>\<^sub>L = dist_code p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L" "\<delta>\<^sub>R = dist_code p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R"
  assumes "(\<delta>, c\<^sub>0, c\<^sub>1) = combine_code (\<delta>\<^sub>L, p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (\<delta>\<^sub>R, p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "\<delta> = dist_code c\<^sub>0 c\<^sub>1"
  using assms by (auto simp: closest_pair_combine_code_dist_eq split: if_splits)

declare combine.simps [simp add]

lemma combine_code_eq:
  assumes "\<delta>\<^sub>L' = dist_code p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L" "\<delta>\<^sub>R' = dist_code p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R" "sortedY ps"
  assumes "(c\<^sub>0, c\<^sub>1) = combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  assumes "(\<delta>', c\<^sub>0', c\<^sub>1') = combine_code (\<delta>\<^sub>L', p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (\<delta>\<^sub>R', p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  shows "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
proof -
  obtain C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<Delta>\<^sub>i' C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i' where \<Delta>\<^sub>i_def:
    "(C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    "(\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') = (if \<delta>\<^sub>L' < \<delta>\<^sub>R' then (\<delta>\<^sub>L', p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (\<delta>\<^sub>R', p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
    by metis
  define ps' ps'' where ps'_def:
    "ps' = filter (\<lambda>p. dist p (l, snd p) \<le> dist C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i) ps"
    "ps'' = filter (\<lambda>p. (fst p - l)\<^sup>2 \<le> \<Delta>\<^sub>i') ps"
  obtain C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' where \<Delta>_def:
    "(C\<^sub>0, C\<^sub>1) = closest_pair_combine (C\<^sub>0\<^sub>i, C\<^sub>1\<^sub>i) ps'"
    "(\<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_combine_code (\<Delta>\<^sub>i', C\<^sub>0\<^sub>i', C\<^sub>1\<^sub>i') ps''"
    by (metis prod_cases3)
  note defs = \<Delta>\<^sub>i_def ps'_def \<Delta>_def
  have *: "C\<^sub>0\<^sub>i = C\<^sub>0\<^sub>i'" "C\<^sub>1\<^sub>i = C\<^sub>1\<^sub>i'" "\<Delta>\<^sub>i' = dist_code C\<^sub>0\<^sub>i' C\<^sub>1\<^sub>i'"
    using \<Delta>\<^sub>i_def assms(1,2,3,4) dist_eq_dist_code_lt by (auto split: if_splits)
  hence "\<And>p. \<bar>fst p - l\<bar> \<le> dist C\<^sub>0\<^sub>i C\<^sub>1\<^sub>i \<longleftrightarrow> (fst p - l)\<^sup>2 \<le> \<Delta>\<^sub>i'"
    using dist_eq_dist_code_abs_1 by (metis (mono_tags) of_int_abs)
  hence "ps' = ps''"
    using ps'_def dist_fst_abs by auto
  moreover have "sortedY ps'"
    using assms(3) ps'_def sortedY_def sorted_wrt_filter by blast
  ultimately have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
    using * closest_pair_combine_code_eq \<Delta>_def by blast+
  moreover have "C\<^sub>0 = c\<^sub>0" "C\<^sub>1 = c\<^sub>1"
    using assms(4) defs(1,3,5) apply (auto split: prod.splits) by (metis Pair_inject)+
  moreover have "C\<^sub>0' = c\<^sub>0'" "C\<^sub>1' = c\<^sub>1'"
    using assms(5) defs(2,4,6) apply (auto split: prod.splits) by (metis prod.inject)+
  ultimately show ?thesis
    by blast
qed


subsection "closest_pair_rec"

function closest_pair_rec_code :: "point list \<Rightarrow> (point list * int * point * point)" where
  "closest_pair_rec_code xs = (
    let n = length xs in
    if n \<le> 3 then
      (sortY xs, closest_pair_bf_code xs)
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec_code xs\<^sub>L in
      let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec_code xs\<^sub>R in

      let ys = merge snd ys\<^sub>L ys\<^sub>R in
      (ys, combine_code p\<^sub>L p\<^sub>R l ys) 
  )"
  by pat_completeness auto
termination closest_pair_rec_code
  apply (relation "Wellfounded.measure (\<lambda>xs. length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

lemma closest_pair_rec_code_simps:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "closest_pair_rec_code xs = (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let l = fst (hd xs\<^sub>R) in
    let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec_code xs\<^sub>L in
    let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec_code xs\<^sub>R in
    let ys = merge snd ys\<^sub>L ys\<^sub>R in
    (ys, combine_code p\<^sub>L p\<^sub>R l ys) 
  )"
  using assms by (auto simp: Let_def)

declare combine.simps combine_code.simps closest_pair_rec_code.simps [simp del]

lemma closest_pair_rec_code_dist_eq:
  assumes "1 < length xs" "(ys, \<delta>, c\<^sub>0, c\<^sub>1) = closest_pair_rec_code xs"
  shows "\<delta> = dist_code c\<^sub>0 c\<^sub>1"
  using assms
proof (induction xs arbitrary: ys \<delta> c\<^sub>0 c\<^sub>1 rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(\<delta>, c\<^sub>0, c\<^sub>1) = closest_pair_bf_code xs"
      using "1.prems"(2) closest_pair_rec_code.simps by simp
    thus ?thesis
      using "1.prems"(1) closest_pair_bf_code_dist_eq by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L \<Delta>\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where YSC\<^sub>0\<^sub>1\<^sub>L_def: "(YS\<^sub>L, \<Delta>\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec_code XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R \<Delta>\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where YSC\<^sub>0\<^sub>1\<^sub>R_def: "(YS\<^sub>R, \<Delta>\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec_code XS\<^sub>R"
      using prod.collapse by metis

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    obtain \<Delta> C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(\<Delta>, C\<^sub>0, C\<^sub>1) = combine_code (\<Delta>\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (\<Delta>\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHL: "\<Delta>\<^sub>L = dist_code C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L"
      using "1.IH" defs by metis+

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHR: "\<Delta>\<^sub>R = dist_code C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R"
      using "1.IH" defs by metis+

    have *: "(YS, \<Delta>, C\<^sub>0, C\<^sub>1) = closest_pair_rec_code xs"
      using False closest_pair_rec_code_simps defs by (auto simp: Let_def split: prod.split)
    moreover have "\<Delta> = dist_code C\<^sub>0 C\<^sub>1"
      using combine_code_dist_eq IHL IHR C\<^sub>0\<^sub>1_def by blast
    ultimately show ?thesis
      using "1.prems"(2) * by (metis Pair_inject)
  qed
qed

lemma closest_pair_rec_ys_eq:
  assumes "1 < length xs"
  assumes "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  assumes "(ys', \<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_rec_code xs"
  shows "ys = ys'"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 ys' \<delta>' c\<^sub>0' c\<^sub>1' rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "ys = sortY xs"
      using "1.prems"(2) closest_pair_rec.simps by simp
    moreover have "ys' = sortY xs"
      using "1.prems"(3) closest_pair_rec_code.simps by (simp add: True)
    ultimately show ?thesis
      using "1.prems"(1) by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L YS\<^sub>L' \<Delta>\<^sub>L' C\<^sub>0\<^sub>L' C\<^sub>1\<^sub>L' where YSC\<^sub>0\<^sub>1\<^sub>L_def:
      "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      "(YS\<^sub>L', \<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') = closest_pair_rec_code XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R YS\<^sub>R' \<Delta>\<^sub>R' C\<^sub>0\<^sub>R' C\<^sub>1\<^sub>R' where YSC\<^sub>0\<^sub>1\<^sub>R_def:
      "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      "(YS\<^sub>R', \<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') = closest_pair_rec_code XS\<^sub>R"
      using prod.collapse by metis

    define YS YS' where YS_def:
      "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
      "YS' = merge (\<lambda>p. snd p) YS\<^sub>L' YS\<^sub>R'"
    obtain C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' where C\<^sub>0\<^sub>1_def:
      "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      "(\<Delta>', C\<^sub>0', C\<^sub>1') = combine_code (\<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') (\<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') L YS'"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHL: "YS\<^sub>L = YS\<^sub>L'"
      using "1.IH" defs by metis

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHR: "YS\<^sub>R = YS\<^sub>R'"
      using "1.IH" defs by metis

    have "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs(1,2,3,5,7,9)
      by (auto simp: Let_def split: prod.split)
    moreover have "(YS', \<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_rec_code xs"
      using False closest_pair_rec_code_simps defs(1,2,4,6,8,10)
      by (auto simp: Let_def split: prod.split)
    moreover have "YS = YS'"
      using IHL IHR YS_def by simp
    ultimately show ?thesis
      by (metis "1.prems"(2,3) Pair_inject)
  qed
qed

lemma closest_pair_rec_code_eq:
  assumes "1 < length xs"
  assumes "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec xs"
  assumes "(ys', \<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_rec_code xs"
  shows "c\<^sub>0 = c\<^sub>0' \<and> c\<^sub>1 = c\<^sub>1'"
  using assms
proof (induction xs arbitrary: ys c\<^sub>0 c\<^sub>1 ys' \<delta>' c\<^sub>0' c\<^sub>1' rule: length_induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof (cases "?n \<le> 3")
    case True
    hence "(c\<^sub>0, c\<^sub>1) = closest_pair_bf xs"
      using "1.prems"(2) closest_pair_rec.simps by simp
    moreover have "(\<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_bf_code xs"
      using "1.prems"(3) closest_pair_rec_code.simps by (simp add: True)
    ultimately show ?thesis
      using "1.prems"(1) closest_pair_bf_code_eq by simp
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS\<^sub>L\<^sub>R_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) xs"
      using prod.collapse by blast
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L YS\<^sub>L' \<Delta>\<^sub>L' C\<^sub>0\<^sub>L' C\<^sub>1\<^sub>L' where YSC\<^sub>0\<^sub>1\<^sub>L_def:
      "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      "(YS\<^sub>L', \<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') = closest_pair_rec_code XS\<^sub>L"
      using prod.collapse by metis
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R YS\<^sub>R' \<Delta>\<^sub>R' C\<^sub>0\<^sub>R' C\<^sub>1\<^sub>R' where YSC\<^sub>0\<^sub>1\<^sub>R_def:
      "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      "(YS\<^sub>R', \<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') = closest_pair_rec_code XS\<^sub>R"
      using prod.collapse by metis

    define YS YS' where YS_def:
      "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
      "YS' = merge (\<lambda>p. snd p) YS\<^sub>L' YS\<^sub>R'"
    obtain C\<^sub>0 C\<^sub>1 \<Delta>' C\<^sub>0' C\<^sub>1' where C\<^sub>0\<^sub>1_def:
      "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      "(\<Delta>', C\<^sub>0', C\<^sub>1') = combine_code (\<Delta>\<^sub>L', C\<^sub>0\<^sub>L', C\<^sub>1\<^sub>L') (\<Delta>\<^sub>R', C\<^sub>0\<^sub>R', C\<^sub>1\<^sub>R') L YS'"
      using prod.collapse by metis
    note defs = XS\<^sub>L\<^sub>R_def L_def YSC\<^sub>0\<^sub>1\<^sub>L_def YSC\<^sub>0\<^sub>1\<^sub>R_def YS_def C\<^sub>0\<^sub>1_def

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHL: "C\<^sub>0\<^sub>L = C\<^sub>0\<^sub>L'" "C\<^sub>1\<^sub>L = C\<^sub>1\<^sub>L'"
      using "1.IH" defs by metis+

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length xs"
      using False "1.prems"(1) defs by (auto simp: split_at_take_drop_conv)
    hence IHR: "C\<^sub>0\<^sub>R = C\<^sub>0\<^sub>R'" "C\<^sub>1\<^sub>R = C\<^sub>1\<^sub>R'"
      using "1.IH" defs by metis+

    have "sortedY YS\<^sub>L" "sortedY YS\<^sub>R"
      using closest_pair_rec_set_length_sortedY YSC\<^sub>0\<^sub>1\<^sub>L_def(1) YSC\<^sub>0\<^sub>1\<^sub>R_def(1) by blast+
    hence "sortedY YS"
      using sorted_merge sortedY_def YS_def by blast
    moreover have "YS = YS'"
      using defs \<open>1 < length XS\<^sub>L\<close> \<open>1 < length XS\<^sub>R\<close> closest_pair_rec_ys_eq by blast
    moreover have "\<Delta>\<^sub>L' = dist_code C\<^sub>0\<^sub>L' C\<^sub>1\<^sub>L'" "\<Delta>\<^sub>R' = dist_code C\<^sub>0\<^sub>R' C\<^sub>1\<^sub>R'"
      using defs \<open>1 < length XS\<^sub>L\<close> \<open>1 < length XS\<^sub>R\<close> closest_pair_rec_code_dist_eq by blast+
    ultimately have "C\<^sub>0 = C\<^sub>0'" "C\<^sub>1 = C\<^sub>1'"
      using combine_code_eq IHL IHR C\<^sub>0\<^sub>1_def by blast+
    moreover have "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec xs"
      using False closest_pair_rec_simps defs(1,2,3,5,7,9)
      by (auto simp: Let_def split: prod.split)
    moreover have "(YS', \<Delta>', C\<^sub>0', C\<^sub>1') = closest_pair_rec_code xs"
      using False closest_pair_rec_code_simps defs(1,2,4,6,8,10)
      by (auto simp: Let_def split: prod.split)
    ultimately show ?thesis
      using "1.prems"(2,3) by (metis Pair_inject)
  qed
qed


subsection "closest_pair"

declare closest_pair.simps [simp add]

fun closest_pair_code :: "point list \<Rightarrow> (point * point)" where
  "closest_pair_code [] = undefined"
| "closest_pair_code [_] = undefined"
| "closest_pair_code ps = (let (_, _, c\<^sub>0, c\<^sub>1) = closest_pair_rec_code (sortX ps) in (c\<^sub>0, c\<^sub>1))"

lemma closest_pair_code_eq:
  "closest_pair ps = closest_pair_code ps"
proof (induction ps rule: induct_list012)
  case (3 x y zs)
  obtain ys c\<^sub>0 c\<^sub>1 ys' \<delta>' c\<^sub>0' c\<^sub>1' where *:
    "(ys, c\<^sub>0, c\<^sub>1) = closest_pair_rec (sortX (x # y # zs))"
    "(ys', \<delta>', c\<^sub>0', c\<^sub>1') = closest_pair_rec_code (sortX (x # y # zs))"
    by (metis prod_cases3)
  moreover have "1 < length (sortX (x # y # zs))"
    by (simp add: length_sortX)
  ultimately have "c\<^sub>0 = c\<^sub>0'" "c\<^sub>1 = c\<^sub>1'"
    using closest_pair_rec_code_eq by blast+
  thus ?case
    using * by (auto split: prod.splits)
qed auto


subsection "Code Export"

export_code closest_pair_code in OCaml
  module_name Verified

end