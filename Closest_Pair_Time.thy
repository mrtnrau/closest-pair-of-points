theory Closest_Pair_Time
imports 
  Closest_Pair
  "Landau_Symbols.Landau_More"
  "Akra_Bazzi.Akra_Bazzi_Method"
  "Akra_Bazzi.Akra_Bazzi_Approximation"
begin

section "Closest Pair Of Points Time Analysis"

subsection "length"

fun t_length :: "'a list \<Rightarrow> nat" where
  "t_length [] = 0"
| "t_length (x#xs) = 1 + t_length xs"

lemma t_length:
  "t_length xs = length xs"
  by (induction xs) auto

definition length_cost :: "nat \<Rightarrow> real" where
  "length_cost n = n"

lemma length_cost_nonneg[simp]:
  "0 \<le> length_cost n"
  unfolding length_cost_def by simp

lemma t_length_conv_length_cost:
  "t_length xs = length_cost (length xs)"
  unfolding length_cost_def using t_length by auto


subsection "filter"

fun t_filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_filter P [] = 0"
| "t_filter P (x#xs) = (
    if P x then
      1 + t_filter P xs
    else
      1 + t_filter P xs
  )"

lemma t_filter:
  "t_filter P xs = length xs"
  by (induction xs) auto

definition filter_cost :: "nat \<Rightarrow> real" where
  "filter_cost n = n"

lemma filter_cost_nonneg[simp]:
  "0 \<le> filter_cost n"
  unfolding filter_cost_def by simp

lemma t_filter_conv_filter_cost:
  "t_filter P xs = filter_cost (length xs)"
  unfolding filter_cost_def using t_filter by auto


subsection "take"

fun t_take :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_take n [] = 0"
| "t_take n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> 1 + t_take m xs
  )"

lemma t_take:
  "t_take n xs = min n (length xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition take_cost :: "nat \<Rightarrow> real" where
  "take_cost n = n"

lemma take_cost_nonneg[simp]:
  "0 \<le> take_cost n"
  unfolding take_cost_def by simp

lemma t_take_conv_take_cost:
  "t_take n xs \<le> take_cost (length xs)"
  unfolding take_cost_def by (auto simp add: min_def t_take)


subsection "split_at"

fun t_split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_split_at n [] = 0"
| "t_split_at n (x#xs) = (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> 1 + t_split_at m xs
  )"

lemma t_split_at:
  "t_split_at n xs = min n (length xs)"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition split_at_cost :: "nat \<Rightarrow> real" where
  "split_at_cost n = n"

lemma split_at_cost_nonneg[simp]:
  "0 \<le> split_at_cost n"
  unfolding split_at_cost_def by simp

lemma t_split_at_conv_split_at_cost:
  "t_split_at n xs \<le> split_at_cost (length xs)"
  unfolding split_at_cost_def by (auto simp add: min_def t_split_at)


subsection "merge"

fun t_merge :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_merge f (x#xs) (y#ys) = (
    if f x \<le> f y then
      1 + t_merge f xs (y#ys)
    else
      1 + t_merge f (x#xs) ys
  )"
| "t_merge f xs [] = 0"
| "t_merge f [] ys = 0"

lemma t_merge:
  "t_merge f xs ys \<le> length xs + length ys"
  by (induction f xs ys rule: t_merge.induct) auto

definition merge_cost :: "nat \<Rightarrow> real" where
  "merge_cost n = n"

lemma merge_cost_nonneg[simp]:
  "0 \<le> merge_cost n"
  unfolding merge_cost_def by simp

lemma t_merge_conv_merge_cost:
  "t_merge f xs ys \<le> merge_cost (length xs + length ys)"
  unfolding merge_cost_def by (metis of_nat_mono t_merge)


subsection "msort"

function t_msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_msort f [] = 0"
| "t_msort f [_] = 1"
| "t_msort f (x # y # xs') = (
    let xs = x # y # xs' in
    let n = length xs div 2 in
    let (l, r) = split_at n xs in
    t_length xs + t_split_at n xs + t_msort f l + t_msort f r + t_merge f l r
  )"
  by pat_completeness auto
termination t_msort
  apply (relation "Wellfounded.measure (\<lambda>(_, xs). length xs)")
  apply (auto simp add: split_at_take_drop_conv Let_def)
  done

function msort_cost :: "nat \<Rightarrow> real" where
  "msort_cost 0 = 0"
| "msort_cost 1 = 1"
| "2 \<le> n \<Longrightarrow> msort_cost n = length_cost n + split_at_cost n + 
    msort_cost (nat \<lfloor>real n / 2\<rfloor>) + msort_cost (nat \<lceil>real n / 2\<rceil>) + merge_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

definition sortX_cost :: "nat \<Rightarrow> real" where
  "sortX_cost = msort_cost"

definition sortY_cost :: "nat \<Rightarrow> real" where
  "sortY_cost = msort_cost"

declare t_length.simps t_split_at.simps t_merge.simps[simp del]


lemma t_msort_conv_msort_cost:
  "t_msort f xs \<le> msort_cost (length xs)"
proof (induction f xs rule: t_msort.induct)
  case (2 f x)
  thus ?case
    using msort_cost.simps(2) by auto
next
  case (3 f x y xs')

  define XS where "XS = x # y # xs'"
  define N where "N = length XS"
  define LR where "LR = split_at (N div 2) XS"
  define L where "L = fst LR"
  define R where "R = snd LR"
  note defs = XS_def N_def LR_def L_def R_def

  let ?LHS = "t_length XS + t_split_at (N div 2) XS + t_msort f L + t_msort f R + t_merge f L R"
  let ?RHS = "length_cost N + split_at_cost N + msort_cost (nat \<lfloor>real N / 2\<rfloor>) +
              msort_cost (nat \<lceil>real N / 2\<rceil>) + merge_cost N"

  have IHL: "t_msort f L \<le> msort_cost (length L)"
    using defs "3.IH"(1) prod.collapse by blast
  have IHR: "t_msort f R \<le> msort_cost (length R)"
    using defs "3.IH"(2) prod.collapse by blast

  have *: "length L = N div 2" "length R = N - N div 2"
    by (auto simp add: defs split_at_take_drop_conv)
  hence "(nat \<lfloor>real N / 2\<rfloor>) = length L" "(nat \<lceil>real N / 2\<rceil>) = length R"
    by linarith+
  hence IH: "t_msort f L \<le> msort_cost (nat \<lfloor>real N / 2\<rfloor>)"
            "t_msort f R \<le> msort_cost (nat \<lceil>real N / 2\<rceil>)"
    using IHL IHR by simp_all

  have "N = length L + length R"
    using * by linarith
  hence "t_merge f L R \<le> merge_cost N"
    using t_merge_conv_merge_cost by metis
  moreover have "t_length XS = length_cost N"
    using t_length_conv_length_cost defs by blast
  moreover have "t_split_at (N div 2) XS \<le> split_at_cost N"
    using t_split_at_conv_split_at_cost defs by blast
  ultimately have *: "?LHS \<le> ?RHS"
    using IH by simp
  moreover have "t_msort f XS = ?LHS"
    by (auto simp add: defs split: prod.split)
  moreover have "msort_cost N = ?RHS"
    by (simp add: defs)
  ultimately have "t_msort f XS \<le> msort_cost N"
    by presburger 
  thus ?case
    using XS_def N_def by blast
qed auto

lemma msort_cost_nonneg[simp]:
  "0 \<le> msort_cost n"
  by (induction n rule: msort_cost.induct) (auto simp del: One_nat_def)

lemma sortX_cost_nonneg[simp]:
  "0 \<le> sortX_cost n"
  unfolding sortX_cost_def by simp

lemma sortY_cost_nonneg[simp]:
  "0 \<le> sortY_cost n"
  unfolding sortY_cost_def by simp

theorem msort_cost:
  "msort_cost \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  by (master_theorem) (auto simp add: length_cost_def split_at_cost_def merge_cost_def)

corollary sortX_cost:
  "sortX_cost \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  unfolding sortX_cost_def using msort_cost by simp

corollary sortY_cost:
  "sortY_cost \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  unfolding sortY_cost_def using msort_cost by simp


subsection "find_closest"

fun t_find_closest :: "point \<Rightarrow> point list \<Rightarrow> nat" where
  "t_find_closest p\<^sub>0 [] = 0"
| "t_find_closest p\<^sub>0 [p] = 1"
| "t_find_closest p\<^sub>0 (p # ps) = (
    let c = find_closest p\<^sub>0 ps in
    let t = t_find_closest p\<^sub>0 ps in
    if dist p\<^sub>0 p < dist p\<^sub>0 c then
      1 + t
    else
      1 + t
  )"

lemma t_find_closest:
  "t_find_closest p ps = length ps"
  by (induction p ps rule: t_find_closest.induct) auto

definition find_closest_cost :: "nat \<Rightarrow> real" where
  "find_closest_cost n = n"

lemma find_closest_cost_nonneg[simp]:
  "0 \<le> find_closest_cost n"
  unfolding find_closest_cost_def by simp

lemma t_find_closest_conv_find_closest_cost:
  "t_find_closest p ps = find_closest_cost (length ps)"
  unfolding find_closest_cost_def using t_find_closest by auto


subsection "gen_closest_pair"

fun t_gen_closest_pair :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> nat" where
  "t_gen_closest_pair f [] = 0"
| "t_gen_closest_pair f [p\<^sub>0] = 1"
| "t_gen_closest_pair f [p\<^sub>0, p\<^sub>1] = 2"
| "t_gen_closest_pair f (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = gen_closest_pair f ps in
    let t_gen = t_gen_closest_pair f ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (f ps) in
    let t_find = t_find_closest p\<^sub>0 (f ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      1 + t_gen + t_find
    else
      1 + t_gen + t_find
  )"

lemma t_gen_closest_pair_id:
  "f = (\<lambda>ps. ps) \<Longrightarrow> t_gen_closest_pair f ps \<le> length ps * length ps"
proof (induction f ps rule: t_gen_closest_pair.induct)
  case (4 f p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  have "t_gen_closest_pair f ?ps \<le> length ?ps * length ?ps"
    using 4 prod_cases3 by metis
  thus ?case
    using "4.prems" t_find_closest by simp
qed auto

lemma t_gen_closest_pair_take_7:
  "f = take 7 \<Longrightarrow> t_gen_closest_pair f ps \<le> 8 * length ps"
proof (induction f ps rule: t_gen_closest_pair.induct)
  case (4 f p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  have "t_gen_closest_pair f ?ps \<le> 8 * length ?ps"
    using 4 prod_cases3 by metis
  thus ?case
    using "4.prems" t_find_closest by simp
qed auto


subsection "bf_closest_pair"

definition t_bf_closest_pair :: "point list \<Rightarrow> nat" where
  "t_bf_closest_pair ps = t_gen_closest_pair (\<lambda>ps. ps) ps"

lemma t_bf_closest_pair:
  "t_bf_closest_pair ps \<le> length ps * length ps"
  unfolding t_bf_closest_pair_def using t_gen_closest_pair_id by simp

definition bf_closest_pair_cost :: "nat \<Rightarrow> real" where
  "bf_closest_pair_cost n = n * n"

lemma bf_closest_pair_cost_nonneg[simp]:
  "0 \<le> bf_closest_pair_cost n"
  unfolding bf_closest_pair_cost_def by simp

lemma t_bf_closest_pair_conv_bf_closest_pair_cost:
  "t_bf_closest_pair ps \<le> bf_closest_pair_cost (length ps)"
  unfolding bf_closest_pair_cost_def using t_bf_closest_pair of_nat_mono by blast


subsection "closest_pair_7"

definition t_closest_pair_7 :: "point list \<Rightarrow> nat" where
  "t_closest_pair_7 ps = t_gen_closest_pair (take 7) ps"

lemma t_closest_pair_7:
  "t_closest_pair_7 ps \<le> 8 * length ps"
  unfolding t_closest_pair_7_def using t_gen_closest_pair_take_7 by simp

definition closest_pair_7_cost :: "nat \<Rightarrow> real" where
  "closest_pair_7_cost n = 8 * n"

lemma closest_pair_7_cost_nonneg[simp]:
  "0 \<le> closest_pair_7_cost n"
  unfolding closest_pair_7_cost_def by simp

lemma t_closest_pair_7_conv_closest_pair_7_cost:
  "t_closest_pair_7 ps \<le> closest_pair_7_cost (length ps)"
  unfolding closest_pair_7_cost_def using t_closest_pair_7 of_nat_mono by blast


subsection "combine"

fun t_combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> nat" where
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ys' = filter (\<lambda>p. l - dist c\<^sub>0 c\<^sub>1 \<le> fst p \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1) ys in
    let t_f = t_filter (\<lambda>p. l - dist c\<^sub>0 c\<^sub>1 \<le> fst p \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1) ys in
    if length ys' < 2 then
      t_f
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_7 ys' in
      let t_c = t_closest_pair_7 ys' in
      if dist p\<^sub>0 p\<^sub>1 < dist c\<^sub>0 c\<^sub>1 then
        t_f + t_c
      else
        t_f + t_c
  )"

lemma t_combine:
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys \<le> 9 * length ys"
proof -
  let ?c\<^sub>0\<^sub>1 = "(if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))"
  let ?c\<^sub>0 = "fst ?c\<^sub>0\<^sub>1"
  let ?c\<^sub>1 = "snd ?c\<^sub>0\<^sub>1"
  let ?P = "(\<lambda>p. l -  dist ?c\<^sub>0 ?c\<^sub>1 \<le> fst p \<and> fst p \<le> l +  dist ?c\<^sub>0 ?c\<^sub>1)"
  let ?ys' = "filter ?P ys"
  let ?t_f = "t_filter ?P ys"
  let ?p\<^sub>0\<^sub>1 = "closest_pair_7 ?ys'"
  let ?t_c = "t_closest_pair_7 ?ys'"
  let ?p\<^sub>0 = "fst ?p\<^sub>0\<^sub>1"
  let ?p\<^sub>1 = "snd ?p\<^sub>0\<^sub>1"

  show ?thesis
  proof cases
    assume "length ?ys' < 2"
    hence "?t_f = t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R)  l ys"
      by (auto simp add: Let_def split!: prod.splits)
    moreover have "?t_f = length ys"
      using t_filter[of ?P ys] by simp
    ultimately show ?thesis
      by linarith
  next
    assume *: "\<not> length ?ys' < 2"
    have "?t_c \<le> 8 * length ?ys'"
      using t_closest_pair_7 by simp
    moreover have "length ?ys' \<le> length ys"
      by simp
    ultimately have "?t_c \<le> 8 * length ys"
      by linarith
    moreover have "?t_f + ?t_c = t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys"
      using * by (auto simp add: Let_def split!: prod.splits)
    moreover have "?t_f = length ys"
      using t_filter[of ?P ys] by simp
    ultimately show ?thesis
      by linarith
  qed
qed

definition combine_cost :: "nat \<Rightarrow> real" where
  "combine_cost n = 9 * n"

lemma combine_cost_nonneg[simp]:
  "0 \<le> combine_cost n"
  unfolding combine_cost_def by simp

lemma t_combine_conv_combine_cost:
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys \<le> combine_cost (length ys)"
  unfolding combine_cost_def using t_combine of_nat_mono by blast

declare t_combine.simps [simp del]


subsection "closest_pair_rec"

function t_closest_pair_rec :: "point list \<Rightarrow> nat" where
  "t_closest_pair_rec xs = (
    let n = length xs in
    let t_l = t_length xs in
    if n \<le> 3 then
      t_l + t_msort (\<lambda>p. snd p) xs + t_bf_closest_pair xs
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      let t_s = t_split_at (n div 2) xs in
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
      let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
      let t_cl = t_closest_pair_rec xs\<^sub>L in
      let t_cr = t_closest_pair_rec xs\<^sub>R in

      let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
      let t_m = t_merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
      let t_c = t_combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys in
      t_l + t_s + t_cl + t_cr + t_m + t_c
  )"
  by pat_completeness auto
termination t_closest_pair_rec
  apply (relation "Wellfounded.measure (\<lambda>xs. length xs)")
  apply (auto simp add: split_at_take_drop_conv Let_def)
  done

lemma t_closest_pair_rec_simps_1:
  assumes "n = length xs" "n \<le> 3"
  shows "t_closest_pair_rec xs = t_length xs + t_msort (\<lambda>p. snd p) xs + t_bf_closest_pair xs"
  using assms by simp

lemma t_closest_pair_rec_simps_2:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "t_closest_pair_rec xs = (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let t_s = t_split_at (n div 2) xs in
    let l = fst (hd xs\<^sub>R) in
    let (ys\<^sub>L, c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) = closest_pair_rec xs\<^sub>L in
    let (ys\<^sub>R, c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) = closest_pair_rec xs\<^sub>R in
    let t_cl = t_closest_pair_rec xs\<^sub>L in
    let t_cr = t_closest_pair_rec xs\<^sub>R in
    let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
    let t_m = t_merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
    let t_c = t_combine (c\<^sub>0\<^sub>L, c\<^sub>1\<^sub>L) (c\<^sub>0\<^sub>R, c\<^sub>1\<^sub>R) l ys in
    t_length xs + t_s + t_cl + t_cr + t_m + t_c
  )"
  using assms by (auto simp add: Let_def)

declare t_closest_pair_rec.simps [simp del]

function closest_pair_rec_cost :: "nat \<Rightarrow> real" where
  "n \<le> 3 \<Longrightarrow> closest_pair_rec_cost n = length_cost n + msort_cost n + bf_closest_pair_cost n"
| "3 < n \<Longrightarrow> closest_pair_rec_cost n = length_cost n + split_at_cost n + 
    closest_pair_rec_cost (nat \<lfloor>real n / 2\<rfloor>) + closest_pair_rec_cost (nat \<lceil>real n / 2\<rceil>) +
   merge_cost n + combine_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

lemma t_closest_pair_rec_conv_closest_pair_rec_cost:
  "t_closest_pair_rec ps \<le> closest_pair_rec_cost (length ps)"
proof (induction ps rule: length_induct)
  case (1 ps)
  let ?n = "length ps"
  show ?case
  proof (cases "?n \<le> 3")
    case True        
    hence "t_closest_pair_rec ps = 
           t_length ps + t_msort (\<lambda>p. snd p) ps + t_bf_closest_pair ps"
      using t_closest_pair_rec_simps_1 by simp
    moreover have "closest_pair_rec_cost ?n = 
                   length_cost ?n + msort_cost ?n + bf_closest_pair_cost ?n"
      using True by simp
    ultimately show ?thesis
      using t_length_conv_length_cost t_msort_conv_msort_cost
            t_bf_closest_pair_conv_bf_closest_pair_cost of_nat_add by smt
  next
    case False

    define XS where "XS = split_at (?n div 2) ps"
    define TS where "TS = t_split_at (?n div 2) ps"
    define XS\<^sub>L where "XS\<^sub>L = fst XS"
    define XS\<^sub>R where "XS\<^sub>R = snd XS"
    define L where "L = fst (hd XS\<^sub>R)"
    note divide_defs = XS_def TS_def XS\<^sub>L_def XS\<^sub>R_def L_def

    define CP\<^sub>L where "CP\<^sub>L = closest_pair_rec XS\<^sub>L"
    define TL where "TL = t_closest_pair_rec XS\<^sub>L"
    define YS\<^sub>L where "YS\<^sub>L = fst CP\<^sub>L"
    define C\<^sub>L where "C\<^sub>L = snd CP\<^sub>L"
    define C\<^sub>0\<^sub>L where "C\<^sub>0\<^sub>L = fst C\<^sub>L"
    define C\<^sub>1\<^sub>L where "C\<^sub>1\<^sub>L = snd C\<^sub>L"
    define CP\<^sub>R where "CP\<^sub>R = closest_pair_rec XS\<^sub>R"
    define TR where "TR = t_closest_pair_rec XS\<^sub>R"
    define YS\<^sub>R where "YS\<^sub>R = fst CP\<^sub>R"
    define C\<^sub>R where "C\<^sub>R = snd CP\<^sub>R"
    define C\<^sub>0\<^sub>R where "C\<^sub>0\<^sub>R = fst C\<^sub>R"
    define C\<^sub>1\<^sub>R where "C\<^sub>1\<^sub>R = snd C\<^sub>R"
    note conquer_defs = CP\<^sub>L_def TL_def YS\<^sub>L_def C\<^sub>L_def C\<^sub>0\<^sub>L_def C\<^sub>1\<^sub>L_def
                        CP\<^sub>R_def TR_def YS\<^sub>R_def C\<^sub>R_def C\<^sub>0\<^sub>R_def C\<^sub>1\<^sub>R_def

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define TM where "TM = t_merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define TC where "TC = t_combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
    note combine_defs = YS_def TM_def TC_def

    have FL: "t_closest_pair_rec ps = t_length ps + TS + TL + TR + TM + TC"
      using False t_closest_pair_rec_simps_2
      by (auto simp add:  divide_defs conquer_defs combine_defs split: prod.splits)

    have FR: "closest_pair_rec_cost (length ps) =
              length_cost ?n + split_at_cost ?n + closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>) +
              closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>) + merge_cost ?n + combine_cost ?n"
      using False by simp

    have XSLR: "XS\<^sub>L = take (?n div 2) ps" "XS\<^sub>R = drop (?n div 2) ps"
      using divide_defs by (auto simp add: split_at_take_drop_conv)
    hence "length XS\<^sub>L = ?n div 2" "length XS\<^sub>R = ?n - ?n div 2"
      by simp_all
    hence *: "(nat \<lfloor>real ?n / 2\<rfloor>) = length XS\<^sub>L" "(nat \<lceil>real ?n / 2\<rceil>) = length XS\<^sub>R"
      by linarith+

    have "length XS\<^sub>L < length ps"
      using False XSLR by simp
    hence "t_closest_pair_rec XS\<^sub>L \<le> closest_pair_rec_cost (length XS\<^sub>L)"
      using 1 by simp
    hence IHL: "t_closest_pair_rec XS\<^sub>L \<le> closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>)"
      using * by simp

    have "length XS\<^sub>R < length ps"
      using False XSLR by simp_all
    hence "t_closest_pair_rec XS\<^sub>R \<le> closest_pair_rec_cost (length XS\<^sub>R)"
      using 1 by simp
    hence IHR: "t_closest_pair_rec XS\<^sub>R \<le> closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>)"
      using * by simp

    have #: "?n = length YS\<^sub>L + length YS\<^sub>R"
      sorry

    have "t_length ps = length_cost ?n"
      using t_length_conv_length_cost by blast
    moreover have "TS \<le> split_at_cost ?n"
      using t_split_at_conv_split_at_cost TS_def by blast
    moreover have "TL \<le> closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>)"
      using IHL TL_def by blast
    moreover have "TR \<le> closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>)"
      using IHR TR_def by blast
    moreover have "TM \<le> merge_cost ?n"
      using # t_merge_conv_merge_cost TM_def by auto
    moreover have "TC \<le> combine_cost ?n"
      using # combine_defs length_merge t_combine_conv_combine_cost by metis
    ultimately show ?thesis
      using FL FR by linarith
  qed
qed
  
lemma closest_pair_rec_cost_nonneg[simp]:
  "0 \<le> closest_pair_rec_cost n"
  by (induction n rule: closest_pair_rec_cost.induct) (auto simp del: One_nat_def)

theorem closest_pair_rec_cost:
  "closest_pair_rec_cost \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  by (master_theorem) (auto simp add: length_cost_def split_at_cost_def merge_cost_def combine_cost_def)


subsection "closest_pair"

end