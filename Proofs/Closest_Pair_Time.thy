theory Closest_Pair_Time
imports 
  Closest_Pair
  "Landau_Symbols.Landau_More"
  "HOL-Library.Going_To_Filter"
  "Akra_Bazzi.Akra_Bazzi_Method"
  "Akra_Bazzi.Akra_Bazzi_Approximation"
begin


section "Core Time Complexity Argument"

subsection "2D-Boxes and Points"

lemma cbox_2D: 
  fixes x\<^sub>0 :: real and y\<^sub>0 :: real
  shows "cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) = { (x, y). x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1 }"
  by fastforce

lemma mem_cbox_2D:
  fixes x :: real and y :: real
  shows "x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1 \<longleftrightarrow> (x, y) \<in> cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1)"
  by fastforce

lemma cbox_top_un:
  fixes x\<^sub>0 :: real and y\<^sub>0 :: real
  assumes "y\<^sub>0 \<le> y\<^sub>1" "y\<^sub>1 \<le> y\<^sub>2"
  shows "cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>0, y\<^sub>1) (x\<^sub>1, y\<^sub>2) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>2)"
  using assms by auto

lemma cbox_right_un:
  fixes x\<^sub>0 :: real and y\<^sub>0 :: real
  assumes "x\<^sub>0 \<le> x\<^sub>1" "x\<^sub>1 \<le> x\<^sub>2"
  shows "cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>1, y\<^sub>0) (x\<^sub>2, y\<^sub>1) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>2, y\<^sub>1)"
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
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + \<delta>, y + \<delta>)" "min_dist \<delta> ps" "0 \<le> \<delta>"
  shows "card ps \<le> 4"
proof (cases "\<delta> = 0")
  case True
  hence "{ (x, y) } = cbox (x, y) (x + \<delta>, y + \<delta>)"
    using cbox_def by simp
  hence "\<forall>p \<in> ps. p = (x, y)"
    using assms(1) by blast
  hence "\<forall>p \<in> ps. \<forall>q \<in> ps. p = q"
    apply (auto split: prod.splits) by (metis of_int_eq_iff)+
  thus ?thesis
    using card_le_1_if_pairwise_eq by force
next
  case False
  hence \<delta>: "0 < \<delta>"
    using assms(3) by simp
  show ?thesis
  proof (rule ccontr)
    assume A: "\<not> (card ps \<le> 4)"
    define PS where PS_def: "PS = (\<lambda>(x, y). (real_of_int x, real_of_int y)) ` ps"
    have "inj_on (\<lambda>(x, y). (real_of_int x, real_of_int y)) ps"
      using inj_on_def by fastforce
    hence *: "\<not> (card PS \<le> 4)"
      using A PS_def by (simp add: card_image)

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

    hence "PS \<subseteq> \<Union>(?sq)"
      using assms(1) PS_def by (auto split: prod.splits)
    moreover have "card ?sq < card PS"
      using * card_insert_le_m1 card_le_4 by linarith
    moreover have "finite ?sq"
      by simp
    ultimately have "\<exists>p\<^sub>0 \<in> PS. \<exists>p\<^sub>1 \<in> PS. \<exists>S \<in> ?sq. (p\<^sub>0 \<noteq> p\<^sub>1 \<and> p\<^sub>0 \<in> S \<and> p\<^sub>1 \<in> S)"
      using pigeonhole[of ?sq PS] by blast
    then obtain S p\<^sub>0 p\<^sub>1 where #: "p\<^sub>0 \<in> PS" "p\<^sub>1 \<in> PS" "S \<in> ?sq" "p\<^sub>0 \<noteq> p\<^sub>1" "p\<^sub>0 \<in> S" "p\<^sub>1 \<in> S"
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
      using sqrt2_less_2 \<delta> by simp
    ultimately have "dist p\<^sub>0 p\<^sub>1 < \<delta>"
      by simp
    moreover have "\<delta> \<le> dist p\<^sub>0 p\<^sub>1"
      using assms(2) # min_dist_def PS_def by auto
    ultimately show False
      by simp
  qed
qed


subsection "Final Lemma"

lemma max_points_is_7:
  fixes \<delta> :: real and p :: point and ps :: "point list"
  assumes "distinct (p # ps)" "sortedY (p # ps)" "0 \<le> \<delta>" "set (p # ps) = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p' \<in> set (p # ps). l - \<delta> \<le> fst p' \<and> fst p' \<le> l + \<delta>"
  assumes "\<forall>p' \<in> ps\<^sub>L. fst p' \<le> l" "\<forall>p' \<in> ps\<^sub>R. l \<le> fst p'"
  assumes "min_dist \<delta> ps\<^sub>L" "min_dist \<delta> ps\<^sub>R"
  shows "length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps) \<le> 7"
proof -
  define PS where "PS = p # ps"
  define R where "R = cbox (l - \<delta>, snd p) (l + \<delta>, snd p + \<delta>)"
  define RPS where "RPS = { p \<in> set PS. p \<in> R }"
  define LSQ where "LSQ = cbox (l - \<delta>, snd p) (l, snd p + \<delta>)"
  define LSQPS where "LSQPS = { p \<in> ps\<^sub>L. p \<in> LSQ }"
  define RSQ where "RSQ = cbox (l, snd p) (l + \<delta>, snd p + \<delta>)"
  define RSQPS where "RSQPS = { p \<in> ps\<^sub>R. p \<in> RSQ }"
  note defs = PS_def R_def RPS_def LSQ_def LSQPS_def RSQ_def RSQPS_def

  have "R = LSQ \<union> RSQ"
    using defs cbox_right_un by auto
  moreover have "\<forall>p \<in> ps\<^sub>L. p \<in> RSQ \<longrightarrow> p \<in> LSQ"
    using RSQ_def LSQ_def assms(6) by auto
  moreover have "\<forall>p \<in> ps\<^sub>R. p \<in> LSQ \<longrightarrow> p \<in> RSQ"
    using RSQ_def LSQ_def assms(7) by auto
  ultimately have "RPS = LSQPS \<union> RSQPS"
    using LSQPS_def RSQPS_def PS_def RPS_def assms(4) by blast

  have "min_dist \<delta> LSQPS"
    using assms(8) LSQPS_def min_dist_def by simp
  hence CLSQPS: "card LSQPS \<le> 4"
    using max_points_square[of LSQPS "l - \<delta>" "snd p" \<delta>] assms(3) LSQ_def LSQPS_def by auto

  have "min_dist \<delta> RSQPS"
    using assms(9) RSQPS_def min_dist_def by simp
  hence CRSQPS: "card RSQPS \<le> 4"
    using max_points_square[of RSQPS l "snd p" \<delta>] assms(3) RSQ_def RSQPS_def by auto

  have CRPS: "card RPS \<le> 8"
    using CLSQPS CRSQPS card_Un_le[of LSQPS RSQPS] \<open>RPS = LSQPS \<union> RSQPS\<close> by auto

  have "set (filter (\<lambda>q. snd q - snd p \<le> \<delta>) PS) \<subseteq> RPS"
  proof standard
    fix q
    assume *: "q \<in> set (filter (\<lambda>q. snd q - snd p \<le> \<delta>) PS)"
    hence CPS: "q \<in> set PS"
      by simp
    hence "snd p \<le> snd q" "snd q \<le> snd p + \<delta>"
      using assms(2) PS_def sortedY_def * by (auto split: if_splits)
    moreover have "l - \<delta> \<le> fst q" "fst q \<le> l + \<delta>"
      using CPS assms(5) PS_def by blast+
    ultimately have "q \<in> R"
      using R_def mem_cbox_2D[of "l - \<delta>" "fst q" "l + \<delta>" "snd p" "snd q" "snd p + \<delta>"]
      by (simp add: prod.case_eq_if)
    thus "q \<in> RPS"
      using CPS RPS_def by simp
  qed
  moreover have "finite RPS"
    by (simp add: RPS_def)
  ultimately have "card (set (filter (\<lambda>q. snd q - snd p \<le> \<delta>) PS)) \<le> 8"
    using CRPS card_mono[of RPS "set (filter (\<lambda>q. snd q - snd p \<le> \<delta>) PS)"] by simp
  hence "length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) PS) \<le> 8"
    using assms(1) PS_def by (simp add: distinct_card)
  thus ?thesis
    using PS_def assms(1,3) by simp
qed


section "Landau Auxiliary"

text \<open>
  The following lemma expresses a procedure for deriving complexity properties of
  the form @{prop"t \<in> O[m going_to at_top within A](f o m)"} where
    \<^item> \<open>t\<close> is a (timing) function on same data domain (e.g. lists),
    \<^item> \<open>m\<close> is a measure function on that data domain (e.g. length),
    \<^item> \<open>t'\<close> is a function on @{typ nat},
    \<^item> \<open>A\<close> is the set of valid inputs for the data domain.
  One needs to show that
    \<^item> \<open>t\<close> is bounded by @{term "t' o m"} for valid inputs
    \<^item> @{prop"t' \<in> O(f)"}
  to conclude the overall property @{prop"t \<in> O[m going_to at_top within A](f o m)"}.
\<close>

lemma bigo_measure_trans:
  fixes t :: "'a \<Rightarrow> real" and t' :: "nat \<Rightarrow> real" and m :: "'a \<Rightarrow> nat" and f ::"nat \<Rightarrow> real"
  assumes "\<And>x. x \<in> A \<Longrightarrow> t x \<le> (t' o m) x"
      and "t' \<in> O(f)"
      and "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> t x"
  shows "t \<in> O[m going_to at_top within A](f o m)"
proof -
  have 0: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> (t' o m) x" by (meson assms(1,3) order_trans)
  have 1: "t \<in> O[m going_to at_top within A](t' o m)"
    apply(rule bigoI[where c=1]) using assms 0
    by (simp add: eventually_inf_principal going_to_within_def)
  have 2: "t' o m \<in> O[m going_to at_top](f o m)"
    unfolding o_def going_to_def
    by(rule landau_o.big.filtercomap[OF assms(2)])
  have 3: "t' o m \<in> O[m going_to at_top within A](f o m)"
    using landau_o.big.filter_mono[OF _2] going_to_mono[OF _subset_UNIV] by blast
  show ?thesis by(rule landau_o.big_trans[OF 1 3])
qed


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
| "t_filter P (x#xs) = 1 + (if P x then t_filter P xs else t_filter P xs)"

lemma t_filter:
  "t_filter P xs = length xs"
  by (induction xs) auto

definition filter_cost :: "nat \<Rightarrow> real" where
  "filter_cost n = n"

lemma t_filter_conv_filter_cost:
  "t_filter P xs = filter_cost (length xs)"
  unfolding filter_cost_def using t_filter by auto


subsection "split_at"

fun t_split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_split_at n [] = 0"
| "t_split_at n (x#xs) = 1 + (
    case n of
      0 \<Rightarrow> 0
    | Suc m \<Rightarrow> t_split_at m xs
  )"

lemma t_split_at:
  "t_split_at n xs \<le> length xs"
  by (induction xs arbitrary: n) (auto split: nat.split)

definition split_at_cost :: "nat \<Rightarrow> real" where
  "split_at_cost n = n"

lemma split_at_cost_nonneg[simp]:
  "0 \<le> split_at_cost n"
  unfolding split_at_cost_def by simp

lemma t_split_at_conv_split_at_cost:
  "t_split_at n xs \<le> split_at_cost (length xs)"
  unfolding split_at_cost_def by (auto simp: min_def t_split_at)


subsection "merge"

fun t_merge' :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_merge' f (x#xs) (y#ys) = 1 + (
    if f x \<le> f y then
      t_merge' f xs (y#ys)
    else
      t_merge' f (x#xs) ys
  )"
| "t_merge' f xs [] = 0"
| "t_merge' f [] ys = 0"

definition t_merge :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> ('b list * 'b list) \<Rightarrow> nat" where
  "t_merge f xys = t_merge' f (fst xys) (snd xys)"

lemma t_merge:
  "t_merge f (xs, ys) \<le> length xs + length ys"
  unfolding t_merge_def by (induction f xs ys rule: t_merge'.induct) auto

definition merge_cost :: "nat \<Rightarrow> real" where
  "merge_cost n = n"

lemma merge_cost_nonneg[simp]:
  "0 \<le> merge_cost n"
  unfolding merge_cost_def by simp

lemma t_merge_conv_merge_cost:
  "t_merge f (xs, ys) \<le> merge_cost (length xs + length ys)"
  unfolding merge_cost_def by (metis of_nat_mono t_merge)


subsection "msort"

function t_msort :: "('b \<Rightarrow> 'a::linorder) \<Rightarrow> 'b list \<Rightarrow> nat" where
  "t_msort f [] = 0"
| "t_msort f [_] = 1"
| "t_msort f (x # y # xs') = 1 + (
    let xs = x # y # xs' in
    let (l, r) = split_at (length xs div 2) xs in
    t_length xs + t_split_at (length xs div 2) xs +
    t_msort f l + t_msort f r + t_merge f (l, r)
  )"
  by pat_completeness auto
termination t_msort
  apply (relation "Wellfounded.measure (\<lambda>(_, xs). length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

definition t_sortX :: "point list \<Rightarrow> nat" where
  "t_sortX ps = t_msort (\<lambda>p. fst p) ps"

definition t_sortY :: "point list \<Rightarrow> nat" where
  "t_sortY ps = t_msort (\<lambda>p. snd p) ps"

function msort_cost :: "nat \<Rightarrow> real" where
  "msort_cost 0 = 0"
| "msort_cost 1 = 1"
| "2 \<le> n \<Longrightarrow> msort_cost n = 1 + length_cost n + split_at_cost n + 
    msort_cost (nat \<lfloor>real n / 2\<rfloor>) + msort_cost (nat \<lceil>real n / 2\<rceil>) + merge_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

definition sortX_cost :: "nat \<Rightarrow> real" where
  "sortX_cost = msort_cost"

definition sortY_cost :: "nat \<Rightarrow> real" where
  "sortY_cost = msort_cost"

declare t_length.simps t_split_at.simps[simp del]

lemma msort_cost_nonneg[simp]:
  "0 \<le> msort_cost n"
  by (induction n rule: msort_cost.induct) (auto simp del: One_nat_def)

corollary sortX_cost_nonneg[simp]:
  "0 \<le> sortX_cost n"
  unfolding sortX_cost_def by simp

corollary sortY_cost_nonneg[simp]:
  "0 \<le> sortY_cost n"
  unfolding sortY_cost_def by simp

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
  obtain L R where LR_def: "(L, R) = split_at (N div 2) XS"
    using prod.collapse by blast
  note defs = XS_def N_def LR_def

  let ?LHS = "1 + t_length XS + t_split_at (N div 2) XS + t_msort f L + t_msort f R + t_merge f (L, R)"
  let ?RHS = "1 + length_cost N + split_at_cost N + msort_cost (nat \<lfloor>real N / 2\<rfloor>) +
              msort_cost (nat \<lceil>real N / 2\<rceil>) + merge_cost N"

  have IHL: "t_msort f L \<le> msort_cost (length L)"
    using defs "3.IH"(1) prod.collapse by blast
  have IHR: "t_msort f R \<le> msort_cost (length R)"
    using defs "3.IH"(2) prod.collapse by blast

  have *: "length L = N div 2" "length R = N - N div 2"
    using defs by (auto simp: split_at_take_drop_conv)
  hence "(nat \<lfloor>real N / 2\<rfloor>) = length L" "(nat \<lceil>real N / 2\<rceil>) = length R"
    by linarith+
  hence IH: "t_msort f L \<le> msort_cost (nat \<lfloor>real N / 2\<rfloor>)"
            "t_msort f R \<le> msort_cost (nat \<lceil>real N / 2\<rceil>)"
    using IHL IHR by simp_all

  have "N = length L + length R"
    using * by linarith
  hence "t_merge f (L, R) \<le> merge_cost N"
    using t_merge_conv_merge_cost by metis
  moreover have "t_length XS = length_cost N"
    using t_length_conv_length_cost defs by blast
  moreover have "t_split_at (N div 2) XS \<le> split_at_cost N"
    using t_split_at_conv_split_at_cost defs by blast
  ultimately have *: "?LHS \<le> ?RHS"
    using IH by simp
  moreover have "t_msort f XS = ?LHS"
    using defs by (auto simp: Let_def split: prod.split)
  moreover have "msort_cost N = ?RHS"
    by (simp add: defs)
  ultimately have "t_msort f XS \<le> msort_cost N"
    by presburger 
  thus ?case
    using XS_def N_def by blast
qed auto

corollary t_sortX_conv_sortX_cost:
  "t_sortX xs \<le> sortX_cost (length xs)"
  unfolding t_sortX_def sortX_cost_def using t_msort_conv_msort_cost by blast

corollary t_sortY_conv_sortY_cost:
  "t_sortY xs \<le> sortY_cost (length xs)"
  unfolding t_sortY_def sortY_cost_def using t_msort_conv_msort_cost by blast

theorem msort_cost:
  "msort_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  by (master_theorem) (auto simp: length_cost_def split_at_cost_def merge_cost_def)

corollary sortX_cost:
  "sortX_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding sortX_cost_def using msort_cost by simp

corollary sortY_cost:
  "sortY_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  unfolding sortY_cost_def using msort_cost by simp

theorem t_msort_bigo:
  "t_msort f \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
proof -
  have 0: "\<And>xs. t_msort f xs \<le> (msort_cost o length) xs"
    unfolding comp_def using t_msort_conv_msort_cost by blast
  show ?thesis
    using bigo_measure_trans[OF 0] by (simp add: bigthetaD1 msort_cost)
qed

corollary t_sortX_bigo:
  "t_sortX \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  unfolding t_sortX_def sortX_cost_def using t_msort_bigo by blast

corollary t_sortY_bigo:
  "t_sortY \<in> O[length going_to at_top]((\<lambda>n. n * ln n) o length)"
  unfolding t_sortY_def sortY_cost_def using t_msort_bigo by blast


subsection "find_closest"

fun t_find_closest :: "point \<Rightarrow> point list \<Rightarrow> nat" where
  "t_find_closest _ [] = 0"
| "t_find_closest _ [_] = 1"
| "t_find_closest p (p\<^sub>0 # ps) = 1 + (
    let p\<^sub>1 = find_closest p ps in
    t_find_closest p ps + (
    if dist p p\<^sub>0 < dist p p\<^sub>1 then 0 else 0
    )
  )"

lemma t_find_closest:
  "t_find_closest p ps = length ps"
  by (induction p ps rule: t_find_closest.induct) auto


subsection "closest_pair_bf"

fun t_closest_pair_bf :: "point list \<Rightarrow> nat" where
  "t_closest_pair_bf [] = 0"
| "t_closest_pair_bf [_] = 1"
| "t_closest_pair_bf [_, _] = 2"
| "t_closest_pair_bf (p\<^sub>0 # ps) = 1 + (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_bf ps in
    t_closest_pair_bf ps + (
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    t_find_closest p\<^sub>0 ps + (
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then 0 else 0
    ))
  )"

lemma t_closest_pair_bf:
  "t_closest_pair_bf ps \<le> length ps * length ps"
proof (induction rule: t_closest_pair_bf.induct)
  case (4 p\<^sub>0 p\<^sub>2 p\<^sub>3 ps)
  let ?ps = "p\<^sub>2 # p\<^sub>3 # ps"
  have "t_closest_pair_bf ?ps \<le> length ?ps * length ?ps"
    using 4 prod_cases3 by metis
  thus ?case
    using "4.prems" t_find_closest by simp
qed auto

definition closest_pair_bf_cost :: "nat \<Rightarrow> real" where
  "closest_pair_bf_cost n = n * n"

lemma closest_pair_bf_cost_nonneg[simp]:
  "0 \<le> closest_pair_bf_cost n"
  unfolding closest_pair_bf_cost_def by simp

lemma t_closest_pair_bf_conv_closest_pair_bf_cost:
  "t_closest_pair_bf ps \<le> closest_pair_bf_cost (length ps)"
  unfolding closest_pair_bf_cost_def using t_closest_pair_bf of_nat_mono by fastforce


subsection "find_closest_\<delta>"

fun t_find_closest_\<delta> :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> nat" where
  "t_find_closest_\<delta> _ _ [] = 0"
| "t_find_closest_\<delta> _ _ [_] = 1"
| "t_find_closest_\<delta> p \<delta> (p\<^sub>0 # ps) = 1 + (
    if \<delta> \<le> snd p\<^sub>0 - snd p then
      0
    else
      let p\<^sub>1 = find_closest_\<delta> p (min \<delta> (dist p p\<^sub>0)) ps in
      t_find_closest_\<delta> p (min \<delta> (dist p p\<^sub>0)) ps + (
      if dist p p\<^sub>0 \<le> dist p p\<^sub>1 then 0 else 0
    )
  )"

lemma t_find_closest_\<delta>_mono:
  "\<delta>' \<le> \<delta> \<Longrightarrow> t_find_closest_\<delta> p \<delta>' ps \<le> t_find_closest_\<delta> p \<delta> ps"
  apply (induction rule: t_find_closest_\<delta>.induct)
  apply (auto simp: Let_def min_def)
  apply (metis surj_pair)+
  done

lemma length_filter_P_impl_Q:
   "(\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> length (filter P xs) \<le> length (filter Q xs)"
  by (induction xs) auto

lemma t_find_closest_cnt:
  "t_find_closest_\<delta> p \<delta> ps \<le> 1 + length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) ps)"
proof (induction p \<delta> ps rule: t_find_closest_\<delta>.induct)
  case (3 p \<delta> p\<^sub>0 p\<^sub>2 ps)
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest_\<delta> p (min \<delta> (dist p p\<^sub>0)) (p\<^sub>2 # ps)"
  show ?case
  proof (cases "\<delta> \<le> snd p\<^sub>0 - snd p")
    case True
    thus ?thesis
      by simp
  next
    case False
    hence "t_find_closest_\<delta> p \<delta> (p\<^sub>0 # p\<^sub>2 # ps) = 1 + t_find_closest_\<delta> p (min \<delta> (dist p p\<^sub>0)) (p\<^sub>2 # ps)"
      using p\<^sub>1_def by simp
    also have "... \<le> 1 + 1 + length (filter (\<lambda>q. snd q - snd p \<le> min \<delta> (dist p p\<^sub>0)) (p\<^sub>2 # ps))"
      using False 3 p\<^sub>1_def by simp
    also have "... \<le> 1 + 1 + length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) (p\<^sub>2 # ps))"
      using length_filter_P_impl_Q by (smt add_left_mono)
    also have "... \<le> 1 + length (filter (\<lambda>q. snd q - snd p \<le> \<delta>) (p\<^sub>0 # p\<^sub>2 # ps))"
      using False by simp
    ultimately show ?thesis 
      by simp
  qed
qed auto

lemma t_find_closest_\<delta>:
  fixes \<delta> :: real and p :: point and ps :: "point list" and l :: int
  assumes "distinct (p # ps)" "sortedY (p # ps)" "0 \<le> \<delta>" "set (p # ps) = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p' \<in> set (p # ps). l - \<delta> \<le> fst p' \<and> fst p' \<le> l + \<delta>"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "min_dist \<delta> ps\<^sub>L" "min_dist \<delta> ps\<^sub>R"
  shows "t_find_closest_\<delta> p \<delta> ps \<le> 8"
  using assms max_points_is_7[of p ps \<delta> ps\<^sub>L ps\<^sub>R l] t_find_closest_cnt[of p \<delta> ps] by linarith


subsection "closest_pair_combine"

fun t_closest_pair_combine :: "(point * point) \<Rightarrow> point list \<Rightarrow> nat" where
  "t_closest_pair_combine _ [] = 0"
| "t_closest_pair_combine _ [_] = 1"
| "t_closest_pair_combine (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ps) = 1 + (
    let p\<^sub>1 = find_closest_\<delta> p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps in
    t_find_closest_\<delta> p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ps + (
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ps
    else
      t_closest_pair_combine (p\<^sub>0, p\<^sub>1) ps
  ))"

lemma t_closest_pair_combine:
  assumes "distinct ps" "sortedY ps" "\<delta> = dist c\<^sub>0 c\<^sub>1" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> set ps. l - \<Delta> \<le> fst p \<and> fst p \<le> l + \<Delta>"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "min_dist \<Delta> ps\<^sub>L" "min_dist \<Delta> ps\<^sub>R" "\<delta> \<le> \<Delta>"
  shows "t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ps \<le> 9 * length ps"
  using assms
proof (induction "(c\<^sub>0, c\<^sub>1)" ps arbitrary: \<delta> c\<^sub>0 c\<^sub>1 ps\<^sub>L ps\<^sub>R rule: t_closest_pair_combine.induct)
  case (3 c\<^sub>0 c\<^sub>1 p\<^sub>0 p\<^sub>2 ps)
  let ?ps = "p\<^sub>2 # ps"
  define p\<^sub>1 where p\<^sub>1_def: "p\<^sub>1 = find_closest_\<delta> p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps"
  define PS\<^sub>L where PS\<^sub>L_def: "PS\<^sub>L = ps\<^sub>L - { p\<^sub>0 }"
  define PS\<^sub>R where PS\<^sub>R_def: "PS\<^sub>R = ps\<^sub>R - { p\<^sub>0 }"
  note defs = p\<^sub>1_def PS\<^sub>L_def PS\<^sub>R_def
  have *: "0 \<le> \<Delta>"
    using "3.prems"(3,10) zero_le_dist[of c\<^sub>0 c\<^sub>1] by argo
  hence "t_find_closest_\<delta> p\<^sub>0 \<Delta> ?ps \<le> 8"
    using t_find_closest_\<delta>[of p\<^sub>0 ?ps \<Delta> ps\<^sub>L ps\<^sub>R] "3.prems" by blast
  hence A: "t_find_closest_\<delta> p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps \<le> 8"
    by (metis "3.prems"(3,10) order_trans t_find_closest_\<delta>_mono)
  have B: "distinct ?ps" "sortedY ?ps"
    using "3.prems"(1,2) sortedY_def by simp_all
  have C: "set ?ps = PS\<^sub>L \<union> PS\<^sub>R"
    using defs "3.prems"(1,4) by auto
  have D: "\<forall>p \<in> set ?ps. l - \<Delta> \<le> fst p \<and> fst p \<le> l + \<Delta>"
    using "3.prems"(5) by simp
  have E: "\<forall>p \<in> PS\<^sub>L. fst p \<le> l" "\<forall>p \<in> PS\<^sub>R. l \<le> fst p" 
    using defs "3.prems"(6,7) by simp_all
  have F: "min_dist \<Delta> PS\<^sub>L" "min_dist \<Delta> PS\<^sub>R"
    using defs "3.prems"(8,9) min_dist_def by simp_all
  show ?case
  proof (cases "dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1")
    case True
    hence "t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ?ps \<le> 9 * length ?ps"
      using "3.hyps"(1) "3.prems"(3,10) defs(1) B C D E F by blast
    moreover have "t_closest_pair_combine (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ?ps) =
                   1 + t_find_closest_\<delta> p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps + t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ?ps"
      using defs True by (auto split: prod.splits)
    ultimately show ?thesis
      using A by auto
  next
    case False
    moreover have "0 \<le> dist p\<^sub>0 p\<^sub>1"
      by auto
    ultimately have "t_closest_pair_combine (p\<^sub>0, p\<^sub>1) ?ps \<le> 9 * length ?ps"
      using "3.hyps"(2) "3.prems"(3,10) defs(1) B C D E F by auto
    moreover have "t_closest_pair_combine (c\<^sub>0, c\<^sub>1) (p\<^sub>0 # ?ps) =
                   1 + t_find_closest_\<delta> p\<^sub>0 (dist c\<^sub>0 c\<^sub>1) ?ps + t_closest_pair_combine (p\<^sub>0, p\<^sub>1) ?ps"
      using defs False by (auto split: prod.splits)
    ultimately show ?thesis
      using A by simp
  qed
qed auto


subsection "combine"

fun t_combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> int \<Rightarrow> point list \<Rightarrow> nat" where
  "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let ps' = filter (\<lambda>p. dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1) ps in
    t_filter (\<lambda>p. dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1) ps + t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ps'
  )"

definition combine_cost :: "nat \<Rightarrow> real" where
  "combine_cost n = 10 * n"

lemma combine_cost_nonneg[simp]:
  "0 \<le> combine_cost n"
  unfolding combine_cost_def by simp

lemma filter_Un:
  "set xs = A \<union> B \<Longrightarrow> set (filter P xs) = { x \<in> A. P x } \<union> { x \<in> B. P x }"
  apply (induction xs)
  apply (auto) by (metis UnI1 UnI2 insert_iff)+

lemma t_combine:
  fixes ps :: "point list"
  assumes "distinct ps" "sortedY ps" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "min_dist (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ps\<^sub>L" "min_dist (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ps\<^sub>R"
  shows "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps \<le> 10 * length ps"
proof -
  obtain c\<^sub>0 c\<^sub>1 where c_def:
    "(c\<^sub>0, c\<^sub>1) = (if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R))" by metis
  let ?P = "(\<lambda>p. dist p (l, snd p) \<le> dist c\<^sub>0 c\<^sub>1)"
  define ps' where ps'_def: "ps' = filter ?P ps"
  define ps\<^sub>L' where ps\<^sub>L'_def: "ps\<^sub>L' = { p \<in> ps\<^sub>L. ?P p }" 
  define ps\<^sub>R' where ps\<^sub>R'_def: "ps\<^sub>R' = { p \<in> ps\<^sub>R. ?P p }"
  note defs = c_def ps'_def ps\<^sub>L'_def ps\<^sub>R'_def
  have "min_dist (dist c\<^sub>0 c\<^sub>1) ps\<^sub>L" "min_dist (dist c\<^sub>0 c\<^sub>1) ps\<^sub>R"
    using assms(6,7) min_dist_def c_def by (smt Pair_inject)+
  hence "min_dist (dist c\<^sub>0 c\<^sub>1) ps\<^sub>L'" "min_dist (dist c\<^sub>0 c\<^sub>1) ps\<^sub>R'"
    using ps\<^sub>L'_def ps\<^sub>R'_def min_dist_def by auto
  moreover have "distinct ps'"
    using ps'_def assms(1) by simp
  moreover have "sortedY ps'"
    using ps'_def assms(2) sortedY_def sorted_wrt_filter by blast
  moreover have "0 \<le> dist c\<^sub>0 c\<^sub>1"
    by simp
  moreover have "set ps' = ps\<^sub>L' \<union> ps\<^sub>R'"
    using assms(3) defs(2,3,4) filter_Un by auto
  moreover have "\<forall>p \<in> set ps'. l - dist c\<^sub>0 c\<^sub>1 \<le> fst p \<and> fst p \<le> l + dist c\<^sub>0 c\<^sub>1"
    using ps'_def dist_transform by force
  moreover have "\<forall>p \<in> ps\<^sub>L'. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R'. l \<le> fst p"
    using assms(4,5) ps\<^sub>L'_def ps\<^sub>R'_def by blast+
  ultimately have "t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ps' \<le> 9 * length ps'"
    using t_closest_pair_combine by blast
  moreover have "length ps' \<le> length ps"
    using ps'_def by simp
  ultimately have *: "t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ps' \<le> 9 * length ps"
    by simp
  have "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps =
        t_filter ?P ps + t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ps'"
    using defs by (auto split: prod.splits)
  also have "... = length ps + t_closest_pair_combine (c\<^sub>0, c\<^sub>1) ps'"
    using t_filter by auto
  finally show ?thesis
    using * by simp
qed

lemma t_combine_conv_combine_cost:
  assumes "distinct ps" "sortedY ps" "set ps = ps\<^sub>L \<union> ps\<^sub>R"
  assumes "\<forall>p \<in> ps\<^sub>L. fst p \<le> l" "\<forall>p \<in> ps\<^sub>R. l \<le> fst p"
  assumes "min_dist (dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L) ps\<^sub>L" "min_dist (dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R) ps\<^sub>R"
  shows "t_combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps \<le> combine_cost (length ps)"
  using assms unfolding combine_cost_def using t_combine by (meson of_nat_le_iff)

declare t_combine.simps [simp del]


subsection "closest_pair_rec"

function t_closest_pair_rec :: "point list \<Rightarrow> nat" where
  "t_closest_pair_rec xs = 1 + (
    let n = length xs in
    t_length xs + (
    if n \<le> 3 then
      t_sortY xs + t_closest_pair_bf xs
    else
      let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
      t_split_at (n div 2) xs + (
      let l = fst (hd xs\<^sub>R) in

      let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec xs\<^sub>L in
      t_closest_pair_rec xs\<^sub>L + (
      let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec xs\<^sub>R in
      t_closest_pair_rec xs\<^sub>R + (

      let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
      t_merge (\<lambda>p. snd p) (ys\<^sub>L, ys\<^sub>R) + t_combine p\<^sub>L p\<^sub>R l ys
    ))))
  )"
  by pat_completeness auto
termination t_closest_pair_rec
  apply (relation "Wellfounded.measure (\<lambda>xs. length xs)")
  apply (auto simp: split_at_take_drop_conv Let_def)
  done

lemma t_closest_pair_rec_simps_1:
  assumes "n = length xs" "n \<le> 3"
  shows "t_closest_pair_rec xs = 1 + t_length xs + t_sortY xs + t_closest_pair_bf xs"
  using assms by simp

lemma t_closest_pair_rec_simps_2:
  assumes "n = length xs" "\<not> (n \<le> 3)"
  shows "t_closest_pair_rec xs = 1 + (
    let (xs\<^sub>L, xs\<^sub>R) = split_at (n div 2) xs in
    let t_s = t_split_at (n div 2) xs in
    let l = fst (hd xs\<^sub>R) in
    let (ys\<^sub>L, p\<^sub>L) = closest_pair_rec xs\<^sub>L in
    let (ys\<^sub>R, p\<^sub>R) = closest_pair_rec xs\<^sub>R in
    let t_cl = t_closest_pair_rec xs\<^sub>L in
    let t_cr = t_closest_pair_rec xs\<^sub>R in
    let ys = merge (\<lambda>p. snd p) ys\<^sub>L ys\<^sub>R in
    let t_m = t_merge (\<lambda>p. snd p) (ys\<^sub>L, ys\<^sub>R) in
    let t_c = t_combine p\<^sub>L p\<^sub>R l ys in
    t_length xs + t_s + t_cl + t_cr + t_m + t_c
  )"
  using assms by (auto simp add: Let_def split!: if_splits prod.splits)

declare t_closest_pair_rec.simps [simp del]

function closest_pair_rec_cost :: "nat \<Rightarrow> real" where
  "n \<le> 3 \<Longrightarrow> closest_pair_rec_cost n = 1 + length_cost n + sortY_cost n + closest_pair_bf_cost n"
| "3 < n \<Longrightarrow> closest_pair_rec_cost n = 1 + length_cost n + split_at_cost n + 
    closest_pair_rec_cost (nat \<lfloor>real n / 2\<rfloor>) + closest_pair_rec_cost (nat \<lceil>real n / 2\<rceil>) +
    merge_cost n + combine_cost n"
  by force simp_all
termination by akra_bazzi_termination simp_all

lemma closest_pair_rec_cost_nonneg[simp]:
  "0 \<le> closest_pair_rec_cost n"
  by (induction n rule: closest_pair_rec_cost.induct) (auto simp add: combine_cost_def)

lemma t_closest_pair_rec_conv_closest_pair_rec_cost:
  assumes "1 < length ps" "distinct ps" "sortedX ps"
  shows "t_closest_pair_rec ps \<le> closest_pair_rec_cost (length ps)"
  using assms
proof (induction ps rule: length_induct)
  case (1 ps)
  let ?n = "length ps"
  show ?case
  proof (cases "?n \<le> 3")
    case True        
    hence "t_closest_pair_rec ps = 
           1 + t_length ps + t_sortY ps + t_closest_pair_bf ps"
      using t_closest_pair_rec_simps_1 by simp
    moreover have "closest_pair_rec_cost ?n = 
                   1 + length_cost ?n + sortY_cost ?n + closest_pair_bf_cost ?n"
      using True by simp
    ultimately show ?thesis
      using t_length_conv_length_cost t_sortY_conv_sortY_cost
            t_closest_pair_bf_conv_closest_pair_bf_cost of_nat_add
      by (smt of_nat_1)
  next
    case False

    obtain XS\<^sub>L XS\<^sub>R where XS_def: "(XS\<^sub>L, XS\<^sub>R) = split_at (?n div 2) ps"
      using prod.collapse by blast
    define TS where "TS = t_split_at (?n div 2) ps"
    define L where "L = fst (hd XS\<^sub>R)"

    obtain YS\<^sub>L C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L where CP\<^sub>L_def: "(YS\<^sub>L, C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) = closest_pair_rec XS\<^sub>L"
      using prod.collapse by metis
    define TL where "TL = t_closest_pair_rec XS\<^sub>L"
    obtain YS\<^sub>R C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R where CP\<^sub>R_def: "(YS\<^sub>R, C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) = closest_pair_rec XS\<^sub>R"
      using prod.collapse by metis
    define TR where "TR = t_closest_pair_rec XS\<^sub>R"

    define YS where "YS = merge (\<lambda>p. snd p) YS\<^sub>L YS\<^sub>R"
    define TM where "TM = t_merge (\<lambda>p. snd p) (YS\<^sub>L, YS\<^sub>R)"
    define TC where "TC = t_combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
    obtain C\<^sub>0 C\<^sub>1 where C\<^sub>0\<^sub>1_def: "(C\<^sub>0, C\<^sub>1) = combine (C\<^sub>0\<^sub>L, C\<^sub>1\<^sub>L) (C\<^sub>0\<^sub>R, C\<^sub>1\<^sub>R) L YS"
      using prod.collapse by metis
    note defs = XS_def TS_def L_def CP\<^sub>L_def TL_def CP\<^sub>R_def TR_def YS_def TM_def TC_def

    have FL: "t_closest_pair_rec ps = 1 + t_length ps + TS + TL + TR + TM + TC"
      using False t_closest_pair_rec_simps_2 defs
      by (auto simp: Let_def split!: if_splits prod.splits)

    have FR: "closest_pair_rec_cost (length ps) = 1 +
              length_cost ?n + split_at_cost ?n + closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>) +
              closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>) + merge_cost ?n + combine_cost ?n"
      using False by simp

    have XSLR: "XS\<^sub>L = take (?n div 2) ps" "XS\<^sub>R = drop (?n div 2) ps"
      using defs by (auto simp: split_at_take_drop_conv)
    hence "length XS\<^sub>L = ?n div 2" "length XS\<^sub>R = ?n - ?n div 2"
      by simp_all
    hence *: "(nat \<lfloor>real ?n / 2\<rfloor>) = length XS\<^sub>L" "(nat \<lceil>real ?n / 2\<rceil>) = length XS\<^sub>R"
      by linarith+
    have "length XS\<^sub>L = length YS\<^sub>L" "length XS\<^sub>R = length YS\<^sub>R"
      using defs closest_pair_rec_set_length_sortedY by metis+
    hence L: "?n = length YS\<^sub>L + length YS\<^sub>R"
      using defs XSLR by fastforce

    have "1 < length XS\<^sub>L" "length XS\<^sub>L < length ps"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>L" "sortedX XS\<^sub>L"
      using XSLR "1.prems"(2,3) sortedX_def sorted_wrt_take by simp_all
    ultimately have "t_closest_pair_rec XS\<^sub>L \<le> closest_pair_rec_cost (length XS\<^sub>L)"
      using "1.IH" by simp
    hence IHL: "t_closest_pair_rec XS\<^sub>L \<le> closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>)"
      using * by simp

    have "1 < length XS\<^sub>R" "length XS\<^sub>R < length ps"
      using False XSLR by simp_all
    moreover have "distinct XS\<^sub>R" "sortedX XS\<^sub>R"
      using XSLR "1.prems"(2,3) sortedX_def sorted_wrt_drop by simp_all
    ultimately have "t_closest_pair_rec XS\<^sub>R \<le> closest_pair_rec_cost (length XS\<^sub>R)"
      using "1.IH" by simp
    hence IHR: "t_closest_pair_rec XS\<^sub>R \<le> closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>)"
      using * by simp

    have "(YS, C\<^sub>0, C\<^sub>1) = closest_pair_rec ps"
      using False closest_pair_rec_simps defs C\<^sub>0\<^sub>1_def by (auto simp: Let_def split: prod.split)
    hence "set ps = set YS" "length ps = length YS" "distinct YS" "sortedY YS"
      using "1.prems" closest_pair_rec_set_length_sortedY closest_pair_rec_distinct by auto
    moreover have "\<forall>p \<in> set YS\<^sub>L. fst p \<le> L"
      using False "1.prems"(3) XSLR \<open>length XS\<^sub>L < length ps\<close> \<open>length XS\<^sub>L = length ps div 2\<close>
            L_def CP\<^sub>L_def sortedX_take_less_hd_drop closest_pair_rec_set_length_sortedY by metis
    moreover have "\<forall>p \<in> set YS\<^sub>R. L \<le> fst p"
      using False "1.prems"(3) XSLR L_def CP\<^sub>R_def
            sortedX_hd_drop_less_drop closest_pair_rec_set_length_sortedY by blast
    moreover have "set YS = set YS\<^sub>L \<union> set YS\<^sub>R"
      using set_merge defs by fast
    moreover have "min_dist (dist C\<^sub>0\<^sub>L C\<^sub>1\<^sub>L) (set YS\<^sub>L)"
      using CP\<^sub>L_def \<open>1 < length XS\<^sub>L\<close> \<open>distinct XS\<^sub>L\<close> \<open>sortedX XS\<^sub>L\<close>
            closest_pair_rec_dist closest_pair_rec_set_length_sortedY by auto
    moreover have "min_dist (dist C\<^sub>0\<^sub>R C\<^sub>1\<^sub>R) (set YS\<^sub>R)"
      using CP\<^sub>R_def \<open>1 < length XS\<^sub>R\<close> \<open>distinct XS\<^sub>R\<close> \<open>sortedX XS\<^sub>R\<close>
            closest_pair_rec_dist closest_pair_rec_set_length_sortedY by auto
    ultimately have "TC \<le> combine_cost ?n"
      using t_combine_conv_combine_cost TC_def by presburger
    moreover have "t_length ps = length_cost ?n"
      using t_length_conv_length_cost by blast
    moreover have "TS \<le> split_at_cost ?n"
      using t_split_at_conv_split_at_cost TS_def by blast
    moreover have "TL \<le> closest_pair_rec_cost (nat \<lfloor>real ?n / 2\<rfloor>)"
      using IHL TL_def by blast
    moreover have "TR \<le> closest_pair_rec_cost (nat \<lceil>real ?n / 2\<rceil>)"
      using IHR TR_def by blast
    moreover have "TM \<le> merge_cost ?n"
      using L t_merge_conv_merge_cost TM_def by auto
    ultimately show ?thesis
      using FL FR by linarith
  qed
qed

theorem closest_pair_rec_cost:
  "closest_pair_rec_cost \<in> \<Theta>(\<lambda>n. n * ln n)"
  by (master_theorem)
     (auto simp: length_cost_def split_at_cost_def merge_cost_def combine_cost_def)
 
theorem t_closest_pair_rec_bigo:
  "t_closest_pair_rec \<in> O[length going_to at_top within { ps.
     1 < length ps \<and> distinct ps \<and> sortedX ps }]((\<lambda>n. n * ln n) o length)"
proof -
  have 0: "\<And>ps. ps \<in> { ps. 1 < length ps \<and> distinct ps \<and> sortedX ps } \<Longrightarrow>
           t_closest_pair_rec ps \<le> (closest_pair_rec_cost o length) ps"
    unfolding comp_def using t_closest_pair_rec_conv_closest_pair_rec_cost by auto
  show ?thesis
    using bigo_measure_trans[OF 0] bigthetaD1[OF closest_pair_rec_cost] of_nat_0_le_iff by blast
qed


subsection "closest_pair"

definition t_closest_pair :: "point list \<Rightarrow> nat" where
  "t_closest_pair ps = t_sortX ps + t_closest_pair_rec (sortX ps)"

definition closest_pair_cost :: "nat \<Rightarrow> real" where
  "closest_pair_cost n = sortX_cost n + closest_pair_rec_cost n"

lemma t_closest_pair_conv_closest_pair_cost:
  assumes "1 < length ps" "distinct ps"
  shows "t_closest_pair ps \<le> closest_pair_cost (length ps)"
  unfolding t_closest_pair_def closest_pair_cost_def using assms sortX of_nat_add
  using t_sortX_conv_sortX_cost t_closest_pair_rec_conv_closest_pair_rec_cost
  by (smt One_nat_def)

theorem closest_pair_cost:
  "closest_pair_cost \<in> O(\<lambda>n. n * ln n)"
  unfolding closest_pair_cost_def
  using sortX_cost closest_pair_rec_cost sum_in_bigo(1) by blast

theorem t_closest_pair_bigo:
  "t_closest_pair \<in> O[length going_to at_top within { ps.
     1 < length ps \<and> distinct ps }]((\<lambda>n. n * ln n) o length)"
proof -
  have 0: "\<And>ps. ps \<in> { ps. 1 < length ps \<and> distinct ps } \<Longrightarrow>
           t_closest_pair ps \<le> (closest_pair_cost o length) ps"
    unfolding comp_def using t_closest_pair_conv_closest_pair_cost by auto
  show ?thesis
    using bigo_measure_trans[OF 0] closest_pair_cost by fastforce
qed

end