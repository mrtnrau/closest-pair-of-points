theory Geometry
  imports "HOL-Analysis.Analysis" "HOL-Library.Multiset"
begin




text \<open>
  2D-Boxes and Sparsity of Points
\<close>

type_synonym point = "real * real"

lemma cbox_2D: 
  "cbox (x\<^sub>0 :: real, y\<^sub>0 :: real) (x\<^sub>1, y\<^sub>1) = { (x, y). x\<^sub>0 \<le> x \<and> x \<le> x\<^sub>1 \<and> y\<^sub>0 \<le> y \<and> y \<le> y\<^sub>1}"
  by fastforce

lemma cbox_top_un:
  assumes "y\<^sub>0 \<le> y\<^sub>1" "y\<^sub>1 \<le> y\<^sub>2"
  shows "cbox (x\<^sub>0 :: real, y\<^sub>0 :: real) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>0, y\<^sub>1) (x\<^sub>1, y\<^sub>2) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>2)"
  using assms by auto

lemma cbox_right_un:
  assumes "x\<^sub>0 \<le> x\<^sub>1" "x\<^sub>1 \<le> x\<^sub>2"
  shows "cbox (x\<^sub>0 :: real, y\<^sub>0 :: real) (x\<^sub>1, y\<^sub>1) \<union> cbox (x\<^sub>1, y\<^sub>0) (x\<^sub>2, y\<^sub>1) = cbox (x\<^sub>0, y\<^sub>0) (x\<^sub>2, y\<^sub>1)"
  using assms by auto

definition sparse :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "sparse d ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> d \<le> dist p\<^sub>0 p\<^sub>1)"




text \<open>
  Maximum Distance between two Points within a Square of size d.
\<close>

lemma cbox_max_dist:
  assumes "p\<^sub>0 = (x, y)" "p\<^sub>1 = (x + d, y + d)" "(x\<^sub>a, y\<^sub>a) \<in> cbox p\<^sub>0 p\<^sub>1" "(x\<^sub>b, y\<^sub>b) \<in> cbox p\<^sub>0 p\<^sub>1" "0 \<le> d"
  shows "dist (x\<^sub>a, y\<^sub>a) (x\<^sub>b, y\<^sub>b) \<le> sqrt 2 * d"
proof -
  have X: "dist x\<^sub>a x\<^sub>b \<le> d"
    using assms dist_real_def by auto
  have Y: "dist y\<^sub>a y\<^sub>b \<le> d"
    using assms dist_real_def by auto

  have "dist (x\<^sub>a, y\<^sub>a) (x\<^sub>b, y\<^sub>b) = sqrt ((dist x\<^sub>a x\<^sub>b)\<^sup>2 + (dist y\<^sub>a y\<^sub>b)\<^sup>2)"
    using dist_Pair_Pair by auto
  also have "... \<le> sqrt (d\<^sup>2 + (dist y\<^sub>a y\<^sub>b)\<^sup>2)"
    using X power_mono by fastforce
  also have "... \<le> sqrt (d\<^sup>2 + d\<^sup>2)"
    using Y power_mono by fastforce
  also have "... = sqrt 2 * sqrt (d\<^sup>2)"
    using real_sqrt_mult by simp
  also have "... = sqrt 2 * d"
    using assms(5) by simp
  finally show ?thesis .
qed




text \<open>
  Pigeonhole Argument
\<close>

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

(* Short but ?not? usable: How to instantiate f if each point p in P should be mapped to a specific Box B especially for the pigeonhole lemma below? *) 
lemma
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




text \<open>
  Maximum Number of d Sparse Points within a Square of size d. 
\<close>

lemma max_points_square:
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + d, y + d)" "sparse d ps" "0 < d"
  shows "card ps \<le> 4"
proof (rule ccontr)
  assume *: "\<not> (card ps \<le> 4)"

  let ?x' = "x + d / 2"
  let ?y' = "y + d / 2"

  let ?ll = "cbox ( x ,  y ) (?x'   , ?y'   )"
  let ?lu = "cbox ( x , ?y') (?x'   ,  y + d)"
  let ?rl = "cbox (?x',  y ) ( x + d, ?y'   )"
  let ?ru = "cbox (?x', ?y') ( x + d,  y + d)"

  let ?sq = "{ ?ll, ?lu, ?rl, ?ru }"

  have Cle4: "card ?sq \<le> 4"
    by (simp add: card_insert_le_m1)

  have "cbox (x, y) (?x', y + d) = ?ll \<union> ?lu"
    using cbox_top_un assms(3) by auto
  moreover have "cbox (?x', y) (x + d, y + d) = ?rl \<union> ?ru"
    using cbox_top_un assms(3) by auto
  moreover have "cbox (x, y) (?x', y + d) \<union> cbox (?x', y) (x + d, y + d) = cbox (x, y) (x + d, y + d)"
    using cbox_right_un assms(3) by simp
  ultimately have "?ll \<union> ?lu \<union> ?rl \<union> ?ru = cbox (x, y) (x + d, y + d)"
    by blast

  hence "ps \<subseteq> \<Union>?sq"
    using assms(1) by auto
  moreover have "card ?sq < card ps"
    using * card_insert_le_m1 Cle4 by simp
  moreover have "finite ?sq"
    by simp
  ultimately have "\<exists>p\<^sub>0 \<in> ps. \<exists>p\<^sub>1 \<in> ps. \<exists>S \<in> ?sq. (p\<^sub>0 \<noteq> p\<^sub>1 \<and> p\<^sub>0 \<in> S \<and> p\<^sub>1 \<in> S)"
    using pigeonhole[of ?sq ps] by blast
  then obtain S p\<^sub>0 p\<^sub>1 where #: "p\<^sub>0 \<in> ps" "p\<^sub>1 \<in> ps" "S \<in> ?sq" "p\<^sub>0 \<noteq> p\<^sub>1" "p\<^sub>0 \<in> S" "p\<^sub>1 \<in> S"
    by blast

  have D: "0 \<le> d / 2"
    using assms(3) by simp
  have LL: "\<forall>p\<^sub>0 \<in> ?ll. \<forall>p\<^sub>1 \<in> ?ll. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (d / 2)"
    using cbox_max_dist[of "(x, y)" x y "(?x', ?y')" "d / 2"] D by auto
  have LU: "\<forall>p\<^sub>0 \<in> ?lu. \<forall>p\<^sub>1 \<in> ?lu. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (d / 2)"
    using cbox_max_dist[of "(x, ?y')" x ?y' "(?x', y + d)" "d / 2"] D by auto
  have RL: "\<forall>p\<^sub>0 \<in> ?rl. \<forall>p\<^sub>1 \<in> ?rl. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (d / 2)"
    using cbox_max_dist[of "(?x', y)" ?x' y "(x + d, ?y')" "d / 2"] D by auto
  have RU: "\<forall>p\<^sub>0 \<in> ?ru. \<forall>p\<^sub>1 \<in> ?ru. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (d / 2)"
    using cbox_max_dist[of "(?x', ?y')" ?x' ?y' "(x + d, y + d)" "d / 2"] D by auto

  have "\<forall>p\<^sub>0 \<in> S. \<forall>p\<^sub>1 \<in> S. dist p\<^sub>0 p\<^sub>1 \<le> sqrt 2 * (d / 2)"
    using # LL LU RL RU by blast
  hence "dist p\<^sub>0 p\<^sub>1 \<le> (sqrt 2 / 2) * d"
    using # by simp
  moreover have "(sqrt 2 / 2) * d < d"
    using sqrt2_less_2 assms(3) by simp
  ultimately have "dist p\<^sub>0 p\<^sub>1 < d"
    by simp
  moreover have "d \<le> dist p\<^sub>0 p\<^sub>1"
    using assms(2) sparse_def # by blast
  ultimately show False
    by simp
qed




lemma
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + d, y + d)" "sparse d ps" "0 < d" "card ps = 4"
  shows "ps = { (x, y), (x + d, y), (x, y + d), (x + d, y + d) }"
  oops



text \<open>
  Maximum Number of d Sparse Points within a Rectangle of width 2 * d and height d. 
\<close>

lemma max_points_rect:
  assumes "\<forall>p \<in> ps. p \<in> cbox (x, y) (x + 2 * d, y + d)" "sparse d ps" "0 < d"
  shows "card ps \<le> 8"
proof -
  let ?l = "cbox (x    , y) (x + d    , y + d)"
  let ?r = "cbox (x + d, y) (x + 2 * d, y + d)"

  let ?psl = "{ p. p \<in> ps \<and> p \<in> ?l }"
  let ?psr = "{ p. p \<in> ps \<and> p \<in> ?r }" 

  have "cbox (x, y) (x + 2 * d, y + d) = ?l \<union> ?r"
    using assms(3) cbox_right_un by simp
  hence *: "ps = ?psl \<union> ?psr"
    using assms(1) by blast

  have "\<forall>p \<in> ?psl. p \<in> ?l"
    by blast
  moreover have "sparse d ?psl"
    using assms(2) * sparse_def by blast
  hence L: "card ?psl \<le> 4"
    using assms(3) max_points_square[of ?psl x y d] by blast

  have "\<forall>p \<in> ?psr. p \<in> ?r"
    by blast
  moreover have "sparse d ?psr"
    using assms(2) * sparse_def by blast
  hence R: "card ?psr \<le> 4"
    using assms(3) max_points_square[of ?psr "x + d" y d] by simp

  have "card ps \<le> card ?psl + card ?psr"
    using * card_Un_le by (metis (no_types, lifting))
  thus ?thesis
    using L R by force
qed

end