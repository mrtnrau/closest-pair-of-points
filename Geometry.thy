theory Geometry
  imports "HOL-Analysis.Analysis"
begin




text \<open>
  Definition of 2D-Boxes and Sparsity of Points
\<close>

type_synonym point = "real * real"

(* use cbox ? *)
fun box :: "point \<Rightarrow> point \<Rightarrow> point set" where
  "box (x\<^sub>0, y\<^sub>0) (x\<^sub>1, y\<^sub>1) = { (x, y). min x\<^sub>0 x\<^sub>1 \<le> x \<and> x \<le> max x\<^sub>0 x\<^sub>1 \<and> min y\<^sub>0 y\<^sub>1 \<le> y \<and> y \<le> max y\<^sub>0 y\<^sub>1 }"

lemma box_extend_top:
  assumes "b \<le> d" "d \<le> e"
  shows "box (a, b) (c, d) \<union> box (a, d) (c, e) = box (a, b) (c, e)"
  using assms by (auto simp add: min_def max_def)

lemma box_extend_right:
  assumes "a \<le> c" "c \<le> e"
  shows "box (a, b) (c, d) \<union> box (c, b) (e, d) = box (a, b) (e, d)"
  using assms by (auto simp add: min_def max_def)

definition sparse :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "sparse d ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> d \<le> dist p\<^sub>0 p\<^sub>1)"




text \<open>
  Lemmas about Cardinality of Sets
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

lemma card_inter_2_le:
  "card (A \<inter> (B \<union> C)) \<le> card (A \<inter> B) + card (A \<inter> C)"
  by (simp add: card_Un_le inf_sup_distrib1)

lemma card_inter_3_le:
  "card (S \<inter> (A \<union> B \<union> C)) \<le> card (S \<inter> A) + card (S \<inter> B) + card (S \<inter> C)"
proof -
  have "card (S \<inter> (A \<union> B \<union> C)) \<le> card (S \<inter> A) + card (S \<inter> (B \<union> C))"
    by (simp add: card_inter_2_le sup_assoc)
  also have "... \<le> card (S \<inter> A) + card (S \<inter> B) + card (S \<inter> C)"
    using card_inter_2_le by auto
  finally show ?thesis by simp
qed

lemma card_inter_4_le:
  "card (S \<inter> (A \<union> B \<union> C \<union> D)) \<le> card (S \<inter> A) + card (S \<inter> B) + card (S \<inter> C) + card (S \<inter> D)"
proof -
  have "card (S \<inter> (A \<union> B \<union> C \<union> D)) \<le> card (S \<inter> A) + card (S \<inter> (B \<union> C \<union> D))"
    by (simp add: card_inter_2_le sup_assoc)
  also have "... \<le> card (S \<inter> A) + card (S \<inter> B) + card (S \<inter> C) + card (S \<inter> D)"
    using card_inter_3_le[of S B C D] by simp
  finally show ?thesis by simp
qed




text \<open>
  Pigeonhole Principle
\<close>

lemma pigeonhole:
  assumes "S \<subseteq> \<Union>{ A, B, C, D }" "4 < card S"
  shows "\<exists>x \<in> S. \<exists>y \<in> S. \<exists>T \<in> { A, B, C, D }. x \<noteq> y \<and> x \<in> T \<and> y \<in> T"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> S. \<exists>y \<in> S. \<exists>T \<in> { A, B, C, D }. x \<noteq> y \<and> x \<in> T \<and> y \<in> T)"

  hence "\<forall>T \<in> { A, B, C, D }. \<forall>x \<in> S. \<forall>y \<in> S. x = y \<or> x \<notin> T \<or> y \<notin> T"
    by auto
  hence *: "\<forall>T \<in> { A, B, C, D }. card (S \<inter> T) \<le> 1"
    using card_S_inter_T by auto

  have "4 < card (S \<inter> \<Union>{ A, B, C, D })"
    using Int_absorb2 assms by fastforce
  also have "... = card (S \<inter> (A \<union> B \<union> C \<union> D))"
    by (simp add: sup_assoc)
  also have "... \<le> card (S \<inter> A) + card (S \<inter> B) + card (S \<inter> C) + card (S \<inter> D)"
    using card_inter_4_le by blast
  also have "... \<le> 4"
    using * by simp
  finally show False by simp
qed




text \<open>
  Maximum Distance between two Points within a Square of size d.
\<close>

lemma maximum_dist_points_in_square:
  assumes "p\<^sub>0 = (x, y)" "p\<^sub>1 = (x + d, y + d)" "(x\<^sub>a, y\<^sub>a) \<in> box p\<^sub>0 p\<^sub>1" "(x\<^sub>b, y\<^sub>b) \<in> box p\<^sub>0 p\<^sub>1" "0 \<le> d"
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
  Maximum Number of d Sparse Points within a Square of size d. 
\<close>

lemma maximum_sparse_points_square:
  assumes "\<forall>p \<in> ps. p \<in> box (x, y) (x + d, y + d)" "sparse d ps" "0 < d"
  shows "card ps \<le> 4"
proof (rule ccontr)
  assume *: "\<not> (card ps \<le> 4)"

  let ?x' = "x + d / 2"
  let ?y' = "y + d / 2"

  let ?ll = "box ( x ,  y ) (?x'   , ?y'   )"
  let ?lu = "box ( x , ?y') (?x'   ,  y + d)"
  let ?rl = "box (?x',  y ) ( x + d, ?y'   )"
  let ?ru = "box (?x', ?y') ( x + d,  y + d)"

  have "box (x, y) (?x', y + d) = ?ll \<union> ?lu"
    using box_extend_top assms(3) by auto
  moreover have "box (?x', y) (x + d, y + d) = ?rl \<union> ?ru"
    using box_extend_top assms(3) by auto
  moreover have "box (x, y) (?x', y + d) \<union> box (?x', y) (x + d, y + d) = box (x, y) (x + d, y + d)"
    using box_extend_right assms(3) by simp
  ultimately have "?ll \<union> ?lu \<union> ?rl \<union> ?ru = box (x, y) (x + d, y + d)"
    by blast

  hence "ps \<subseteq> \<Union>{ ?ll, ?lu, ?rl, ?ru }"
    using assms(1) by blast
  moreover have "4 < card ps"
    using * by simp
  ultimately have "\<exists>p \<in> ps. \<exists>q \<in> ps. \<exists>s \<in> { ?ll, ?lu, ?rl, ?ru }. (p \<noteq> q \<and> p \<in> s \<and> q \<in> s)"
    using pigeonhole by fast
  then obtain p q s where #: "p \<in> ps" "q \<in> ps" "s \<in> { ?ll, ?lu, ?rl, ?ru }" "p \<noteq> q" "p \<in> s" "q \<in> s"
    by blast

  have D: "0 \<le> d / 2"
    using assms(3) by simp
  have LL: "\<forall>a \<in> ?ll. \<forall>b \<in> ?ll. dist a b \<le> sqrt 2 * (d / 2)"
    using maximum_dist_points_in_square[of "(x, y)" x y "(?x', ?y')" "d / 2"] D by auto
  have LU: "\<forall>a \<in> ?lu. \<forall>b \<in> ?lu. dist a b \<le> sqrt 2 * (d / 2)"
    using maximum_dist_points_in_square[of "(x, ?y')" x ?y' "(?x', y + d)" "d / 2"] D by auto
  have RL: "\<forall>a \<in> ?rl. \<forall>b \<in> ?rl. dist a b \<le> sqrt 2 * (d / 2)"
    using maximum_dist_points_in_square[of "(?x', y)" ?x' y "(x + d, ?y')" "d / 2"] D by auto
  have RU: "\<forall>a \<in> ?ru. \<forall>b \<in> ?ru. dist a b \<le> sqrt 2 * (d / 2)"
    using maximum_dist_points_in_square[of "(?x', ?y')" ?x' ?y' "(x + d, y + d)" "d / 2"] D by auto

  have "\<forall>a \<in> s. \<forall>b \<in> s. dist a b \<le> sqrt 2 * (d / 2)"
    using # LL LU RL RU by blast
  hence "dist p q \<le> (sqrt 2 / 2) * d"
    using # by simp
  moreover have "(sqrt 2 / 2) * d < d"
    using sqrt2_less_2 assms(3) by simp
  ultimately have "dist p q < d"
    by simp
  moreover have "d \<le> dist p q"
    using assms(2) sparse_def # by blast
  ultimately show False
    by simp
qed




text \<open>
  Maximum Number of d Sparse Points within a Rectangle of width 2 * d and height d. 
\<close>

lemma maximum_sparse_points_rect:
  assumes "\<forall>p \<in> ps. p \<in> box (x, y) (x + 2 * d, y + d)" "sparse d ps" "0 < d"
  shows "card ps \<le> 8"
proof -
  let ?l = "box (x    , y) (x + d    , y + d)"
  let ?r = "box (x + d, y) (x + 2 * d, y + d)"

  let ?psl = "{ p. p \<in> ps \<and> p \<in> ?l }"
  let ?psr = "{ p. p \<in> ps \<and> p \<in> ?r }" 

  have "box (x, y) (x + 2 * d, y + d) = ?l \<union> ?r"
    using assms(3) box_extend_right by simp
  hence *: "ps = ?psl \<union> ?psr"
    using assms(1) by blast

  have "\<forall>p \<in> ?psl. p \<in> ?l"
    by blast
  moreover have "sparse d ?psl"
    using assms(2) * sparse_def by blast
  hence L: "card ?psl \<le> 4"
    using assms(3) maximum_sparse_points_square[of ?psl x y d] by blast

  have "\<forall>p \<in> ?psr. p \<in> ?r"
    by blast
  moreover have "sparse d ?psr"
    using assms(2) * sparse_def by blast
  hence R: "card ?psr \<le> 4"
    using assms(3) maximum_sparse_points_square[of ?psr "x + d" y d] box.simps by fastforce

  have "card ps \<le> card ?psl + card ?psr"
    using * card_Un_le by (metis (no_types, lifting))
  thus ?thesis
    using L R by force
qed

end