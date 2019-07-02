theory Test
  imports
  "HOL-Analysis.Analysis"
begin

section "Pigeonhole Argument"

subsection "Special Case of Isabelle Pigeonhole Lemma"

lemma pigeonhole_Isabelle:
  assumes "card (f ` P) < card P"
  shows "\<exists>x \<in> P. \<exists>y \<in> P. \<exists>B \<in> (f ` P). x \<noteq> y \<and> B = f x \<and> B = f y"
  using assms pigeonhole by (metis inj_onI rev_image_eqI)


subsection "Auxiliary Lemmas for Pigeonhole Lemma I need"

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


subsection "Pigeonhole Lemma I need"

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

end