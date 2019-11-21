theory Proofs
imports Main
begin

fun f :: "nat \<Rightarrow> nat" where
"f 0 = 0" |
"f (Suc n) = f n"

lemma f0: "f n = 0"
by (induction n) simp_all

lemma long: "(True \<and> True \<and> True \<and> True \<and> True \<and> True \<and> True \<and> True) \<and>
  (True \<and> True \<and> True \<and> True \<and> True \<and> True \<and> True \<and> True)"
by blast

end