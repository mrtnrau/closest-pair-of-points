theory Closest_Pair_Code
  imports Closest_Pair
begin

(*
  TODO: (blocked by minimizing dist computations)
    - tail recursive functions for code export
*)

lemma dist_point:
  fixes p\<^sub>0 :: point and p\<^sub>1 :: point
  shows "dist p\<^sub>0 p\<^sub>1 = sqrt ((fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2)"
  by (auto simp: dist_prod_def dist_real_def) 

fun dist_code :: "point \<Rightarrow> point \<Rightarrow> real" where
  "dist_code p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

lemma dist_eq_dist_code_lt:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 < dist p\<^sub>2 p\<^sub>3 \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 < dist_code p\<^sub>2 p\<^sub>3"
  using dist_point by simp

lemma dist_eq_dist_code_le:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 \<le> dist p\<^sub>2 p\<^sub>3 \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 \<le> dist_code p\<^sub>2 p\<^sub>3"
  using dist_point by simp

lemma dist_eq_dist_code_abs_1:
  fixes p\<^sub>0 :: point
  shows "\<bar>c\<bar> \<le> dist p\<^sub>0 p\<^sub>1 \<longleftrightarrow> c\<^sup>2 \<le> dist_code p\<^sub>0 p\<^sub>1"
  using dist_point by (metis dist_code.simps real_sqrt_abs real_sqrt_le_iff sqrt_ge_absD)

lemma dist_eq_dist_code_abs_2:
  fixes p\<^sub>0 :: point
  shows "dist p\<^sub>0 p\<^sub>1 \<le> \<bar>c\<bar> \<longleftrightarrow> dist_code p\<^sub>0 p\<^sub>1 \<le> c\<^sup>2"
  using dist_point by (metis dist_code.simps real_sqrt_abs real_sqrt_le_iff)

fun find_closest_\<delta>_code :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest_\<delta>_code p \<delta> [] = undefined"
| "find_closest_\<delta>_code p \<delta> [c] = c"
| "find_closest_\<delta>_code p \<delta> (c\<^sub>0 # cs) = (
    if \<delta> \<le> (snd c\<^sub>0 - snd p)\<^sup>2 then
      c\<^sub>0
    else
      let c\<^sub>1 = find_closest_\<delta>_code p \<delta> cs in
      if dist_code p c\<^sub>0 \<le> dist_code p c\<^sub>1 then
        c\<^sub>0
      else
        c\<^sub>1
  )"

declare dist_code.simps [simp del]
declare find_closest_\<delta>.simps [simp add]
declare closest_pair_combine.simps [simp add]
declare combine.simps [simp add]

lemma find_closest_\<delta>_eq_find_closest_\<delta>_code:
  "\<delta> = dist p\<^sub>0 p\<^sub>1 \<Longrightarrow> \<delta>\<^sub>c = dist_code p\<^sub>0 p\<^sub>1 \<Longrightarrow> find_closest_\<delta> p \<delta> ps = find_closest_\<delta>_code p \<delta>\<^sub>c ps"
  by (induction p \<delta> ps rule: find_closest_\<delta>.induct)
     (auto simp: Let_def dist_eq_dist_code_le dist_eq_dist_code_abs_2)

fun closest_pair_combine_code :: "real \<Rightarrow> point list \<Rightarrow> point * point" where
  "closest_pair_combine_code \<delta> [] = undefined"
| "closest_pair_combine_code \<delta> [p] = undefined"
| "closest_pair_combine_code \<delta> [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_pair_combine_code \<delta> (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_pair_combine_code \<delta> ps in
    let c = find_closest_\<delta>_code p\<^sub>0 (min \<delta> (dist_code c\<^sub>0 c\<^sub>1)) ps in
    if dist_code c\<^sub>0 c\<^sub>1 \<le> dist_code p\<^sub>0 c then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, c)
  )"

lemma closest_pair_combine_eq_closest_pair_combine_code:
  "\<delta> = dist p\<^sub>0 p\<^sub>1 \<Longrightarrow> \<delta>\<^sub>c = dist_code p\<^sub>0 p\<^sub>1 \<Longrightarrow> closest_pair_combine \<delta> ps = closest_pair_combine_code \<delta>\<^sub>c ps"
  by (induction \<delta> ps arbitrary: \<delta>\<^sub>c p\<^sub>0 p\<^sub>1 rule: closest_pair_combine.induct)
     (auto simp: Let_def min_def find_closest_\<delta>_eq_find_closest_\<delta>_code dist_eq_dist_code_le dist_eq_dist_code_abs_2 split!: prod.splits)

fun combine_code :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine_code (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = (
    let (c\<^sub>0, c\<^sub>1) = if dist_code p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist_code p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let \<delta> = dist_code c\<^sub>0 c\<^sub>1 in
    let ps' = filter (\<lambda>p. (fst p - l)\<^sup>2 \<le> \<delta>) ps in
    if length ps' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_pair_combine_code \<delta> ps' in
      if dist_code p\<^sub>0 p\<^sub>1 < \<delta> then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

lemma combine_eq_combine_code:
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps = combine_code (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ps"
  by (auto simp: Let_def closest_pair_combine_eq_closest_pair_combine_code dist_eq_dist_code_lt dist_eq_dist_code_abs_1)


(* *)


fun fc :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (real * point)" where
  "fc p \<delta> [] = undefined"
| "fc p \<delta> [c] = (dist p c, c)"
| "fc p \<delta> (c\<^sub>0 # cs) = (
    let \<delta>\<^sub>0 = dist p c\<^sub>0 in
    if \<delta> \<le> \<bar>snd c\<^sub>0 - snd p\<bar> then
      (\<delta>\<^sub>0, c\<^sub>0)
    else
      let (\<delta>\<^sub>1, c\<^sub>1) = fc p (min \<delta> \<delta>\<^sub>0) cs in
      if \<delta>\<^sub>0 \<le> \<delta>\<^sub>1 then
        (\<delta>\<^sub>0, c\<^sub>0)
      else
        (\<delta>\<^sub>1, c\<^sub>1)
  )"

fun fcc :: "point \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (real * point)" where
  "fcc p \<delta> [] = undefined"
| "fcc p \<delta> [c] = (dist_code p c, c)"
| "fcc p \<delta> (c\<^sub>0 # cs) = (
    let \<delta>\<^sub>0 = dist_code p c\<^sub>0 in
    if \<delta> \<le> (snd c\<^sub>0 - snd p)\<^sup>2 then
      (\<delta>\<^sub>0, c\<^sub>0)
    else
      let (\<delta>\<^sub>1, c\<^sub>1) = fcc p (min \<delta> \<delta>\<^sub>0) cs in
      if \<delta>\<^sub>0 \<le> \<delta>\<^sub>1 then
        (\<delta>\<^sub>0, c\<^sub>0)
      else
        (\<delta>\<^sub>1, c\<^sub>1)
  )"

lemma A1:
  "0 < length cs \<Longrightarrow> (\<delta>\<^sub>c, c) = fc p \<delta> cs \<Longrightarrow> \<delta>\<^sub>c = dist p c"
proof (induction p \<delta> cs arbitrary: \<delta>\<^sub>c c rule: fc.induct)
  case (3 p \<delta> c\<^sub>0 c\<^sub>2 cs)
  show ?case
  proof cases
    assume "\<delta> \<le> \<bar>snd c\<^sub>0 - snd p\<bar>"
    thus ?thesis
      using "3.prems" by simp
  next
    assume *: "\<not> \<delta> \<le> \<bar>snd c\<^sub>0 - snd p\<bar>"
    define \<delta>\<^sub>0 where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist p c\<^sub>0"
    obtain \<delta>\<^sub>1 c\<^sub>1 where \<delta>\<^sub>1_def: "(\<delta>\<^sub>1, c\<^sub>1) = fc p (min \<delta> \<delta>\<^sub>0) (c\<^sub>2 # cs)"
      by (metis surj_pair)
    note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
    have "\<delta>\<^sub>1 = dist p c\<^sub>1"
      using "3.IH"[of \<delta>\<^sub>0 \<delta>\<^sub>1 c\<^sub>1] * defs by simp
    thus ?thesis
      using defs "3.prems" by (auto simp: Let_def split: if_splits prod.splits)
  qed
qed simp_all

lemma A2:
  "0 < length cs \<Longrightarrow> (\<delta>\<^sub>c, c) = fcc p \<delta> cs \<Longrightarrow> \<delta>\<^sub>c = dist_code p c"
proof (induction p \<delta> cs arbitrary: \<delta>\<^sub>c c rule: fcc.induct)
  case (3 p \<delta> c\<^sub>0 c\<^sub>2 cs)
  show ?case
  proof cases
    assume "\<delta> \<le> (snd c\<^sub>0 - snd p)\<^sup>2"
    thus ?thesis
      using "3.prems" by simp
  next
    assume *: "\<not> \<delta> \<le> (snd c\<^sub>0 - snd p)\<^sup>2"
    define \<delta>\<^sub>0 where \<delta>\<^sub>0_def: "\<delta>\<^sub>0 = dist_code p c\<^sub>0"
    obtain \<delta>\<^sub>1 c\<^sub>1 where \<delta>\<^sub>1_def: "(\<delta>\<^sub>1, c\<^sub>1) = fcc p (min \<delta> \<delta>\<^sub>0) (c\<^sub>2 # cs)"
      by (metis surj_pair)
    note defs = \<delta>\<^sub>0_def \<delta>\<^sub>1_def
    have "\<delta>\<^sub>1 = dist_code p c\<^sub>1"
      using "3.IH"[of \<delta>\<^sub>0 \<delta>\<^sub>1 c\<^sub>1] * defs by simp
    thus ?thesis
      using defs "3.prems" by (auto simp: Let_def split: if_splits prod.splits)
  qed
qed simp_all

lemma
  assumes "0 < length cs" "\<delta> = dist p\<^sub>0 p\<^sub>1" "\<delta>' = dist_code p\<^sub>0 p\<^sub>1"
  assumes "(\<delta>\<^sub>l, c\<^sub>l) = fc p \<delta> cs" "(\<delta>\<^sub>r, c\<^sub>r) = fcc p \<delta>' cs"
  shows "c\<^sub>l = c\<^sub>r"
  using assms
proof (induction p \<delta> cs arbitrary: \<delta>' p\<^sub>0 p\<^sub>1 \<delta>\<^sub>l c\<^sub>l \<delta>\<^sub>r c\<^sub>r rule: fc.induct)
  case (3 p \<delta> c\<^sub>0 c\<^sub>2 cs)

  define \<delta>\<^sub>0 where a: "\<delta>\<^sub>0 = dist p c\<^sub>0"
  define \<delta>\<^sub>0' where b: "\<delta>\<^sub>0' = dist_code p c\<^sub>0"
  obtain \<delta>\<^sub>1 c\<^sub>1 where c: "(\<delta>\<^sub>1, c\<^sub>1) = fc p (min \<delta> \<delta>\<^sub>0) (c\<^sub>2 # cs)"
    by (metis surj_pair)
  hence B1: "\<delta>\<^sub>1 = dist p c\<^sub>1"
    using A1 by blast
  obtain \<delta>\<^sub>1' c\<^sub>1' where d: "(\<delta>\<^sub>1', c\<^sub>1') = fcc p (min \<delta>' \<delta>\<^sub>0') (c\<^sub>2 # cs)"
    by (metis surj_pair)
  hence B2: "\<delta>\<^sub>1' = dist_code p c\<^sub>1'"
    using A2 by blast
  note defs = a b c d
  
  show ?case
  proof (cases "\<delta> \<le> \<bar>snd c\<^sub>0 - snd p\<bar>")
    case True
    then show ?thesis using "3.prems"
      by (auto simp: Let_def dist_eq_dist_code_abs_2 split: if_splits prod.splits)
  next
    case False
    hence *: "c\<^sub>1 = c\<^sub>1'"
      using "3.IH"[of \<delta>\<^sub>0 _ _ "min \<delta>' \<delta>\<^sub>0'" \<delta>\<^sub>1 c\<^sub>1 \<delta>\<^sub>1' c\<^sub>1'] defs
      by (smt "3.prems"(2) "3.prems"(3) dist_eq_dist_code_le length_greater_0_conv list.discI)
    show ?thesis
    proof cases
      assume "\<delta>\<^sub>0 \<le> \<delta>\<^sub>1"
      moreover have "\<delta>\<^sub>0' \<le> \<delta>\<^sub>1'"
        using calculation by (simp add: * B1 B2 defs dist_eq_dist_code_le)
      ultimately show ?thesis
        using "3.prems" * False defs by (auto simp: Let_def split: if_splits prod.splits)
    next
      assume "\<not> \<delta>\<^sub>0 \<le> \<delta>\<^sub>1"
      moreover have "\<not> \<delta>\<^sub>0' \<le> \<delta>\<^sub>1'"
        using calculation by (simp add: * B1 B2 defs dist_eq_dist_code_le)
      ultimately show ?thesis 
        using "3.prems" * False defs by (auto simp: Let_def dist_eq_dist_code_abs_2 split: if_splits prod.splits)
    qed
  qed
qed auto

end