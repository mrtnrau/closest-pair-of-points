theory Test
imports
  "HOL-Analysis.Analysis"
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.Code_Real_Approx_By_Float"
begin

type_synonym point = "int * int"

fun dist_code :: "point \<Rightarrow> point \<Rightarrow> int" where
  "dist_code p\<^sub>0 p\<^sub>1 = (fst p\<^sub>0 - fst p\<^sub>1)\<^sup>2 + (snd p\<^sub>0 - snd p\<^sub>1)\<^sup>2"

fun find_closest :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest _ [] = undefined"
| "find_closest _ [p] = p"
| "find_closest p (p\<^sub>0 # ps) = (
    let p\<^sub>1 = find_closest p ps in
    if dist p p\<^sub>0 < dist p p\<^sub>1 then
      p\<^sub>0
    else
      p\<^sub>1
  )"

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

declare dist_code.simps [simp del]

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
    by blast
  thus ?case
    using "3.prems"(2,3) * defs by (auto split: prod.splits)
qed auto

declare find_closest_code.simps [simp del]

declare [[code drop: "(<) :: real \<Rightarrow> real \<Rightarrow> bool" "(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool"]] 

export_code find_closest_code in OCaml
  module_name Verified

end