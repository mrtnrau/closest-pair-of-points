theory Test
  imports
  "HOL-Library.Code_Real_Approx_By_Float"
begin

definition f :: "real \<Rightarrow> bool" where
  "f x \<longleftrightarrow> x < x" (* \<le> *)

export_code f in SML

text \<open>
  Fails for all export languages for < and \<le> respectively with:

  "Real.Ratreal" is not a constructor, on left hand side of equation, in theorem:
  ord_real_inst.less_real (Ratreal ?x) (Ratreal ?y) \<equiv> ord_rat_inst.less_rat ?x ?y

  "Real.Ratreal" is not a constructor, on left hand side of equation, in theorem:
  ord_real_inst.less_eq_real (Ratreal ?x) (Ratreal ?y) \<equiv> ord_rat_inst.less_eq_rat ?x ?y
\<close>

end