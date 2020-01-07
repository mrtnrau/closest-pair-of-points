(*  Title:      HOL/Library/OptionalSugar.thy
    Author:     Gerwin Klein, Tobias Nipkow
    Copyright   2005 NICTA and TUM
*)
(*<*)
theory OptionalSugarLocal
imports Complex_Main LaTeXsugarLocal
begin

(* displaying theorems with conjunctions between premises: *)
translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"

(* hiding set *)
(*translations
  "xs" <= "CONST set xs"*)

notation (latex output)
  log  ("\<^latex>\<open>$\\log$\<close>\<^bsub>_\<^esub>")

notation (latex output)
  ln  ("\<^latex>\<open>$\\ln$\<close>")

notation (latex output)
  sqrt ("\<^latex>\<open>$\\sqrt{\<close>_\<^latex>\<open>}$\<close>")

(* hiding numeric conversions - embeddings only *)
translations
  "n" <= "CONST of_nat n"
  "n" <= "CONST int n"
  "n" <= "CONST real n"
  "n" <= "CONST real_of_nat n"
  "n" <= "CONST real_of_int n"
  "n" <= "CONST of_real n"
  "n" <= "CONST complex_of_real n"
  "n" <= "CONST nat n"

(* append *)
syntax (latex output)
  "_appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^latex>\<open>\\isacharat\<close>" 65)
translations
  "_appendL xs ys" <= "xs @ ys" 
  "_appendL (_appendL xs ys) zs" <= "_appendL xs (_appendL ys zs)"


(* deprecated, use thm with style instead, will be removed *)
(* aligning equations *)
notation (tab output)
  "HOL.eq"  ("(_) \<^latex>\<open>}\\putisatab\\isa{\\ \<close>=\<^latex>\<open>}\\putisatab\\isa{\<close> (_)" [50,49] 50) and
  "Pure.eq"  ("(_) \<^latex>\<open>}\\putisatab\\isa{\\ \<close>\<equiv>\<^latex>\<open>}\\putisatab\\isa{\<close> (_)")

(* Let *)
translations 
  "_bind (p, CONST DUMMY) e" <= "_bind p (CONST fst e)"
  "_bind (CONST DUMMY, p) e" <= "_bind p (CONST snd e)"

  "_tuple_args x (_tuple_args y z)" ==
    "_tuple_args x (_tuple_arg (_tuple y z))"

  "_bind (CONST Some p) e" <= "_bind p (CONST the e)"
(*  "_bind (p # CONST DUMMY) e" <= "_bind p (CONST hd e)" *)
(*  "_bind (CONST DUMMY # p) e" <= "_bind p (CONST tl e)" *)

(* type constraints with spacing *)
no_syntax (output)
  "_constrain" :: "logic => type => logic"  ("_::_" [4, 0] 3)
  "_constrain" :: "prop' => type => prop'"  ("_::_" [4, 0] 3)

syntax (output)
  "_constrain" :: "logic => type => logic"  ("_ :: _" [4, 0] 3)
  "_constrain" :: "prop' => type => prop'"  ("_ :: _" [4, 0] 3)


(* sorts as intersections *)

syntax (output)
  "_topsort" :: "sort"  ("\<top>" 1000)
  "_sort" :: "classes => sort"  ("'(_')" 1000)
  "_classes" :: "id => classes => classes"  ("_ \<inter> _" 1000)
  "_classes" :: "longid => classes => classes"  ("_ \<inter> _" 1000)

end
(*>*)
