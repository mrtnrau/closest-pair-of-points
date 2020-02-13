section \<open>Time Monad\<close>

theory Time_Monad
imports
  Main
  "HOL-Library.Monad_Syntax"
begin

datatype 'a tm = TM (val: 'a) nat

fun val :: "'a tm \<Rightarrow> 'a" where
"val (TM v n) = v"

fun time :: "'a tm \<Rightarrow> nat" where
"time (TM v n) = n"

definition bind_tm :: "'a tm \<Rightarrow> ('a \<Rightarrow> 'b tm) \<Rightarrow> 'b tm" where
"bind_tm s f = (case s of TM u m \<Rightarrow> case f u of TM v n \<Rightarrow> TM v (m+n))"

adhoc_overloading Monad_Syntax.bind bind_tm

definition "tick v = TM v 1"

definition "return v = TM v 0"

abbreviation eqtick :: "'a tm \<Rightarrow> 'a tm \<Rightarrow> bool" (infix "=1" 50) where
 "eqtick l r \<equiv> (l = (r \<bind> tick))"

(* warning: bind_tm is not a constant on purpose, does not work if it is: *)
translations "CONST eqtick l r" <= "(l = (bind_tm r CONST tick))"

lemmas tm_simps = bind_tm_def return_def tick_def

lemma time_return[simp]: "time (return x) = 0"
by(simp add: return_def)

lemma surj_TM: "v = val tm \<Longrightarrow> t = time tm \<Longrightarrow> tm = TM v t"
by (metis time.simps tm.exhaust val.simps)

text\<open>The following lemmas push @{const val} into a monadic term:\<close>

lemma val_return[simp]: "val (return x) = x"
by(simp add: return_def)

lemma val_bind_tm[simp]: "val (bind_tm m f) = (let x = val m in val(f x))"
by(simp add: bind_tm_def split: tm.split)

lemma val_tick[simp]: "val (tick x) = x"
by(simp add: tick_def)

lemma val_let: "val (let x = t in f(x)) = (let x = t in val(f x))"
by simp

lemma let_id: "(let x = t in x) = t"
  by simp

lemma time_distrib_bind:
  "time (bind_tm tm f) = time tm + time (f (val tm))"
  unfolding bind_tm_def by (simp split: tm.split)

lemmas time_simps = time_distrib_bind tick_def

lemmas val_simps =
  val_return
  val_bind_tm
  val_tick
  val_let
  let_id
  if_distrib[of val]
  prod.case_distrib[of val]

lemmas val_cong = arg_cong[where f=val]

lemma bind_tm_cong[fundef_cong]:
  assumes "\<And>v. v = val n \<Longrightarrow> f v = g v" "m = n"
  shows "bind_tm m f = bind_tm n g"
  using assms unfolding bind_tm_def by (auto split: tm.split)

hide_const TM

end
