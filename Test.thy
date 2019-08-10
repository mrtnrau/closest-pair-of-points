theory Test
  imports
    "HOL-Library.Code_Target_Nat"
begin

definition f :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "f x y = x + y"

export_code f in OCaml
  module_name Verified

end