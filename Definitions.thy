theory Definitions
 imports "HOL-Analysis.Analysis"
begin

type_synonym point = "real * real"

definition sparse :: "real \<Rightarrow> point set \<Rightarrow> bool" where
  "sparse d ps \<longleftrightarrow> (\<forall>p\<^sub>0 \<in> ps. \<forall>p\<^sub>1 \<in> ps. p\<^sub>0 \<noteq> p\<^sub>1 \<longrightarrow> d \<le> dist p\<^sub>0 p\<^sub>1)"

fun find_closest :: "point \<Rightarrow> point list \<Rightarrow> point" where
  "find_closest _ [] = undefined"
| "find_closest _ [p] = p"
| "find_closest p\<^sub>0 (p # ps) = (
    let c = find_closest p\<^sub>0 ps in
    if dist p\<^sub>0 p < dist p\<^sub>0 c then
      p
    else
      c
  )"

fun brute_force_closest :: "point list \<Rightarrow> (point * point)" where
  "brute_force_closest [] = undefined"
| "brute_force_closest [_] = undefined"
| "brute_force_closest [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "brute_force_closest (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = brute_force_closest ps in
    let p\<^sub>1 = find_closest p\<^sub>0 ps in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

(* combine brute_force_closest and closest_7 ? *)
fun closest_7 :: "point list \<Rightarrow> (point * point)" where
  "closest_7 [] = undefined"
| "closest_7 [_] = undefined"
| "closest_7 [p\<^sub>0, p\<^sub>1] = (p\<^sub>0, p\<^sub>1)"
| "closest_7 (p\<^sub>0 # ps) = (
    let (c\<^sub>0, c\<^sub>1) = closest_7 ps in
    let p\<^sub>1 = find_closest p\<^sub>0 (take 7 ps) in
    if dist c\<^sub>0 c\<^sub>1 \<le> dist p\<^sub>0 p\<^sub>1 then
      (c\<^sub>0, c\<^sub>1)
    else
      (p\<^sub>0, p\<^sub>1) 
  )"

fun divide :: "(point list \<Rightarrow> point list) \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> (point list * point list)" where
  "divide f xs ys = (
    let xs' = f xs in
    let ps = set xs' in
    let ys' = filter (\<lambda>p. p \<in> ps) ys in
    (xs', ys')
  )"

fun combine :: "(point * point) \<Rightarrow> (point * point) \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) l ys = (
    let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
    let \<delta> = dist c\<^sub>0 c\<^sub>1 in
    let ys' = filter (\<lambda>(x, _). l - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys in
    if length ys' < 2 then
      (c\<^sub>0, c\<^sub>1)
    else
      let (p\<^sub>0, p\<^sub>1) = closest_7 ys' in
      if dist p\<^sub>0 p\<^sub>1 < \<delta> then
        (p\<^sub>0, p\<^sub>1)
      else
        (c\<^sub>0, c\<^sub>1) 
  )"

function (sequential) closest' :: "point set \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "closest' ps xs ys = (
    let n = length xs in
    if n \<le> 3 then
      brute_force_closest xs
    else
      let (xs\<^sub>L, ys\<^sub>L) = divide (take (n div 2)) xs ys in
      let (xs\<^sub>R, ys\<^sub>R) = divide (drop (n div 2)) xs ys in

      let (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest' (set xs\<^sub>L) xs\<^sub>L ys\<^sub>L in
      let (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest' (set xs\<^sub>R) xs\<^sub>R ys\<^sub>R in

      combine (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) (fst (hd xs\<^sub>R)) ys 
  )"
  by pat_completeness auto
termination closest'
  apply (relation "Wellfounded.measure (\<lambda>(_, xs, _). length xs)")
  apply (auto simp add: Let_def)
  done

definition sortX :: "point list \<Rightarrow> point list" where
  "sortX ps = sort_key fst ps"

definition sortedX :: "point list \<Rightarrow> bool" where
  "sortedX ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. fst p\<^sub>0 \<le> fst p\<^sub>1) ps"

definition sortY :: "point list \<Rightarrow> point list" where
  "sortY ps = sort_key snd ps"

definition sortedY :: "point list \<Rightarrow> bool" where
  "sortedY ps = sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. snd p\<^sub>0 \<le> snd p\<^sub>1) ps"

definition closest :: "point list \<Rightarrow> (point * point)" where
  "closest ps = closest' (set ps) (sortX ps) (sortY ps)"

function (sequential) closest'_inline :: "point set \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> (point * point)" where
  "closest'_inline ps xs ys = (
    let n = length xs in
    if n \<le> 3 then
      brute_force_closest xs
    else
      \<comment> \<open>Divide\<close>
      let xs\<^sub>L = take (n div 2) xs in
      let ps\<^sub>L = set xs\<^sub>L in
      let ys\<^sub>L = filter (\<lambda>p. p \<in> ps\<^sub>L) ys in

      let xs\<^sub>R = drop (n div 2) xs in
      let ps\<^sub>R = set xs\<^sub>R in
      let ys\<^sub>R = filter (\<lambda>p. p \<in> ps\<^sub>R) ys in

      \<comment> \<open>Conquer\<close>
      let (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) = closest'_inline ps\<^sub>L xs\<^sub>L ys\<^sub>L in
      let (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) = closest'_inline ps\<^sub>R xs\<^sub>R ys\<^sub>R in

      \<comment> \<open>Combine\<close>
      let l = fst (hd xs\<^sub>R) in
      let (c\<^sub>0, c\<^sub>1) = if dist p\<^sub>0\<^sub>L p\<^sub>1\<^sub>L < dist p\<^sub>0\<^sub>R p\<^sub>1\<^sub>R then (p\<^sub>0\<^sub>L, p\<^sub>1\<^sub>L) else (p\<^sub>0\<^sub>R, p\<^sub>1\<^sub>R) in
      let \<delta> = dist c\<^sub>0 c\<^sub>1 in
      let ys' = filter (\<lambda>(x, _). l - \<delta> \<le> x \<and> x \<le> l + \<delta>) ys in
      if length ys' < 2 then
        (c\<^sub>0, c\<^sub>1)
      else
        let (p\<^sub>0, p\<^sub>1) = closest_7 ys' in
        if dist p\<^sub>0 p\<^sub>1 < \<delta> then
          (p\<^sub>0, p\<^sub>1)
        else
          (c\<^sub>0, c\<^sub>1) 
  )"
  by pat_completeness auto
termination closest'_inline
  apply (relation "Wellfounded.measure (\<lambda>(_, xs, _). length xs)")
  apply (auto simp add: Let_def)
  done

end