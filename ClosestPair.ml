type point = float * float

let dist ((x0, y0) : point) ((x1, y1) : point): float =
  let dx = x0 -. x1
  and dy = y0 -. y1 in
  dx *. dx +. dy *. dy

let format_point ((x, y) : point): string =
  Printf.sprintf "(%.2f, %.2f)" x y

let random_point (): point =
  let x = Random.float 1000000.0
  and y = Random.float 1000000.0
  in (x, y)

let random_points (n : int): point array =
  Random.self_init ();
  let arr = Array.make n (0.0, 0.0) in
  for i = 0 to n - 1 do
    Array.unsafe_set arr i (random_point ())
  done;
  arr

module Time : sig
  val statistics : (unit -> 'a) list -> int -> float list
end =
struct
  let time (f : unit -> 'a): float =
    let start = Sys.time()
    and _ = f () in
    Sys.time() -. start

  let times (f : unit -> 'a) (n : int): float =
    let cnt = ref 0.0 in
    for _ = 1 to n do
      cnt := !cnt +. time f
    done;
    !cnt /. float_of_int n

  let statistics fs n =
    List.map(fun f -> times f n) fs
end

module Mutable : sig
  val bf_closest_pair : point array -> point * point
  val closest_pair : point array -> point * point
end =
struct
  let bf_closest_pair' (ps : point array) (l : int) (h : int): point * point =
    let p0 = ref (Array.unsafe_get ps l)
    and p1 = ref (Array.unsafe_get ps (l + 1)) in
    let delta = ref (dist !p0 !p1) in
    for i = l to h do
      let c0 = Array.unsafe_get ps i in
      for j = i + 1 to h do
        let c1 = Array.unsafe_get ps j in
        let d = dist c0 c1 in
        if d < !delta then
          begin
            p0 := c0;
            p1 := c1;
            delta := d;
          end
      done;
    done;
    (!p0, !p1)

  let bf_closest_pair ps =
    bf_closest_pair' ps 0 (Array.length ps - 1)

  let sort_by_y (ps : point array) (l : int) (h : int): unit =
    let arr = Array.sub ps l (h - l + 1) in
    Array.stable_sort (fun (_, y0) (_, y1) -> int_of_float (y0 -. y1)) arr;
    Array.blit arr 0 ps l (h - l + 1)

  let sort_by_x (ps : point array) (l : int) (h : int): unit =
    let arr = Array.sub ps l (h - l + 1) in
    Array.stable_sort (fun (x0, _) (x1, _) -> int_of_float (x0 -. x1)) arr;
    Array.blit arr 0 ps l (h - l + 1)

  let merge (ps : point array) (aux : point array) (l : int) (m : int) (h : int): unit =
    for k = l to h do
      Array.unsafe_set aux k (Array.unsafe_get ps k)
    done;
    let i = ref l
    and j = ref (m + 1) in
    for k = l to h do
      if !i > m then
        begin
          Array.unsafe_set ps k (Array.unsafe_get aux !j);
          j := !j + 1
        end
      else if !j > h then
        begin
          Array.unsafe_set ps k (Array.unsafe_get aux !i);
          i := !i + 1
        end
      else if snd (Array.unsafe_get aux !j) <= snd (Array.unsafe_get aux !i) then
        begin
          Array.unsafe_set ps k (Array.unsafe_get aux !j);
          j := !j + 1
        end
      else
        begin
          Array.unsafe_set ps k (Array.unsafe_get aux !i);
          i := !i + 1
        end;
    done

  let rec closest_pair_rec (xs : point array) (ys : point array) (aux : point array) (l : int) (h : int): point * point =
    if (h - l <= 2) then
      begin
        sort_by_y ys l h;
        bf_closest_pair' xs l h
      end
    else
      begin
        let m = l + (h - l) / 2 in
        let median = Array.unsafe_get xs m in
        let (lp0, lp1) = closest_pair_rec xs ys aux l m in
        let (rp0, rp1) = closest_pair_rec xs ys aux (m + 1) h in
        let (p0', p1') = if dist lp0 lp1 <= dist rp0 rp1 then (lp0, lp1) else (rp0, rp1) in
        let p0 = ref p0' in
        let p1 = ref p1' in
        let delta = ref (dist !p0 !p1) in

        merge ys aux l m h;

        let k = ref 0 in
        for i = l to h do
          if abs_float (fst (Array.unsafe_get ys i) -. fst median) <= !delta then
            begin
              Array.unsafe_set aux !k (Array.unsafe_get ys i);
              k := !k + 1
            end
        done;

        for i = 0 to !k - 1 do
          let j = ref (i + 1) in
          while !j < !k && snd (Array.unsafe_get aux !j) -. snd (Array.unsafe_get aux i) < !delta do
            let d = dist (Array.unsafe_get aux i) (Array.unsafe_get aux !j) in
            if d < !delta then
              begin
                delta := d;
                p0 := Array.unsafe_get aux i;
                p1 := Array.unsafe_get aux !j
              end;
            j := !j + 1
          done;
        done;

        (!p0, !p1)
      end

  let closest_pair ps =
    let n = Array.length ps in
    sort_by_x ps 0 (n - 1);
    closest_pair_rec ps (Array.copy ps) (Array.init n (fun _ -> (0.0, 0.0))) 0 (n - 1)
end

module Immutable : sig
  val bf_closest_pair : point list -> point * point
  val closest_pair : point list -> point * point
end =
struct

  let rec length_rec (acc : int) (xs : 'a list): int =
    match xs with
    | [] -> acc
    | _ :: xs -> (length_rec[@tailcall]) (acc + 1) xs

  let length (xs : 'a list) : int =
    length_rec 0 xs

  let rec reverse_rec (acc : 'a list) (xs : 'a list): 'a list =
      match xs with
      | [] -> acc
      | x :: xs -> (reverse_rec[@tailcall]) (x :: acc) xs

  let reverse (xs : 'a list): 'a list =
    reverse_rec [] xs

  let rec filter_rec (f : 'a -> bool) (acc : 'a list) (xs : 'a list): 'a list =
      match xs with
      | [] -> reverse acc
      | x :: xs -> if f x then (filter_rec[@tailcall]) f (x :: acc) xs else (filter_rec[@tailcall]) f acc xs

  let filter (f : 'a -> bool) (xs : 'a list): 'a list =
      filter_rec f [] xs

  let rec split_at (n : int) (acc : 'a list) (xs : 'a list): 'a list * 'a list =
    match xs with
    | [] -> (reverse acc, xs)
    | x :: xs -> if n <= 0 then (reverse acc, x :: xs) else (split_at (n - 1)[@tailcall]) (x :: acc) xs

  let split_at (n : int) (xs : 'a list): 'a list * 'a list =
    split_at n [] xs

  let rec find_closest (p : point) (c0: point) (ps: point list): point =
    match ps with
    | [] -> c0
    | c1 :: ps -> if dist p c0 <= dist p c1 then (find_closest[@tailcall]) p c0 ps else (find_closest[@tailcall]) p c1 ps

  let rec bf_closest_pair_rec (f : point list -> point list) (c0 : point) (c1 : point) (ps : point list): point * point =
    match ps with
    | p0 :: p2 :: ps ->
      let p1 = find_closest p0 p2 (f ps) in
      if dist c0 c1 <= dist p0 p1 then
        (bf_closest_pair_rec[@tailcall]) f c0 c1 (p2 :: ps)
      else
        (bf_closest_pair_rec[@tailcall]) f p0 p1 (p2 :: ps)
    | _ -> (c0, c1)

  let bf_closest_pair (ps : point list): point * point =
    match ps with
    | p0 :: p1 :: ps -> bf_closest_pair_rec (fun ps -> ps) p0 p1 (p0 :: p1 :: ps)
    | _ -> raise (Invalid_argument "Not enough points")

  let bf_closest_pair_7 (ps: point list): point * point =
    match ps with
    | p0 :: p1 :: ps -> bf_closest_pair_rec (fun ps -> fst (split_at 6 ps)) p0 p1 (p0 :: p1 :: ps)
    | _ -> raise (Invalid_argument "Not enough points")

  let rec merge (f : point -> float) (ps : point list) (ps0 : point list) (ps1 : point list): point list =
    match (ps0, ps1) with
    | (p0 :: ps0, p1 :: ps1) ->
        if f p0 <= f p1 then
          (merge[@tailcall]) f (p0 :: ps) ps0 (p1 :: ps1)
        else
          (merge[@tailcall]) f (p1 :: ps) (p0 :: ps0) ps1
    | ([], p1 :: ps1) -> (merge[@tailcall]) f (p1 :: ps) [] ps1
    | (p0 :: ps0, []) -> (merge[@tailcall]) f (p0 :: ps) ps0 []
    | ([], []) -> reverse ps

  let merge (f : point -> float) (ps0 : point list) (ps1 : point list): point list =
    merge f [] ps0 ps1

  let rec msort (f : point -> float) (ps : point list): point list =
    let n = length ps in
    if n <= 1 then
      ps
    else
      let (l, r) = split_at (n / 2) ps in
      merge f (msort f l) (msort f r)

  let rec closest_pair_rec (psX : point list): point list * (point * point) =
    let n = length psX in
    if n <= 3 then
      (msort snd psX, bf_closest_pair psX)
    else
      let (lx, rx) = split_at (n / 2) psX in
      let l = fst (List.hd rx) in
      let (ysL, (lp0, lp1)) = closest_pair_rec lx in
      let (ysR, (rp0, rp1)) = closest_pair_rec rx in
      let psY = merge snd ysL ysR in
      let (p0, p1) = if dist lp0 lp1 <= dist rp0 rp1 then (lp0, lp1) else (rp0, rp1) in
      let delta = dist p0 p1 in
      let ys = filter (fun p -> l -. delta <= fst p && fst p <= l +. delta) psY in
      if length ys < 2 then
        (psY, (p0, p1))
      else
        let (c0, c1) = bf_closest_pair_7 ys in
        if dist p0 p1 <= dist c0 c1 then
          (psY, (p0, p1))
        else
          (psY, (c0, c1))

    let closest_pair ps =
      snd (closest_pair_rec (msort fst ps))
end

module Z : sig
  type t = int
  val zero : t
  val leq : t -> t -> bool
  val lt : t -> t -> bool
  val equal : t -> t -> bool
  val of_int : t -> int
  val sub : t -> t -> t
  val add : t -> t -> t
  val neg : t -> t
  val abs : t -> t
  val div_rem : t -> t -> t * t
end = struct
  type t = int
  let zero = 0
  let leq = (<=)
  let lt = (<)
  let equal = (=)
  let of_int x = x
  let sub = (-)
  let add = (+)
  let neg x = -x
  let abs = Pervasives.abs
  let div_rem x y = (x / y, x mod y)
end

module Verified : sig
  val closest_pair : (float * float) list -> (float * float) * (float * float)
end = struct

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_real = ({one = 1.0} : float one);;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_real = ({times = Pervasives.( *. )} : float times);;

let power_real =
  ({one_power = one_real; times_power = times_real} : float power);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let ord_real =
  ({less_eq = Pervasives.(<=); less = Pervasives.(<)} : float ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_real = ({ord_preorder = ord_real} : float preorder);;

let order_real = ({preorder_order = preorder_real} : float order);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_real = ({order_linorder = order_real} : float linorder);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type nat = Nat of Z.t;;

type num = One | Bit0 of num | Bit1 of num;;

let rec integer_of_nat (Nat x) = x;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec equal_nat m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let zero_nat : nat = Nat Z.zero;;

let one_nat : nat = Nat (Z.of_int 1);;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nat n zero_nat then []
          else x :: take (minus_nat n one_nat) xs);;

let rec hd (x21 :: x22) = x21;;

let rec apsnd f (x, y) = (x, f y);;

let divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec rev_it_rec acc x1 = match acc, x1 with acc, [] -> acc
                     | acc, x :: xs -> rev_it_rec (x :: acc) xs;;

let rec rev_it xs = rev_it_rec [] xs;;

let rec split_at_it_rec
  acc n x2 = match acc, n, x2 with acc, n, [] -> (rev_it acc, [])
    | acc, n, x :: xs ->
        (if equal_nat n zero_nat then (rev_it acc, x :: xs)
          else split_at_it_rec (x :: acc) (minus_nat n one_nat) xs);;

let rec split_at_it n xs = split_at_it_rec [] n xs;;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let rec length_it_rec
  acc x1 = match acc, x1 with acc, [] -> acc
    | acc, x :: xs -> length_it_rec (plus_nat acc one_nat) xs;;

let rec length_it xs = length_it_rec zero_nat xs;;

let rec merge_it_rec _B
  f acc x2 x3 = match f, acc, x2, x3 with f, acc, [], [] -> rev_it acc
    | f, acc, x :: xs, [] -> merge_it_rec _B f (x :: acc) xs []
    | f, acc, [], y :: ys -> merge_it_rec _B f (y :: acc) ys []
    | f, acc, x :: xs, y :: ys ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then merge_it_rec _B f (x :: acc) xs (y :: ys)
          else merge_it_rec _B f (y :: acc) (x :: xs) ys);;

let rec merge_it _B f xs ys = merge_it_rec _B f [] xs ys;;

let rec msort _B
  f x1 = match f, x1 with f, [] -> []
    | f, [x] -> [x]
    | f, x :: y :: xs ->
        (let xsa = x :: y :: xs in
         let n = divide_nat (length_it xsa) (nat_of_integer (Z.of_int 2)) in
         let (l, r) = split_at_it n xsa in
          merge_it _B f (msort _B f l) (msort _B f r));;

let rec sortX ps = msort linorder_real fst ps;;

let rec snd (x1, x2) = x2;;

let rec sortY ps = msort linorder_real snd ps;;

let rec power _A
  a n = (if equal_nat n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nat)));;

let rec dist_code
  p_0 p_1 =
    Pervasives.( +. )
      (power power_real (Pervasives.( -. ) (fst p_0) (fst p_1))
        (nat_of_integer (Z.of_int 2)))
      (power power_real (Pervasives.( -. ) (snd p_0) (snd p_1))
        (nat_of_integer (Z.of_int 2)));;

let rec find_closest_it_rec
  p c_0 x2 = match p, c_0, x2 with p, c_0, [] -> c_0
    | p, c_0, c_1 :: cs ->
        (if Pervasives.(<) (dist_code p c_0) (dist_code p c_1)
          then find_closest_it_rec p c_0 cs else find_closest_it_rec p c_1 cs);;

let rec find_closest_it
  uu x1 = match uu, x1 with uu, [] -> failwith "undefined"
    | p, p_0 :: ps -> find_closest_it_rec p p_0 ps;;

let rec gen_closest_pair_it_rec
  f x1 x2 = match f, x1, x2 with f, (c_0, c_1), [] -> (c_0, c_1)
    | f, (c_0, c_1), [p_0] -> (c_0, c_1)
    | f, (c_0, c_1), p_0 :: v :: va ->
        (let p_1 = find_closest_it p_0 (f (v :: va)) in
          (if Pervasives.(<) (dist_code c_0 c_1) (dist_code p_0 p_1)
            then gen_closest_pair_it_rec f (c_0, c_1) (v :: va)
            else gen_closest_pair_it_rec f (p_0, p_1) (v :: va)));;

let rec gen_closest_pair_it
  f x1 = match f, x1 with
    f, p_0 :: p_1 :: ps ->
      gen_closest_pair_it_rec f (p_0, find_closest_it p_0 (f (p_1 :: ps)))
        (p_1 :: ps)
    | uu, [] -> failwith "undefined"
    | uu, [v] -> failwith "undefined";;

let rec bf_closest_pair_it ps = gen_closest_pair_it (fun psa -> psa) ps;;

let rec closest_pair_7_it
  ps = gen_closest_pair_it (take (nat_of_integer (Z.of_int 7))) ps;;

let rec filter_it_rec
  acc p x2 = match acc, p, x2 with acc, p, [] -> rev_it acc
    | acc, p, x :: xs ->
        (if p x then filter_it_rec (x :: acc) p xs
          else filter_it_rec acc p xs);;

let rec filter_it p xs = filter_it_rec [] p xs;;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let rec combine_code
  (p_0_L, p_1_L) (p_0_R, p_1_R) l ys =
    (let (c_0, c_1) =
       (if Pervasives.(<) (dist_code p_0_L p_1_L) (dist_code p_0_R p_1_R)
         then (p_0_L, p_1_L) else (p_0_R, p_1_R))
       in
     let ysa =
       filter_it
         (fun p -> Pervasives.(<=) (dist_code p (l, snd p)) (dist_code c_0 c_1))
         ys
       in
      (if less_nat (length_it ysa) (nat_of_integer (Z.of_int 2)) then (c_0, c_1)
        else (let (p_0, p_1) = closest_pair_7_it ysa in
               (if Pervasives.(<) (dist_code p_0 p_1) (dist_code c_0 c_1)
                 then (p_0, p_1) else (c_0, c_1)))));;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec closest_pair_rec
  xs = (let n = length_it xs in
         (if less_eq_nat n (nat_of_integer (Z.of_int 3))
           then (sortY xs, bf_closest_pair_it xs)
           else (let (xs_L, xs_R) =
                   split_at_it (divide_nat n (nat_of_integer (Z.of_int 2))) xs
                   in
                 let l = fst (hd xs_R) in
                 let (ys_L, (c_0_L, c_1_L)) = closest_pair_rec xs_L in
                 let (ys_R, (c_0_R, c_1_R)) = closest_pair_rec xs_R in
                 let ys = merge_it linorder_real snd ys_L ys_R in
                  (ys, combine_code (c_0_L, c_1_L) (c_0_R, c_1_R) l ys))));;

let rec closest_pair ps = (let (_, c) = closest_pair_rec (sortX ps) in c);;

end;; (*struct Verified*)

let print_header (header : int list): unit =
  Printf.printf "  \t";
  List.iter (fun n -> Printf.printf "%d\t\t" n) header;
  print_newline ()

let print_stat_row (label : string) (row : float list): unit =
  Printf.printf "%s:\t" label;
  List.iter (fun stat -> Printf.printf "%.5f\t\t" stat) row;
  print_newline ()

let _ =
  let iteration = int_of_string (Sys.argv.(1)) in
  let ns = Array.sub Sys.argv 2 (Array.length Sys.argv - 2) |> Array.map int_of_string |> Array.to_list in
  let ps = List.map random_points ns in

  let mstats = List.map (fun ps -> fun () -> Mutable.closest_pair ps) ps in
  let istats = List.map (fun ps -> fun () -> Immutable.closest_pair ps) (List.map Array.to_list ps) in
  let vstats = List.map (fun ps -> fun () -> Verified.closest_pair ps) (List.map Array.to_list ps) in

  print_header ns;
  print_stat_row "M" (Time.statistics mstats iteration);
  print_stat_row "I" (Time.statistics istats iteration);
  print_stat_row "V" (Time.statistics vstats iteration)
