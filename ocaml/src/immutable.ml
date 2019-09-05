open Point

let rec split_at (n : int) (acc : 'a list) (xs : 'a list): 'a list * 'a list =
  match xs with
  | [] -> (List.rev acc, xs)
  | x :: xs ->
    if n <= 0 then
      (List.rev acc, x :: xs)
    else
      (split_at (n - 1)[@tailcall]) (x :: acc) xs

let split_at (n : int) (xs : 'a list): 'a list * 'a list =
  split_at n [] xs

let rec find_closest (p : point) (c0 : point) (ps : point list): point =
  match ps with
  | [] -> c0
  | c1 :: ps ->
    if dist p c0 <= dist p c1 then
      (find_closest[@tailcall]) p c0 ps
    else
      (find_closest[@tailcall]) p c1 ps

let rec bf_closest_pair_rec (c0 : point) (c1 : point) (ps : point list): point * point =
  match ps with
  | p0 :: p2 :: ps ->
    let p1 = find_closest p0 p2 ps in
    if dist c0 c1 <= dist p0 p1 then
      (bf_closest_pair_rec[@tailcall]) c0 c1 (p2 :: ps)
    else
      (bf_closest_pair_rec[@tailcall]) p0 p1 (p2 :: ps)
  | _ -> (c0, c1)

let bf_closest_pair (ps : point list): point * point =
  match ps with
  | p0 :: p1 :: ps -> bf_closest_pair_rec p0 p1 (p0 :: p1 :: ps)
  | _ -> raise (Invalid_argument "Not enough points")

let rec find_closest_delta (p : point) (delta : float) (c0 : point) (ps : point list): float * point =
    match ps with
    | [] -> (delta, c0)
    | c1 :: ps ->
      if delta <= snd c1 -. snd p then
        (delta, c0)
      else
        let delta' = dist p c1 in
        if delta <= delta' then
          (find_closest_delta[@tailcall]) p delta c0 ps
        else
          (find_closest_delta[@tailcall]) p delta' c1 ps

let rec closest_pair_combine_rec (delta : float) (c0 : point) (c1 : point) (ps : point list): point * point =
  match ps with
  | p0 :: p2 :: ps ->
    let (delta', p1) = find_closest_delta p0 delta p2 ps in
    if dist c0 c1 <= dist p0 p1 then
      (closest_pair_combine_rec[@tailcall]) delta c0 c1 (p2 :: ps)
    else
      (closest_pair_combine_rec[@tailcall]) delta' p0 p1 (p2 :: ps)
  | _ -> (c0, c1)

let closest_pair_combine (delta : float) (ps : point list): point * point =
  match ps with
  | p0 :: p1 :: ps -> closest_pair_combine_rec delta p0 p1 (p0 :: p1 :: ps)
  | _ -> raise (Invalid_argument "Not enough points")

(* Alternative 1 *)

(* let rec closest_pair_combine_rec' (c0 : point) (c1 : point) (ps : point list): point * point =
  match ps with
  | p0 :: p2 :: ps ->
    let p1 = find_closest p0 p2 (fst (split_at 7 ps)) in
    if dist c0 c1 <= dist p0 p1 then
      (closest_pair_combine_rec'[@tailcall]) c0 c1 (p2 :: ps)
    else
      (closest_pair_combine_rec'[@tailcall]) p0 p1 (p2 :: ps)
  | _ -> (c0, c1)

let closest_pair_combine' (ps : point list): point * point =
  match ps with
  | p0 :: p1 :: ps -> closest_pair_combine_rec' p0 p1 (p0 :: p1 :: ps)
  | _ -> raise (Invalid_argument "Not enough points") *)

(* Alternative 2 *)

(* let rec find_closest' (delta : float) (c0 : point) (c1 : point) (p : point) (cs : point list): float * point * point =
  match cs with
  | [] -> (delta, c0, c1)
  | c :: cs ->
    if snd p +. delta <= snd c -. snd p then
      (delta, c0, c1)
    else
      let delta' = dist p c in
      if delta <= delta' then
        (delta, c0, c1)
      else
        (find_closest'[@tailcall]) delta' p c p cs

let rec closest_pair_combine'' (delta : float) (c0 : point) (c1 : point) (ps : point list) (cs : point list): float * point * point =
  match (ps, cs) with
  | (p :: ps, c :: cs) ->
    if snd c < snd p then
      (closest_pair_combine''[@tailcall]) delta c0 c1 (p :: ps) cs
    else
      let (delta', c0', c1') = find_closest' delta c0 c1 p (c :: cs) in
      (closest_pair_combine''[@tailcall]) delta' c0' c1' ps (c :: cs)
  | _ -> (delta, c0, c1) *)

let rec merge (f : point -> float) (ps : point list) (ps0 : point list) (ps1 : point list): point list =
  match (ps0, ps1) with
  | (p0 :: ps0, p1 :: ps1) ->
    if f p0 <= f p1 then
      (merge[@tailcall]) f (p0 :: ps) ps0 (p1 :: ps1)
    else
      (merge[@tailcall]) f (p1 :: ps) (p0 :: ps0) ps1
  | ([], p1 :: ps1) -> (merge[@tailcall]) f (p1 :: ps) [] ps1
  | (p0 :: ps0, []) -> (merge[@tailcall]) f (p0 :: ps) ps0 []
  | ([], []) -> List.rev ps

let merge (f : point -> float) (ps0 : point list) (ps1 : point list): point list =
  merge f [] ps0 ps1

let rec msort (f : point -> float) (ps : point list): point list =
  let n = List.length ps in
  if n <= 1 then
    ps
  else
    let (l, r) = split_at (n / 2) ps in
    merge f (msort f l) (msort f r)

let rec closest_pair_rec (psX : point list): point list * (point * point) =
  let n = List.length psX in
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
    let ys = List.filter (fun p -> l -. delta <= fst p && fst p <= l +. delta) psY in

    (* let ysLF = List.filter (fun p -> l -. delta <= fst p && fst p <= l +. delta) ysL in
    let ysRF = List.filter (fun p -> l -. delta <= fst p && fst p <= l +. delta) ysR in
    let (delta', c0, c1) = closest_pair_combine'' delta p0 p1 ysLF ysRF in
    let (_, c0', c1') = closest_pair_combine'' delta' c0 c1 ysRF ysLF in
    (merge snd ysL ysR, (c0', c1')) *)

    if List.length ys < 2 then
      (psY, (p0, p1))
    else
      let (c0, c1) = closest_pair_combine delta ys in
      if dist p0 p1 <= dist c0 c1 then
        (psY, (p0, p1))
      else
        (psY, (c0, c1))

let closest_pair (ps : point list): point * point =
  snd (closest_pair_rec (msort fst ps))
