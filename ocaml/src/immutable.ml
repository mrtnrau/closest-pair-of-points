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

let rec find_closest (p : point) (c0: point) (ps: point list): point =
  match ps with
  | [] -> c0
  | c1 :: ps ->
    if dist p c0 <= dist p c1 then
      (find_closest[@tailcall]) p c0 ps
    else
      (find_closest[@tailcall]) p c1 ps

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
    if List.length ys < 2 then
      (psY, (p0, p1))
    else
      let (c0, c1) = bf_closest_pair_7 ys in
      if dist p0 p1 <= dist c0 c1 then
        (psY, (p0, p1))
      else
        (psY, (c0, c1))

let closest_pair ps =
  snd (closest_pair_rec (msort fst ps))