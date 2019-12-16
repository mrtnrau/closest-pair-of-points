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

let rec find_closest (p : point) (ps : point list): float * point =
  match ps with
  | [] -> raise (Invalid_argument "Not enough points.")
  | [p0] -> (dist p p0, p0)
  | p0 :: ps ->
    let (d1, p1) = find_closest p ps in
    let d0 = dist p p0 in
    if d0 < d1 then
      (d0, p0)
    else
      (d1, p1)

let rec closest_pair_bf (ps : point list): (float * point * point) =
  match ps with
  | [] -> raise (Invalid_argument "Not enough points.")
  | [_] -> raise (Invalid_argument "Not enough points.")
  | [p0; p1] -> (dist p0 p1, p0, p1)
  | p0 :: ps ->
    let (dc, c0, c1) = closest_pair_bf ps in
    let (dp, p1) = find_closest p0 ps in
    if dc <= dp then
      (dc, c0, c1)
    else
      (dp, p0, p1)

let rec find_closest_delta (p : point) (d : float) (ps : point list): float * point =
  match ps with
  | [] -> raise (Invalid_argument "Not enough points.")
  | [c] -> (dist p c, c)
  | c0 :: cs ->
    let d0 = dist p c0 in
    if d <= Z.sub (snd c0) (snd p) then
      (d0, c0)
    else
      let (d1, c1) = find_closest_delta p (min d d0) cs in
      if d0 <= d1 then
        (d0, c0)
      else
        (d1, c1)

let rec closest_pair_combine (d : float) (c0 : point) (c1 : point) (ps : point list): float * point * point =
  match ps with
  | [] -> (d, c0, c1)
  | [_] -> (d, c0, c1)
  | p0 :: ps ->
    let (d', p1) = find_closest_delta p0 d ps in
    if d <= d' then
      (closest_pair_combine[@tailcall]) d c0 c1 ps
    else
      (closest_pair_combine[@tailcall]) d' p0 p1 ps

let rec merge (f : point -> Z.t) (ps : point list) (ps0 : point list) (ps1 : point list): point list =
  match (ps0, ps1) with
  | (p0 :: ps0, p1 :: ps1) ->
    if Z.leq (f p0) (f p1) then
      (merge[@tailcall]) f (p0 :: ps) ps0 (p1 :: ps1)
    else
      (merge[@tailcall]) f (p1 :: ps) (p0 :: ps0) ps1
  | ([], p1 :: ps1) -> (merge[@tailcall]) f (p1 :: ps) [] ps1
  | (p0 :: ps0, []) -> (merge[@tailcall]) f (p0 :: ps) ps0 []
  | ([], []) -> List.rev ps

let merge (f : point -> Z.t) (ps0 : point list) (ps1 : point list): point list =
  merge f [] ps0 ps1

let rec msort (f : point -> float) (ps : point list): point list =
  let n = List.length ps in
  if n <= 1 then
    ps
  else
    let (l, r) = split_at (n / 2) ps in
    merge f (msort f l) (msort f r)

let rec closest_pair_rec (psX : point list): point list * (float * point * point) =
  let n = List.length psX in
  if n <= 3 then
    (msort snd psX, closest_pair_bf psX)
  else
    let (lx, rx) = split_at (n / 2) psX in
    let l = fst (List.hd rx) in

    let (ysL, (dl, lp0, lp1)) = closest_pair_rec lx in
    let (ysR, (dr, rp0, rp1)) = closest_pair_rec rx in
    let psY = merge snd ysL ysR in

    let (d, c0, c1) = if dl < dr then (dl, lp0, lp1) else (dr, rp0, rp1) in
    let ys = List.filter (fun p -> Z.leq (Z.abs (Z.sub (fst p) l)) (d) psY in
    (ys, closest_pair_combine d c0 c1 ys)

let closest_pair (ps : point list): point * point =
  let (_, (_, c0, c1)) = closest_pair_rec (msort fst ps) in (c0, c1)
