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

let rec find_closest_bf (p : point) (ps : point list): Z.t * point =
  match ps with
  | [] -> raise (Invalid_argument "Not enough points.")
  | [p0] -> (dist p p0, p0)
  | p0 :: ps ->
    let (d1, p1) = find_closest_bf p ps in
    let d0 = dist p p0 in
    if Z.lt d0 d1 then
      (d0, p0)
    else
      (d1, p1)

let rec closest_pair_bf (ps : point list): (Z.t * point * point) =
  match ps with
  | [] -> raise (Invalid_argument "Not enough points.")
  | [_] -> raise (Invalid_argument "Not enough points.")
  | [p0; p1] -> (dist p0 p1, p0, p1)
  | p0 :: ps ->
    let (dc, c0, c1) = closest_pair_bf ps in
    let (dp, p1) = find_closest_bf p0 ps in
    if Z.leq dc dp then
      (dc, c0, c1)
    else
      (dp, p0, p1)

let rec find_closest (p : point) (d : Z.t) (ps : point list): Z.t * point =
  match ps with
  | [] -> raise (Invalid_argument "Not enough points.")
  | [c] -> (dist p c, c)
  | c0 :: cs ->
    let d0 = dist p c0 in
    if Z.leq d (Z.pow (Z.sub (snd c0) (snd p)) 2) then
      (d0, c0)
    else
      let (d1, c1) = find_closest p (Z.min d d0) cs in
      if Z.leq d0 d1 then
        (d0, c0)
      else
        (d1, c1)

let rec find_closest_pair (d : Z.t) (c0 : point) (c1 : point) (ps : point list): Z.t * point * point =
  match ps with
  | [] -> (d, c0, c1)
  | [_] -> (d, c0, c1)
  | p0 :: ps ->
    let (d', p1) = find_closest p0 d ps in
    if Z.leq d d' then
      (find_closest_pair[@tailcall]) d c0 c1 ps
    else
      (find_closest_pair[@tailcall]) d' p0 p1 ps

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

let rec msort (f : point -> Z.t) (ps : point list): point list =
  let n = List.length ps in
  if n <= 1 then
    ps
  else
    let (l, r) = split_at (n / 2) ps in
    merge f (msort f l) (msort f r)

let rec closest_pair_rec (psX : point list): point list * (Z.t * point * point) =
  let n = List.length psX in
  if n <= 3 then
    (msort snd psX, closest_pair_bf psX)
  else
    let (lx, rx) = split_at (n / 2) psX in
    let l = fst (List.hd rx) in

    let (ysL, (dl, lp0, lp1)) = closest_pair_rec lx in
    let (ysR, (dr, rp0, rp1)) = closest_pair_rec rx in
    let psY = merge snd ysL ysR in

    let (d, c0, c1) = if Z.lt dl dr then (dl, lp0, lp1) else (dr, rp0, rp1) in
    let ys = List.filter (fun p -> Z.lt (Z.pow (Z.sub (fst p) l) 2) d) psY in
    (ys, find_closest_pair d c0 c1 ys)

let closest_pair (ps : point list): point * point =
  let (_, (_, c0, c1)) = closest_pair_rec (msort fst ps) in (c0, c1)
