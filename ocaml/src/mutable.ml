open Point

let bf_closest_pair' (ps : point array) (l : int) (h : int): point * point =
  let p0 = ref (Array.unsafe_get ps l) in
  let p1 = ref (Array.unsafe_get ps (l + 1)) in
  let delta = ref (dist !p0 !p1) in
  for i = l to h do
    let c0 = Array.unsafe_get ps i in
    for j = i + 1 to h do
      let c1 = Array.unsafe_get ps j in
      let d = dist c0 c1 in
      if d < !delta then (
          p0 := c0;
          p1 := c1;
          delta := d;
      )
    done;
  done;
  (!p0, !p1)

let bf_closest_pair (ps : point array): point * point =
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
  let i = ref l in
  let j = ref (m + 1) in
  for k = l to h do
    if !i > m then (
        Array.unsafe_set ps k (Array.unsafe_get aux !j);
        j := !j + 1
    ) else if !j > h then (
        Array.unsafe_set ps k (Array.unsafe_get aux !i);
        i := !i + 1
    ) else if snd (Array.unsafe_get aux !j) <= snd (Array.unsafe_get aux !i) then (
        Array.unsafe_set ps k (Array.unsafe_get aux !j);
        j := !j + 1
    ) else (
        Array.unsafe_set ps k (Array.unsafe_get aux !i);
        i := !i + 1
    )
  done

let rec closest_pair_rec (xs : point array) (ys : point array) (aux : point array) (l : int) (h : int): point * point =
  if (h - l <= 2) then (
      sort_by_y ys l h;
      bf_closest_pair' xs l h
  ) else (
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
        if abs_float (fst (Array.unsafe_get ys i) -. fst median) <= !delta then (
            Array.unsafe_set aux !k (Array.unsafe_get ys i);
            k := !k + 1
        )
      done;

      for i = 0 to !k - 1 do
        let j = ref (i + 1) in
        while !j < !k && snd (Array.unsafe_get aux !j) -. snd (Array.unsafe_get aux i) < !delta do
          let d = dist (Array.unsafe_get aux i) (Array.unsafe_get aux !j) in
          if d < !delta then (
              delta := d;
              p0 := Array.unsafe_get aux i;
              p1 := Array.unsafe_get aux !j
          );
          j := !j + 1
        done;
      done;

      (!p0, !p1)
  )

let closest_pair (ps : point array): point * point =
  let n = Array.length ps in
  sort_by_x ps 0 (n - 1);
  closest_pair_rec ps (Array.copy ps) (Array.init n (fun _ -> (0.0, 0.0))) 0 (n - 1)
