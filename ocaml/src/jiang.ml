open Point

(* Implementation based on Jiang and Gillespie Basic-2 algorithm *)

let bf_closest_pair' (ps : point array) (l : int) (h : int): Z.t * point * point =
  let p0 = ref (Array.unsafe_get ps l) in
  let p1 = ref (Array.unsafe_get ps (l + 1)) in
  let delta = ref (dist !p0 !p1) in
  for i = l to h do
    let c0 = Array.unsafe_get ps i in
    for j = i + 1 to h do
      let c1 = Array.unsafe_get ps j in
      let d = dist c0 c1 in
      if Z.lt d !delta then (
          p0 := c0;
          p1 := c1;
          delta := d;
      )
    done;
  done;
  (!delta, !p0, !p1)

let bf_closest_pair (ps : point array): Z.t * point * point =
  bf_closest_pair' ps 0 (Array.length ps - 1)

let sort_by_y (ps : point array) (l : int) (h : int): unit =
  let arr = Array.sub ps l (h - l + 1) in
  Array.stable_sort (fun (_, y0) (_, y1) -> Z.compare y0 y1) arr;
  Array.blit arr 0 ps l (h - l + 1)

let sort_by_x (ps : point array) (l : int) (h : int): unit =
  let arr = Array.sub ps l (h - l + 1) in
  Array.stable_sort (fun (x0, _) (x1, _) -> Z.compare x0 x1) arr;
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
    ) else if Z.leq (snd (Array.unsafe_get aux !j)) (snd (Array.unsafe_get aux !i)) then (
        Array.unsafe_set ps k (Array.unsafe_get aux !j);
        j := !j + 1
    ) else (
        Array.unsafe_set ps k (Array.unsafe_get aux !i);
        i := !i + 1
    )
  done

let rec closest_pair_rec (xs : point array) (ys : point array) (aux : point array) (l : int) (h : int): Z.t * point * point =
  if (h - l <= 2) then (
      sort_by_y ys l h;
      bf_closest_pair' xs l h
  ) else (
      let m = l + (h - l) / 2 in
      let median = Array.unsafe_get xs m in
      let (ld, lp0, lp1) = closest_pair_rec xs ys aux l m in
      let (rd, rp0, rp1) = closest_pair_rec xs ys aux (m + 1) h in
      let (d', p0', p1') = if Z.leq ld rd then (ld, lp0, lp1) else (rd, rp0, rp1) in
      let p0 = ref p0' in
      let p1 = ref p1' in
      let d = ref d' in

      let ml = ref l in
      for i = l to m do
        let p = Array.unsafe_get ys i in
        if Z.lt (Z.pow (Z.sub (fst p) (fst median)) 2) !d then (
          Array.unsafe_set aux !ml p;
          ml := !ml + 1
        ) 
      done;

      let mr = ref (m + 1) in
      for i = m + 1 to h do
        let p = Array.unsafe_get ys i in
        if Z.lt (Z.pow (Z.sub (fst p) (fst median)) 2) !d then (
          Array.unsafe_set aux !mr p;
          mr := !mr + 1
        ) 
      done;

      let i = ref l in
      let j = ref (m + 1) in
      while !i < !ml && !j < !mr do
        let pl = Array.unsafe_get aux !i in
        let pr = Array.unsafe_get aux !j in
        if Z.lt (snd pl) (snd pr) then (
          if Z.lt (Z.pow (Z.sub (snd pr) (snd pl)) 2) !d then (
            let d' = dist pl pr in
            if Z.lt d' !d then (
              d := d';
              p0 := pl;
              p1 := pr
            );
            if !j + 1 < !mr then (
              let pr2 = Array.unsafe_get aux (!j + 1) in
              if Z.lt (Z.pow (Z.sub (snd pr2) (snd pl)) 2) !d then (
                let d' = dist pl pr2 in
                if Z.lt d' !d then (
                  d := d';
                  p0 := pl;
                  p1 := pr2
                )
              )
            )
          );
          i := !i + 1
        ) else (
          if Z.lt (Z.pow (Z.sub (snd pl) (snd pr)) 2) !d then (
            let d' = dist pl pr in
            if Z.lt d' !d then (
              d := d';
              p0 := pl;
              p1 := pr
            );
            if !i + 1 < !ml then (
              let pl2 = Array.unsafe_get aux (!i + 1) in
              if Z.lt (Z.pow (Z.sub (snd pl2) (snd pr)) 2) !d then (
                let d' = dist pl2 pr in
                if Z.lt d' !d then (
                  d := d';
                  p0 := pl2;
                  p1 := pr
                )
              )
            )
          );
          j := !j + 1
        )
      done;
        
      merge ys aux l m h;

      (!d, !p0, !p1)
  )

let closest_pair (ps : point array): point * point =
  let n = Array.length ps in
  sort_by_x ps 0 (n - 1);
  let (_, p0, p1) = closest_pair_rec ps (Array.copy ps) (Array.init n (fun _ -> (Z.zero, Z.zero))) 0 (n - 1) in (p0, p1)
