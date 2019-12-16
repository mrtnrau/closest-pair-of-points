type point = Z.t * Z.t

let dist ((x0, y0) : point) ((x1, y1) : point): float =
  let dx = Z.sub x0 x1
  and dy = Z.sub y0 y1 in
  sqrt (Z.to_float (Z.add (Z.mul dx dx) (Z.mul dy dy)))

let format_point ((x, y) : point): string =
  Printf.sprintf "(%s, %s)" (Z.to_string x) (Z.to_string y)

let random_point (): point =
  let x = Z.of_int64 (Random.int64 Int64.max_int)
  and y = Z.of_int64 (Random.int64 Int64.max_int)
  in (x, y)

let random_points (n : int): point array =
  Random.self_init ();
  let arr = Array.make n (Z.zero, Z.zero) in
  for i = 0 to n - 1 do
    Array.unsafe_set arr i (random_point ())
  done;
  arr
