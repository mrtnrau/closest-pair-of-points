type point = Z.t * Z.t

let dist ((x0, y0) : point) ((x1, y1) : point): Z.t =
  let dx = Z.sub x0 x1
  and dy = Z.sub y0 y1 in
  Z.add (Z.pow dx 2) (Z.pow dy 2)

let format_point ((x, y) : point): string =
  Printf.sprintf "(%s, %s)" (Z.to_string x) (Z.to_string y)

let random_point (b : int): point =
  let x = Z.of_int64 (Random.int64 (Int64.of_int b))
  and y = Z.of_int64 (Random.int64 (Int64.of_int b))
  in (x, y)

let random_points (n : int) (b : int): point array =
  Random.self_init ();
  let arr = Array.make n (Z.zero, Z.zero) in
  for i = 0 to n - 1 do
    Array.unsafe_set arr i (random_point b)
  done;
  arr
