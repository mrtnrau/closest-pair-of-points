type point = float * float

let dist ((x0, y0) : point) ((x1, y1) : point): float =
  let dx = x0 -. x1
  and dy = y0 -. y1 in
  sqrt (dx *. dx +. dy *. dy)

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