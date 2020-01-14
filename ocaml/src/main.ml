open Point

let time (f : unit -> 'a): float =
  let start = Sys.time()
  and _ = f () in
  Sys.time() -. start

let stats (f : unit -> 'a) (n : int): int =
  let cnt = ref 0.0 in
  for _ = 1 to n do
    cnt := !cnt +. time f
  done;
  int_of_float (!cnt /. float_of_int n *. 1000.0)

let display (label : string) (n : int) (time : int): unit =
  Printf.printf "%s\t%d\t%dms\n" label n time

let map (f : 'a -> 'b) (xs : 'a list): 'b list =
  let rec map_rec acc = function 
    | [] -> List.rev acc
    | x :: xs -> (map_rec[@tailcall]) (f x :: acc) xs
  in map_rec [] xs

let of_point ((x, y) : point) =
  (Isabelle.Int_of_integer x, Isabelle.Int_of_integer y)

let main () =
  let algorithm =                Sys.argv.(1) in
  let n         = int_of_string  Sys.argv.(2) in
  let iteration = int_of_string  Sys.argv.(3) in

  let ps_array    = random_points n (n * n) in
  let ps_list     = Array.to_list ps_array  in
  let ps_verified = map of_point ps_list    in

  match algorithm with
    "Brute"     -> display algorithm n (stats (fun () -> Cormen.bf_closest_pair      ps_array   ) iteration) 
  | "Sedgewick" -> display algorithm n (stats (fun () -> Sedgewick.closest_pair      ps_array   ) iteration) 
  | "Jiang"     -> display algorithm n (stats (fun () -> Jiang.closest_pair          ps_array   ) iteration) 
  | "Cormen"    -> display algorithm n (stats (fun () -> Cormen.closest_pair         ps_array   ) iteration) 
  | "Ocaml"     -> display algorithm n (stats (fun () -> Ocaml.closest_pair          ps_list    ) iteration) 
  | "Isabelle"  -> display algorithm n (stats (fun () -> Isabelle.closest_pair_code  ps_verified) iteration)

let _ =
    let t = time main in
    Printf.printf "Total time: %ds\n" (int_of_float t)
