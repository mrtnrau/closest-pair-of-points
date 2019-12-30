open Point

let time (f : unit -> 'a): float =
  let start = Sys.time()
  and _ = f () in
  Sys.time() -. start

let times (f : unit -> 'a) (n : int): int =
  let cnt = ref 0.0 in
  for _ = 1 to n do
    cnt := !cnt +. time f
  done;
  int_of_float (!cnt /. float_of_int n *. 1000.0)

let statistics (fs : (unit -> 'a) list) (n : int): int list =
  List.map(fun f -> times f n) fs

let print_header (header : int list) (out : out_channel): unit =
  Printf.fprintf out "  \t";
  List.iter (fun n -> Printf.fprintf out "%d\t\t" n) header;
  Printf.fprintf out "\n"

let print_stat_row (label : string) (row : int list) (out : out_channel): unit =
  Printf.fprintf out "%s:\t" label;
  List.iter (fun stat -> Printf.fprintf out "%dms\t\t" stat) row;
  Printf.fprintf out "\n"

let rec init (from : int) (until : int) (by : int): int list =
  if until < from then
    []
  else
    from :: init (from + by) until by

let map (f : 'a -> 'b) (xs : 'a list): 'b list =
  let rec map_rec acc = function 
    | [] -> List.rev acc
    | x :: xs -> (map_rec[@tailcall]) (f x :: acc) xs
  in map_rec [] xs

let main () =
  let iteration = int_of_string  Sys.argv.(1) in
  let to_file   = bool_of_string Sys.argv.(2) in
  let from      = int_of_string  Sys.argv.(3) in
  let until     = int_of_string  Sys.argv.(4) in
  let by        = int_of_string  Sys.argv.(5) in

  let of_point ((x, y) : point) =
    (Verified.Int_of_integer x, Verified.Int_of_integer y) in

  let of_point_alt ((x, y) : point) =
    (Verified_alt.Int_of_integer x, Verified_alt.Int_of_integer y) in

  let ns = init from until by in
  let ps_array = map (fun n -> random_points n (n * n)) ns in
  (*List.iter (fun arr -> Array.iter (fun p -> Printf.printf "%s " (format_point p)) arr) ps_array; Printf.printf "\n";*)
  let ps_list  = map Array.to_list ps_array in
  let ps_verified = map (fun ps -> map of_point ps) ps_list in
  let ps_verified_alt = map (fun ps -> map of_point_alt ps) ps_list in

  let mstats = map (fun ps -> fun () -> Mutable.closest_pair ps) ps_array in
  let istats = map (fun ps -> fun () -> Immutable.closest_pair ps) ps_list in
  let vstats = map (fun ps -> fun () -> Verified.closest_pair_code ps) ps_verified in
  let wstats = map (fun ps -> fun () -> Verified_alt.closest_pair_code ps) ps_verified_alt in

  let oc = if to_file then open_out "out.txt" else stdout in
  print_header ns oc;
  print_stat_row "M" (statistics mstats iteration) oc;
  print_stat_row "I" (statistics istats iteration) oc;
  print_stat_row "V" (statistics vstats iteration) oc;
  print_stat_row "W" (statistics wstats iteration) oc;
  if to_file then close_out oc

let _ =
    let t = time main in
    Printf.printf "Total time: %ds\n" (int_of_float t)
