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

let main () =
  let iteration = int_of_string  Sys.argv.(1) in
  let to_file   = bool_of_string Sys.argv.(2) in
  let from      = int_of_string  Sys.argv.(3) in
  let until     = int_of_string  Sys.argv.(4) in
  let by        = int_of_string  Sys.argv.(5) in

  let ns = init from until by in
  let ps = List.map random_points ns in

  let mstats = List.map (fun ps -> fun () -> Mutable.closest_pair ps) ps in
  let istats = List.map (fun ps -> fun () -> Immutable.closest_pair ps) (List.map Array.to_list ps) in
  let vstats = List.map (fun ps -> fun () -> Verified.closest_pair ps) (List.map Array.to_list ps) in

  let oc = if to_file then open_out "out.txt" else stdout in
  print_header ns oc;
  print_stat_row "M" (statistics mstats iteration) oc;
  print_stat_row "I" (statistics istats iteration) oc;
  print_stat_row "V" (statistics vstats iteration) oc;
  if to_file then close_out oc

let _ =
    let t = time main in
    Printf.printf "Total time: %ds" (int_of_float t)
