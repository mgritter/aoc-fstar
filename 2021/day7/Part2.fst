module Part2

open FStar.IO
open FStar.Printf
open FStar.All
open FStar.String
open FStar.Int32
open FStar.List.Tot

let int32_to_int (n:Int32.t) : int =
  Int32.v n

let parse_comma_separated_numbers (s:string) : Tot (list int) =
  FStar.List.Tot.map (fun x -> (int32_to_int (Int32.of_string x))) (FStar.String.split [','] s)  

// 1 + 2 + 3 + 4 + ... + N = (n+1)*n/2
let cost_func (steps:nat) : nat =
  (op_Multiply (steps + 1) steps) / 2

let rec summed_distance_to (l:list int) (meeting:int) : Tot nat =
  match l with
  | [] -> 0 
  | hd :: tl -> (cost_func (abs (hd - meeting))) + summed_distance_to tl meeting

let max_search = 1935

let rec min_cost (search_value:nat) (l:list int) : nat =
  let v = summed_distance_to l search_value in
    if search_value = 0 then v
    else min v (min_cost (search_value - 1) l)

let calc_part_2 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let crabs = parse_comma_separated_numbers (read_line fd) in
      if length crabs = 0  then
        print_string "bad input"
      else
        let soln = min_cost max_search crabs in
          print_string (sprintf "min distance is %d\n" soln)

let _ = calc_part_2 "example.txt"
let _ = calc_part_2 "input.txt"
