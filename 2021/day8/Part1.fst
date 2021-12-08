module Part1

open FStar.IO
open FStar.All
open FStar.String
open FStar.Printf
open FStar.List.Tot
  
type display = {
  samples : (l:(list string){length l = 10});
  output: (l:(list string){length l = 4})
}

type parse_result =
 | OK : d:display -> parse_result
 | ParseError : s:string -> parse_result

// TODO: why didn't it alert us when secondPart was "firstPart" in the second strlen?
let parse_line (s:string) : parse_result =
  let x = String.split ['|'] s in
    if length x < 2 then
       ParseError "problem with |"
    else let firstPart = index x 0 in
    let secondPart = index x 1 in
    if strlen firstPart < 1 then
       ParseError "firstPart too short"
    else if strlen secondPart < 1 then
       ParseError "secondPart too short"
    else let firstInputs = (String.split [' '] (sub firstPart 0 (strlen firstPart - 1))) in
    let secondInputs = (String.split [' '] (sub secondPart 1 (strlen secondPart - 1))) in
    if length firstInputs = 10 && length secondInputs = 4 then
       OK ({ samples=firstInputs; output=secondInputs })
    else
       ParseError (sprintf "lengths are wrong %d %d" (length firstInputs) (length secondInputs) )

// TODO: print that this is the inverse of parsing
let display_to_string (d:display) : string =
  concat " | "
  [
   (concat " " d.samples);
   (concat " " d.output)
   ]

val count: #a:eqtype -> a -> list a -> Tot nat
let rec count #a x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + count x tl else count x tl

(* 

Using count:

File "out/Part1.ml", line 44, characters 13-72:
44 |       (((t + (FStar_List_Tot_Base.count (Prims.of_int (2)) segmentCount)) +
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This expression has type int but an expression was expected of type
         Z.t
make: *** [Makefile:12: Part1] Error 2
*)


// 1 has 2 segments
// 4 has 4 segments
// 7 has 3 segments
// 8 has 7 segments
let number_of_1478 (input:list display) : nat =
  let count_1748 (t:nat) (segmentCount:list nat) : nat =
     ( t + (count 2 segmentCount) + (count 4 segmentCount) + 
           (count 3 segmentCount) + (count 7 segmentCount) ) in
  let output_segments = map (fun d -> map strlen d.output) input in
  fold_left count_1748 0 output_segments

let rec parse_input (fd:fd_read) : ML (list display) =
   try
     let l = (read_line fd) in (
     match parse_line l with
     | ParseError e -> (
      print_string( e ^ "\n" );
      failwith "couldn't parse" 
      )
     | OK d -> (
        // print_string ( (display_to_string d) ^ "\n" );
        d :: (parse_input fd)
     )
     )
   with
   | EOF -> []
   | _ -> failwith "unknown error"

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let input = parse_input fd in
      let n = number_of_1478 input in
        print_string (sprintf "%d\n" n )

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"

  
  
