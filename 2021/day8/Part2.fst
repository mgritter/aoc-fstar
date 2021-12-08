module Part2

open FStar.IO
open FStar.All
open FStar.String
open FStar.Printf
open FStar.List.Tot
open FStar.BV
open FStar.Map

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
  String.concat " | "
  [
   (String.concat " " d.samples);
   (String.concat " " d.output)
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

(*
  0:      1:      2:      3:      4:
 aaaa    ....    aaaa    aaaa    ....
b    c  .    c  .    c  .    c  b    c
b    c  .    c  .    c  .    c  b    c
 ....    ....    dddd    dddd    dddd
e    f  .    f  e    .  .    f  .    f
e    f  .    f  e    .  .    f  .    f
 gggg    ....    gggg    gggg    ....

  5:      6:      7:      8:      9:
 aaaa    aaaa    aaaa    aaaa    aaaa
b    .  b    .  .    c  b    c  b    c
b    .  b    .  .    c  b    c  b    c
 dddd    dddd    ....    dddd    dddd
.    f  e    f  .    f  e    f  .    f
.    f  e    f  .    f  e    f  .    f
 gggg    gggg    ....    gggg    gggg

6 segments: 0 6 9
5 segments: 2 3 5

aaaa = in 7 but not 1
cc and ff = in 3 and 1 but not 2 and 5

1 intersect 3 = 3

bbbb or dddd = in 4 but not 1
bbbb and ddd = in 4 6 and 9 but not 0

(b or d) = 4 set difference 1
(b or d) is not a subset of 0


known : 1 4 7 8 0 3

9 union 1 = 9

known : 1 4 7 8 0 3 9 6 

2 vs 5 = 

2 union 4 = 8
2 union 5 is not

*)

type segments = bv_t 7

let contains_char (s:string) (c:char) : bool =
  String.index_of s c <> -1

let string_to_segments (s:string) : segments =
  list2bv (map (contains_char s) 
    ['a'; 'b'; 'c'; 'd'; 'e'; 'f'; 'g'])

type digit_map = Map.t (z:int{z<=9}) segments

let empty () : digit_map =
  Map.restrict Set.empty (Map.const (int2bv 0))

let initial_map (d:display) : digit_map =
  let s1 = tryFind (fun i -> strlen i = 2) d.samples in
  let s4 = tryFind (fun i -> strlen i = 4) d.samples in
  let s7 = tryFind (fun i -> strlen i = 3) d.samples in
  let s8 = tryFind (fun i -> strlen i = 7) d.samples in
    match (s1,s4,s7,s8) with 
    | (Some x1, Some x4, Some x7, Some x8) ->
      (Map.upd
       (Map.upd
        (Map.upd
          (Map.upd 
            (empty()) 
            1 (string_to_segments x1))
            4 (string_to_segments x4))
            7 (string_to_segments x7))
            8 (string_to_segments x8))
    | (_, _, _, _) -> empty()

let infer_3 (s235:(list segments){length s235 = 3}) (init:digit_map) : ML digit_map =
  let s1 = sel init 1 in
    let c1 = index s235 0 in
    let c2 = index s235 1 in
    let c3 = index s235 2 in
        if bvand s1 c1 = c1 then
           upd init 3 c1
        else if bvand s1 c2 = c2 then
           upd init 3 c2
        else if bvand s1 c3 = c3 then
           upd init 3 c3
        else
           failwith "bad inference"

let _ = assert_norm( 
  sel 
  (infer_3 [ string_to_segments "acdeg"; 
            string_to_segments "acdfg";
            string_to_segments "abdfg" ]
         (Map.upd (empty()) 
                1 (string_to_segments "fc")))
  3 = string_to_segments "acdfg")
  
let is_subset (a:segments) (b:segments) : bool =
  bvor a b = b

let infer_0 (s069:(list segments){length s069 = 3}) (init:digit_map) : ML digit_map =
  let s1 = sel init 1 in
  let s4 = sel init 4 in 
  let bd = bvxor s4 s1 in  
    let c1 = index s069 0 in
    let c2 = index s069 1 in
    let c3 = index s069 2 in
        if op_Negation (is_subset bd c1) then
           upd init 0 c1
        else if op_Negation (is_subset bd c2) then
           upd init 0 c2
        else if op_Negation (is_subset bd c3) then
           upd init 0 c3
        else
           failwith "bad inference"

let infer_0 (s069:(list segments){length s069 = 3}) (init:digit_map) : ML digit_map =
  let s0 = sel init 0 in
  let s1 = sel init 1 in 
  let s69 = filter (fun 
    let c1 = index s069 0 in
    let c2 = index s069 1 in
    let c3 = index s069 2 in
        if op_Negation (is_subset bd c1) then
           upd init 0 c1
        else if op_Negation (is_subset bd c2) then
           upd init 0 c2
        else if op_Negation (is_subset bd c3) then
           upd init 0 c3
        else
           failwith "bad inference"


let infer_map (d:display) (init:digit_map) : digit_map =
  let s069 = filter (fun i -> strlen i = 6) d.samples in
  let s235 = filter (fun i -> strlen i = 5) d.samples in  
  let m3 = infer_3 s235 init in
  let m0 = infer_0 s069 m3 in
  let m9 = infer_9 s069 m0 in

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let input = parse_input fd in
      let n = number_of_1478 input in
        print_string (sprintf "%d\n" n )

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"

  
  
