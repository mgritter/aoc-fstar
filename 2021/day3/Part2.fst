module Part2

open FStar.IO
open FStar.Printf
open FStar.List.Tot
open FStar.String
open FStar.BV
open FStar.All

type diagnostic = bv_t 12

let parse_bit (c:char) : Tot bool =
  match c with
  | '0' -> false
  | '1' -> true
  | _ -> false
    
let parse_diagnostic (s:string{length s = 12}) : Tot diagnostic =
  list2bv (map parse_bit (list_of_string s))

let rec parse_input (fd:fd_read) (prev: list diagnostic) : ML (list diagnostic) =
  try 
   let line = read_line fd in
     if strlen line <> 12 then
       failwith "Bad line"
     else
       parse_input fd ((parse_diagnostic line) :: prev)
   with
   | EOF -> prev
   | _ -> failwith "unknown error"

// (Error 236) When clauses are not yet supported in --verify mode; they will be some day

let rec number_of (#a:eqtype) (v:a) (l:list a) : Tot nat (decreases List.Tot.length l) =
  match l with 
  | hd :: tl  ->
     if hd = v then
        1 + (number_of v tl)
     else
        (number_of v tl)
  | [] -> 0

let rec true_and_false_partition_the_list (l:list bool) 
 : Lemma (ensures (number_of true l) + (number_of false l) = List.Tot.length l) =
 match l with
 | [] -> ()
 | hd :: tl -> true_and_false_partition_the_list tl

let majority (input:(list bool)) : 
   Tot (b:bool{number_of b input > (List.Tot.length input / 2) \/
               (b = true /\ number_of true input = (List.Tot.length input / 2))}) =
   let true_count = number_of true input in
     let false_count = number_of false input in
       true_and_false_partition_the_list input;
       (true_count >= false_count)

let _ = assert_norm( majority [false; false; true; true] = true )
let _ = assert_norm( majority [false; true; true] = true )

let minority (input:(list bool)) : 
   Tot (b:bool{number_of b input < ((List.Tot.length input + 1) / 2) \/
               (b = false /\ number_of false input = (List.Tot.length input / 2))}) =
   let true_count = number_of true input in
     let false_count = number_of false input in
       true_and_false_partition_the_list input;
       (true_count < false_count)

let _ = assert_norm( minority [false; false; true; true] = false )
let _ = assert_norm( minority [false; false; false; true] = true  )
let _ = assert_norm( minority [false; true; true] = false )

let ith_element (i:nat{i<12}) (d:diagnostic) : bool =
  List.Tot.index (bv2list d) i

let filter_majority_by_position (i:nat{i<12}) (l:list diagnostic) : (list diagnostic) =
  let bit = majority (map (ith_element i) l) in
    List.Tot.filter (fun d -> ith_element i d = bit ) l

let filter_minority_by_position (i:nat{i<12}) (l:list diagnostic) : (list diagnostic) =
  let bit = minority (map (ith_element i) l) in
    List.Tot.filter (fun d -> ith_element i d = bit ) l

let rec o2 (n:nat) (l:list diagnostic) : ML (option int) (decreases (12 - n)) =
  if List.Tot.length l = 1 then
     Some (bv2int #12 (hd l))
  else if n >= 12 then
     None
  else
     o2 (n+1) (filter_majority_by_position n l)

let rec co2 (n:nat) (l:list diagnostic) : Tot (option int) (decreases (12 - n)) =
  if List.Tot.length l = 1 then
     Some (bv2int #12 (hd l))
  else if n >= 12 then
     None
  else
     co2 (n+1) (filter_minority_by_position n l)

let calc_part_2 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let ds = parse_input fd [] in
      let s1 = o2 0 ds in
        match s1 with
        | None ->
           print_string "bad o2\n"
        | Some v1 ->  
          let s2 = co2 0 ds in
            match s2 with
            | None ->
              print_string "bad co2\n"
            | Some v2 ->
              print_string (sprintf "%d\n" (op_Multiply v1 v2 ))

let _ = calc_part_2 "input.txt"
// let _ = calc_part_2 "example.txt"
