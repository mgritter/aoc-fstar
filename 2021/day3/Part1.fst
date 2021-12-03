module Part1

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

let majority (input:(list bool){((List.Tot.length input) % 2) = 1}) : 
   Tot (b:bool{number_of b input > (List.Tot.length input / 2)}) =
   let true_count = number_of true input in
     let false_count = number_of false input in
       true_and_false_partition_the_list input;
       (true_count > false_count)

let minority (input:(list bool){((List.Tot.length input) % 2) = 1}) : 
   Tot (b:bool{number_of b input <= (List.Tot.length input / 2)}) =
   let true_count = number_of true input in
     let false_count = number_of false input in
       true_and_false_partition_the_list input;
       (true_count < false_count)

let ith_element (i:nat{i<12}) (d:diagnostic) : bool =
  List.Tot.index (bv2list d) i

// Failed to resolve implicit argument ?328 of type pos introduced for flex-flex quasi:	lhs=Instantiating implicit argument in application	rhs=Instantiating implicit argument in application

let rec nat_range_helper (start:nat) (nd:nat{start<nd}) 
    (curr:nat{start <= curr && curr < nd}) 
    (l:list (z:nat{start <= z && z < nd}))
: Tot (list (z:nat{start <= z && z < nd})) (decreases (curr-start)) =
  if curr = start then curr :: l
  else nat_range_helper start nd (curr-1) (curr :: l)

let nat_range_lemma_0 (start:nat) (nd:nat{start<nd}) (l:list (z:nat{start <= z && z < nd}))
  : Lemma( nat_range_helper start nd start l = start :: l ) =
  ()

let nat_range_lemma_1 (start:nat) (nd:nat{start<nd}) 
  (c:nat{start < c && c < nd}) (l:list (z:nat{start <= z && z < nd})) 
  : Lemma( nat_range_helper start nd c l = nat_range_helper start nd (c-1) ( c :: l ) ) =
  ()

let rec nat_range_helper_len (start:nat) (nd:nat{start<nd}) 
   (curr:nat{start <= curr && curr < nd}) 
   (l:list (z:nat{start <= z && z < nd}))
  : Lemma (ensures (List.Tot.length (nat_range_helper start nd curr l) = (List.Tot.length l) + (1 + (curr - start))))
          (decreases (curr - start))
   = if curr = start then 
       nat_range_lemma_0 start nd l
     else (
       nat_range_helper_len start nd (curr-1) (curr::l);
       nat_range_lemma_1 start nd curr l
     )
     
let nat_range (start:nat) (nd:nat) : Tot (list (z:nat{start <= z && z < nd})) =
  if start >= nd then []
  else nat_range_helper start nd (nd-1) []
  
let nat_range_length (start:nat) (nd:nat) 
  : Lemma (requires start < nd)
          (ensures (List.Tot.length (nat_range start nd) = (nd - start)))
          [SMTPat (nat_range start nd)]
  =  nat_range_helper_len start nd (nd-1) []

let zero_to_eleven () : (l:(list (x:nat{0 <= x && x <12})){List.Tot.length l = 12}) =
  nat_range_length 0 12;
  nat_range 0 12

let gamma (l:(list diagnostic){(List.Tot.length l) % 2 = 1}) : int =
  bv2int #12 (list2bv (List.Tot.map 
            (fun i -> (majority (map (ith_element i) l)))
            (zero_to_eleven()) ))

let epsilon (l:(list diagnostic){(List.Tot.length l) % 2 = 1}) : int =
  bv2int #12 (list2bv (List.Tot.map 
            (fun i -> (minority (map (ith_element i) l)))
            (zero_to_eleven()) ))

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let ds = parse_input fd [int2bv #12 0] in
      if List.Tot.length ds % 2 <> 1 then
        print_string "bad input length\n"
      else
      let e = epsilon ds in
        let g = gamma ds in
          print_string (sprintf "%d\n" (op_Multiply e g ))

let _ = calc_part_1 "input.txt"

