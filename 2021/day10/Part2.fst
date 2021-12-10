module Part2

open FStar.IO
open FStar.All
open FStar.String
open FStar.Printf
open FStar.List.Tot
  
// [] {} <> ()
type parse_stack =
 | Empty : parse_stack
 | Square : prev:parse_stack -> parse_stack
 | Curly : prev:parse_stack -> parse_stack
 | Angle : prev:parse_stack -> parse_stack
 | Paren : prev:parse_stack -> parse_stack

// type legal_char = (c:char{c='[' /\ c=']' /\ ... })

// Returns the first character that doesn't match the matching open
let rec parse_line (input:list char) (stack:parse_stack) : (option parse_stack) =
  match input with 
  | [] -> Some stack
  | c :: rest ->
    match c with
    | '[' -> parse_line rest (Square stack)     
    | ']' -> if Square? stack then parse_line rest (Square?.prev stack) 
       else None
    | '(' -> parse_line rest (Paren stack)     
    | ')' -> if Paren? stack then parse_line rest (Paren?.prev stack) 
       else None
    | '<' -> parse_line rest (Angle stack)     
    | '>' -> if Angle? stack then parse_line rest (Angle?.prev stack) 
       else None
    | '{' -> parse_line rest (Curly stack)     
    | '}' -> if Curly? stack then parse_line rest (Curly?.prev stack) 
       else None
    | c -> None

(*
): 1 point.
]: 2 points.
}: 3 points.
>: 4 points.
*)

let rec score (incomplete:parse_stack) (prev:nat): (n:nat{n>=prev}) =
 match incomplete with
 | Empty -> prev
 | Paren s -> score s (1 + (op_Multiply prev 5))
 | Square s -> score s (2 + (op_Multiply prev 5))
 | Curly s -> score s (3 + (op_Multiply prev 5))
 | Angle s -> score s (4 + (op_Multiply prev 5))

let rec parse_input (fd:fd_read) : ML (list int) =
   try
     let l = (read_line fd) in 
       match parse_line (list_of_string l) Empty with
       | None -> parse_input fd
       | Some s -> (score s 0) :: (parse_input fd)
   with
   | EOF -> []
   | _ -> failwith "unknown error"

let rec sort_maintains_length #a (f:(a -> a -> Tot int)) (l:list a) 
 : Lemma (ensures (length l = length (sortWith f l))) 
         (decreases (length l)) =
  match l with
  | [] -> ()
  | pivot::tl ->
     let hi, lo = partition (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     sort_maintains_length f lo;
     sort_maintains_length f hi;
     append_length (sortWith f lo) (pivot::sortWith f hi)

let median (l:(list int){length l > 0}) : Tot int =
  let sorted = List.Tot.sortWith (fun x y -> x - y) l in
    let middle = (length sorted) / 2 in
       sort_maintains_length (fun x y -> x - y) l;
       index sorted middle

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let s = parse_input fd in
      if length s = 0 then
        print_string "No mismatches?!?\n"
      else
        print_string (sprintf "%d\n" (median s) )

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"
