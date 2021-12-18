module Part1

open FStar.String
open FStar.IO
open FStar.All
open FStar.Printf
open FStar.List.Tot
  
type number =
  | Literal : (n:nat) -> number
  | Pair : (left:number) -> (right:number) -> number

noeq type parse_result : a:Type -> ctx:(list char) -> Type =
  | OK : #a:Type -> #ctx:(list char) -> value:a -> (rest:(list char){length rest < length ctx}) -> parse_result a ctx
  | Error : #a:Type -> #ctx:(list char) -> what:string -> parse_result a ctx

// Sublist of a list starting at i and taking n elements
let rec sublist #a (i:nat) (n:nat) (l:(list a){length l >= i+n}) : (x:(list a){length x = n}) =
  if n = 0 then []
  else if i > 0 then match l with
  | hd :: tl -> (sublist (i-1) n tl)
  else match l with
  | hd :: tl -> hd :: (sublist 0 (n-1) tl)

let suffix #a (skip:nat{skip > 0}) (l:(list a){length l >= skip}) : (x:(list a){length x < length l}) =
  sublist skip (length l - skip) l

let rec parse_number (input:list char) : 
  Tot (parse_result number input) 
      (decreases %[length input;1]) =
  if length input = 0 then
    Error "end of input reached"
  else match (index input 0) with
    | '[' -> parse_pair input
    | '0' -> OK (Literal 0) (suffix 1 input)
    | '1' -> OK (Literal 1) (suffix 1 input)
    | '2' -> OK (Literal 2) (suffix 1 input)
    | '3' -> OK (Literal 3) (suffix 1 input)
    | '4' -> OK (Literal 4) (suffix 1 input)
    | '5' -> OK (Literal 5) (suffix 1 input)
    | '6' -> OK (Literal 6) (suffix 1 input)
    | '7' -> OK (Literal 7) (suffix 1 input)
    | '8' -> OK (Literal 8) (suffix 1 input)
    | '9' -> OK (Literal 9) (suffix 1 input)
    | c -> Error ("unexpected character " ^ (string_of_list [c] ))
and parse_pair (input:(list char){length input > 0}) :
 Tot (parse_result number input) 
      (decreases %[length input;0]) =
   match parse_number (suffix 1 input) with
     | Error e -> Error e
     | OK v1 rest1 -> 
        if length rest1 < 2 then
          Error "expected comma, but less than 2 characters"
        else if index rest1 0 <> ',' then
          Error ("expected comma, got " ^ (string_of_list [index rest1 0]))
        else match parse_number (suffix 1 rest1) with
          | Error e -> Error e
          | OK v2 rest2 ->
            if length rest2 < 1 then
              Error "expected close bracket, but less than 1 character"
            else if index rest2 0 <> ']' then
              Error ("expected close bracket, got " ^ (string_of_list [index rest2 0]))
            else
              OK (Pair v1 v2) (suffix 1 rest2)
              
let rec unparse_number (n:number) : (list char) =
  match n with
  | Literal v -> (list_of_string ( sprintf "%d" v))
  | Pair l r -> ['['] @ (unparse_number l) @ [','] @ (unparse_number r) @ [']']

let print_number (n:number) : ML unit = 
  print_string (string_of_list (unparse_number n))

let add_numbers (a:number) (b:number) : number =
  Pair a b

type explode_result =
  | NotFound  // no explosion
  | Finished  : (n:number) -> explode_result // finished handling the explosion
  | LeftRight : (left:nat) -> (right:nat) -> explode_result
  // add left to the literal immediately left of the result
  | Left : (left:nat) -> (n:number) -> explode_result  
  // add right to the literal immediately right of the result
  | Right : (n:number) -> (right:nat) -> explode_result

let rec add_to_leftmost (x:number) (to_add:nat) : number =
  // descent to the leftmost literal in the tree and add the number to it
  // if no leftmost, just drop it
  match x with
  | Literal a -> Literal (a+to_add)
  | Pair a b -> Pair (add_to_leftmost a to_add) b

let rec add_to_rightmost (x:number) (to_add:nat) : number =
  match x with
  | Literal a -> Literal (a+to_add)
  | Pair a b -> Pair a (add_to_rightmost b to_add)
  
let rec explode_number (x:number) (depth:nat) : (r:explode_result{LeftRight? r ==> depth >= 4}) =
  match x with
  | Literal _ -> NotFound
  | (Pair (Literal a) (Literal b)) ->
      if depth >= 4 then
        LeftRight a b
      else
        NotFound
  | Pair a b -> ( match explode_number a (depth+1) with
    | Finished n -> Finished (Pair n b)
    | LeftRight l r -> 
      // x = [[l,r],b]
         Left l (Pair (Literal 0) (add_to_leftmost b r))
         // result = [0,(b+r)] and l still has to be added
    | Left l n -> 
           //      x
           //     / \
           //    a   b
           // l..n  
           //  
      Left l (Pair n b)
    | Right n r ->
           //      x
           //     / \
           //    a   b
           //    n..r  
      Finished (Pair n (add_to_leftmost b r))          
    | NotFound -> ( match explode_number b (depth+1) with
      | NotFound -> NotFound
      | Finished n -> Finished (Pair a n)
      | Left l n -> 
            //      x
            //     / \
            //    a   b
            //     l..n  
        Finished (Pair (add_to_rightmost a l) n)
      | Right n r ->
            //      x
            //     / \
            //    a   b
            //        n..r
        Right (Pair a n) r
      | LeftRight l r ->
            //      x
            //     / \
            //    a   b
            //     l..0..r
        Right (Pair (add_to_rightmost a l) (Literal 0)) r
      )
   )

let print_explode (r:explode_result) : ML unit = 
  match r with 
  | NotFound -> print_string "No explosion\n"
  | Finished n -> print_string "Finished\n"; print_number n; print_string "\n"
  | LeftRight l r -> print_string (sprintf "LeftRight %d %d\n" l r)
  | Left l n -> print_string (sprintf "Left %d\n" l); print_number n; print_string "\n"
  | Right n r  -> print_string (sprintf "Right %d\n" r); print_number n; print_string "\n"

let example0 = Pair (Literal 9) (Literal 8)
let _ = assert_norm( explode_number example0 0 = NotFound)

let example1 = Pair (Pair (Pair (Pair (Pair (Literal 9) (Literal 8)) (Literal 1)) (Literal 2)) (Literal 3)) (Literal 4)
let _ = assert_norm( explode_number example1 0 =
                     Left 9 (Pair (Pair (Pair (Pair (Literal 0) (Literal 9)) (Literal 2)) (Literal 3)) (Literal 4) ))

let example2 = "[[6,[5,[4,[3,2]]]],1]"
let example3 = "[[3,[2,[1,[7,3]]]],[6,[5,[4,[3,2]]]]]"
let example4 = "[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]"

let check_example (s:string) : ML unit = 
  match (parse_number (list_of_string s)) with
  | Error e -> print_string ("Parse error: " ^ e ^ "\n")
  | OK v _ ->  print_number v; print_string "\n";
              print_explode ( explode_number v 0 )

// let _ = check_example example2
// let _ = check_example example3
// let _ = check_example example4

type split_result =
  | NotFoundSplit  // no split
  | FinishedSplit  : (n:number) -> split_result // finished handling the leftmost split

let rec split_number (x:number) : split_result =
  match x with
  | Literal a -> if a > 9 then
     FinishedSplit (Pair (Literal (a / 2)) (Literal ((a+1)/2)))
     else
     NotFoundSplit
  | Pair l r  -> (
     match (split_number l) with
     | FinishedSplit a -> FinishedSplit (Pair a r)
     | NotFoundSplit -> (
        match (split_number r) with
       | FinishedSplit a -> FinishedSplit (Pair l a)
       | NotFoundSplit -> NotFoundSplit
     )
  )

let print_split (r:split_result) : ML unit = 
  match r with 
  | NotFoundSplit -> print_string "No split\n"
  | FinishedSplit n -> print_string "Finished\n"; print_number n; print_string "\n"

let check_example_split (v:number) : ML unit = 
  print_number v; print_string "\n";
  print_split ( split_number v )

// [[[[0,7],4],[15,[0,13]]],[1,1]]

let example5 = Pair (Pair (Pair (Pair (Literal 0) (Literal 7)) 
                                (Literal 4)) 
                          (Pair (Literal 15) 
                                (Pair (Literal 0) (Literal 13))))
                    (Pair (Literal 1) (Literal 1))                    
//let example6 = "[[[[0,7],4],[[7,8],[0,13]]],[1,1]]"

// let _ = check_example_split example5
// let _ = let v = split_number example5 in
//      if FinishedSplit? v then check_example_split (FinishedSplit?.n v)
//     else ()

let rec reduce (a:number) : Dv number =
  match explode_number a 0 with
  | Finished nn -> reduce nn
  | Left _ nn -> reduce nn  
  | Right nn _ -> reduce nn
  | NotFound ->
     match split_number a with
       | FinishedSplit nn -> reduce nn
       | NotFoundSplit -> a

let add_and_reduce (a:number) (b:number) : Dv number = 
  reduce (add_numbers a b)

let rec debug_reduce (a:number) : ML number =
  match explode_number a 0 with
  | Finished nn -> print_string "explode "; print_number nn; print_string "\n"; debug_reduce nn
  | Left _ nn -> print_string "explode "; print_number nn; print_string "\n"; debug_reduce nn
  | Right nn _ -> print_string "explode "; print_number nn; print_string "\n"; debug_reduce nn
  | NotFound ->
     match split_number a with
       | FinishedSplit nn -> print_string "split "; print_number nn; print_string "\n"; debug_reduce nn
       | NotFoundSplit -> print_string "done "; print_number a; print_string "\n"; a

let debug_add (s1:string) (s2:string) : ML unit = 
  let c1 = (list_of_string s1) in
  let c2 = (list_of_string s2) in
  let p1 : parse_result number c1 = parse_number c1 in
  let p2 : parse_result number c2 = parse_number c2 in
  if (Error? p1) || (Error? p2) then
    print_string "parse error"
  else
    let _ = debug_reduce (add_numbers (OK?.value p1) (OK?.value p2)) in ()

(*
Non-functional version of the above, why doesn't match work?

let debug_add2 (s1:string) (s2:string) : ML unit = 
  let c1 = (list_of_string s1) in
  let c2 = (list_of_string s2) in
  let p1 : parse_result number c1 = parse_number c1 in
  let p2 : parse_result number c2 = parse_number c2 in
  match (p1,p2) with
  | (OK v1 _,OK v2 _) -> let _ = debug_reduce (add_numbers v1 v2) in ()
  | _ -> print_string "parse error"
*)

// let _ = debug_add  "[[[[4,3],4],4],[7,[[8,4],9]]]"  "[1,1]"

let rec add_list (l:(list number){Cons? l}) : Dv number = 
  match l with
  | [a] -> a
  | [a;b] -> add_and_reduce a b
  | a :: b :: tail -> add_list ((add_and_reduce a b) :: tail)

let rec magnitude (n:number) : nat =
  match n with
  | Literal x -> x
  | Pair l r -> (op_Multiply 3 (magnitude l)) + (op_Multiply 2 (magnitude r))

let rec parse_input (fd:fd_read) : ML (list number) =
   try
     let line : (list char) = (list_of_string (read_line fd)) in
     match parse_number line with
     | Error e -> print_string e; failwith "parse error"
     | OK v _ -> v :: (parse_input fd)
   with
   | EOF -> []
   | _ -> failwith "unknown error"

let calc_part_1 (fn:string) : ML unit =
 let fd = open_read_file fn in
   let input = parse_input fd in
     if length input < 1 then
       print_string "empty input"
     else
     let sum = add_list input in
       print_number sum;
       print_string (sprintf "\nmagnitude %d\n" (magnitude sum))


let _ = calc_part_1 "example0.txt"
let _ = calc_part_1 "example1.txt"
let _ = calc_part_1 "example2.txt"
let _ = calc_part_1 "input.txt"

let rec find_max_sum (l:list number) (i:nat{i <= length l}) (j:nat{j <= length l}) (best:nat) : Dv nat =
  if i = length l then 
    best
  else if j = length l then
    find_max_sum l (i+1) 0 best
  else if i = j then
    find_max_sum l i (j+1) best
  else 
    let m = magnitude (add_and_reduce (index l i) (index l j)) in
      if m > best then 
         find_max_sum l i (j+1) m
      else
         find_max_sum l i (j+1) best
        

let calc_part_2 (fn:string) : ML unit =
 let fd = open_read_file fn in
   let input = parse_input fd in
     if length input < 1 then
       print_string "empty input"
     else
     let best = find_max_sum input 0 0 0 in
       print_string (sprintf "best magnitude = %d\n" best)


let _ = calc_part_2 "example2.txt"
let _ = calc_part_2 "input.txt"

