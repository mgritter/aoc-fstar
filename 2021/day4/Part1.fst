module Part1

open FStar.Int32
open FStar.IO
open FStar.String
open FStar.All
open FStar.List.Tot
open FStar.Printf

type square =
  | Occupied
  | Empty
  
let vector (a:Type) (len:nat) = (l:(list a){length l = len})

let matrix (a:Type) (width:nat{0<width}) (height:nat{0<height}) =
  (vector (vector a width) height)

let value_at #a #w #h (m:matrix a w h) (i:nat{0 <= i && i < h}) (j:nat{0 <= j && j < w}) : Tot a =
  index (index m i) j  

let int32_to_int (n:Int32.t) : int =
  Int32.v n

let parse_comma_separated_numbers (s:string) : list int =
  map (fun x -> (int32_to_int (Int32.of_string x))) (String.split [','] s)  

val zero_to_four (_:unit) : (l:list (n:nat{n<5}){length l = 5})
let zero_to_four _ = 
  let x = [0;1;2;3;4] in
    assert_norm( length x = 5);
    x

let parse_two_digit_int (s:string{strlen s = 2}) : int =
  if (sub s 0 1) = " " then
    int32_to_int (Int32.of_string (sub s 1 1))
  else
    int32_to_int (Int32.of_string s)
  
// Parse: NN NN NN NN NN
//        b e^
let parse_space_separated_numbers (s:string{strlen s = 14}) : (l:(list int){length l = 5}) =
  map parse_two_digit_int
    (map (fun (i:nat{i<5}) -> 
         (String.sub s (op_Multiply i 3) 2))
      (zero_to_four()))

let parse_number_matrix (l:(list (s:string{strlen s = 14})){length l = 5}) : Tot (matrix int 5 5) =
  map parse_space_separated_numbers l

let read_14_character_line (fd:fd_read) : ML (s:string{strlen s = 14}) =
  let s = read_line fd in
    if strlen s <> 14 then
      failwith "line is the wrong length"
    else
      s

let read_five_lines (fd:fd_read) : ML (l:(list (s:string{strlen s = 14})){length l = 5}) =
  let _ = read_line fd in  // blank
    let l1 = read_14_character_line fd in
    let l2 = read_14_character_line fd in
    let l3 = read_14_character_line fd in
    let l4 = read_14_character_line fd in
    let l5 = read_14_character_line fd in
       [l1; l2; l3; l4; l5]
       
let rec read_matrix_list (fd:fd_read) : ML (list (matrix int 5 5)) =  
   try
     let lines = read_five_lines fd in
         (parse_number_matrix lines) :: (read_matrix_list fd)
   with
   | EOF -> []
   | _ -> failwith "unknown error"

type card = matrix int 5 5 * matrix square 5 5

let five_copies (#a:Type) (v:a) : (l:(list a){length l = 5}) =
  let r = [v;v;v;v;v] in 
    assert_norm( length r = 5 );
    r

let to_empty_card (m:matrix int 5 5) : card =
  (m, (five_copies (five_copies Empty)))

let map_vec #a #b #n (f:a -> Tot b) (l:(list a){List.Tot.length l = n}) : Tot (vector b n) =
  List.Tot.map f l

let mark_single_card (num:int) (c:card) : card =
  let numbers = (fst c) in
  let marks = (snd c) in
  let new_marks = 
    map_vec (fun (y:nat{y<5}) -> 
      (map_vec (fun (x:nat{x<5}) -> 
        if value_at numbers y x = num then
           Occupied
        else
           value_at marks y x)
        (zero_to_four()))
        ) (zero_to_four()) in
     (numbers,new_marks)

let mark (num:int) (boards: list card) : (list card) =
  map (mark_single_card num) boards
   
let is_row_winner (r:nat{r<5}) (c:card) 
: (b:bool{b = for_all (fun sq -> sq = Occupied) (index (snd c) r)})
 = for_all (fun sq -> sq = Occupied) (index (snd c) r)

let _ = assert( for_all (fun sq -> sq = Occupied) [Occupied; Occupied; Occupied;Occupied;Occupied] )
let _ = assert( ~ (for_all (fun sq -> sq = Occupied) [Occupied; Occupied; Occupied;Empty;Occupied]) )

let has_row_winner (c:card) : (b:bool{b ==> (exists r . is_row_winner r c)}) =
  is_row_winner 0 c ||
  is_row_winner 1 c ||
  is_row_winner 2 c ||
  is_row_winner 3 c ||
  is_row_winner 4 c

let column (col:nat{col<5}) (c:card) : (vector square 5) =
  [ (value_at (snd c) 0 col); (value_at (snd c) 1 col); (value_at (snd c) 2 col); 
    (value_at (snd c) 3 col); (value_at (snd c) 4 col) ]

let is_column_winner (col:nat{col<5}) (c:card) 
: (b:bool{b = for_all (fun sq -> sq = Occupied) (column col c)})
 = for_all (fun sq -> sq = Occupied) (column col c)

let has_column_winner (c:card) : (b:bool{b ==> (exists r . is_column_winner r c)}) =
  is_column_winner 0 c ||
  is_column_winner 1 c ||
  is_column_winner 2 c ||
  is_column_winner 3 c ||
  is_column_winner 4 c

let is_winner (c:card) : (b:bool{b <==> has_column_winner c \/ has_row_winner c}) =
  has_column_winner c || has_row_winner c
  
let find_winner (boards: list card) : (option (c:card{is_winner c})) =
  find is_winner boards
 
let calculate_score (winning_card:card) : int =
  fold_right (fun (y:nat{y<5}) (t:int) -> 
      (t + 
      (fold_right (fun (x:nat{x<5}) (t:int) -> 
         if value_at (snd winning_card) y x = Occupied then
            t
         else
            t + (value_at (fst winning_card) y x))
         (zero_to_four()) 0 )
      ))
      (zero_to_four()) 0

let occup_to_string (q:square) : string =
 match q with 
 | Occupied -> "O"
 | Empty -> "."
 
let print_card (c:card) : ML unit =
  let _ = List.map 
    (fun (row:vector square 5) -> print_string 
     (sprintf "%s %s %s %s %s \n"
       (occup_to_string (index row 0))
       (occup_to_string (index row 1))
       (occup_to_string (index row 2))
       (occup_to_string (index row 3))
       (occup_to_string (index row 4))))
    (snd c)
(*
    in let _ = List.map
      (fun (i:nat{i<5}) -> print_string (sprintf "%d %b\n" i (is_row_winner i c)))
      (zero_to_four())
*)
    in 
    print_string (sprintf "%b\n" (is_winner c));
    print_string "\n"

let rec first_winning_card (order:list int) (boards:list card) : ML (option (int*card)) =
  match order with
  | [] -> None
  | hd :: tl ->
    let marked_boards = mark hd boards in
      // let _ = List.map print_card marked_boards in
      match find_winner marked_boards with
        | None -> first_winning_card tl marked_boards
        | Some c -> Some (hd,c)        
   
let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let order = parse_comma_separated_numbers (read_line fd) in
      let cs = (map to_empty_card (read_matrix_list fd)) in
        let wopt = first_winning_card order cs in
          match wopt with 
          | None -> print_string "No winner"
          | Some (last_num,w) -> let score = calculate_score w in
             print_string (sprintf "last_number=%d\n" last_num);
             print_string (sprintf "board_score=%d\n" score);
             print_string (sprintf "%d\n" (op_Multiply score last_num))

let _ = calc_part_1 "input.txt"
//let _ = calc_part_1 "example.txt"



