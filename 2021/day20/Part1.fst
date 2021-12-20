module Part1

open FStar.String
open FStar.IO
open FStar.Printf
open FStar.All
open FStar.List.Tot
  
type cell =
 | On
 | Off
 
let input_rule : string = "##.....##.#.#####.#...###...#.##..#....##..#.##.#.#....##.....#.##.##.#.#.#...#.#.#.###.##..#.#.#.#..#.##.#...#..#.#.#..#####.##.#..#..##.#..#.#...#.....#.###..#..#####.##...#..##..##...#.#...##.##..##...##.##.#......#...##.##.#####.#....####....######.#.#.......#.############.###..#..#......####......#..##.####.##....#..#.#.###..#.####.####.#.##.##.##..###.#..#.......#....#..########....##..##.#...#.#.###.###.###..#..#.###..#....#.###..#.##.##..###.#.#####....###.##.###.....#######........#.#.##...##.#...."

// the 000,000,000 rule flips . to #
// so the entire empty space flips every turn
// which means we have border problems :(

let example_rule : string = "..#.#..#####.#.#.#.###.##.....###.##.#..###.####..#####..#....#..#..##..###..######.###...####..#..#####..##..#.#####...##.#.#..#.##..#.#......#.###.######.###.####...#.##.##..#..#..#####.....#.#....###..#.##......#.....#..#..#..##..#...##.######.####.####.#.#...#.......#..#.#.#...####.##.#......#..#...##.#.##..#...##.#.##..###.#......#.#.......#.#.#.####.###.##...#.....####.#..#..#.##.#....##..#.####....##...##..#...#......#.#.......#.......##..####..#...#.#.#...##..#.#..###..#####........#..####......#..#"

let vector (a:Type) (len:nat) = (l:(list a){List.Tot.length l = len})

let matrix (a:Type) (width:nat{0<width}) (height:nat{0<height}) =
  (vector (vector a width) height)

let value_at #a #w #h (m:matrix a w h) (i:nat{0 <= i && i < h}) (j:nat{0 <= j && j < w}) : Tot a =
  List.Tot.index (List.Tot.index m i) j  

let neighbor_at #a #w #h (m:matrix a w h) (default_value:a) (y:nat{y < h}) (x:nat{x < w}) 
  (dy:int{-1 <= dy && dy <= 1}) (dx:int{-1 <= dx && dx <= 1}) (old:list a) 
  : Tot (l:(list a){length l = length old + 1})  =
  if (y = 0 && dy = -1) then
    default_value :: old
  else if (x = 0 && dx = -1) then
    default_value :: old
  else if (y = h - 1 && dy = 1) then
    default_value :: old
  else if (x = w - 1 && dx = 1) then
    default_value :: old
  else
    (value_at m (y + dy) (x+dx)) :: old
    
let neighborhood #a #w #h (m:matrix a w h) (dv:a) (y:nat{y<h}) (x:nat{x<w}) 
: Tot (l:(list a){length l = 9}) = 
  neighbor_at m dv y x (-1) (-1)
  (neighbor_at m dv y x (-1) 0
  (neighbor_at m dv y x (-1) 1
  (neighbor_at m dv y x 0 (-1)
  (neighbor_at m dv y x 0 0
  (neighbor_at m dv y x 0 1
  (neighbor_at m dv y x 1 (-1)
  (neighbor_at m dv y x 1 0
  (neighbor_at m dv y x 1 1
    []))))))))

// Copied from day 9 -- create a range of integres
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

let map_vec #a #b #n (f:a -> Tot b) (l:(list a){List.Tot.length l = n}) : Tot (vector b n) =
  List.Tot.map f l

let nat_range_no_really (w:nat{0 < w}) :  (l:list (z:nat{0 <= z && z < w}){List.Tot.length l = w}) =
  let ret = (nat_range 0 w) in 
    nat_range_length 0 w;
    ret

let rec parse_row_aux (s:list char) (expected_len:nat) : Tot
 (option (vector cell expected_len)) 
 (decreases expected_len) =
    if expected_len = 0 then
       match s with
         | [] -> Some []
         | _ -> None
    else
    let add_cell (c:cell) (tl:list char) : (option (vector cell expected_len)) =
       match (parse_row_aux tl (expected_len - 1)) with
       | None -> None
       | Some l -> Some (c :: l)
    in match s with 
    | [] -> None
    | '.' :: tl -> (add_cell Off tl)
    | '#' :: tl -> (add_cell On tl)
    | _ -> None
    
let parse_row (s:string) (expected_len:nat) : (option (vector cell expected_len)) =
  parse_row_aux (list_of_string s) expected_len

let rec parse_matrix_aux (fd:fd_read) (width:nat) : ML (list (vector cell width)) =
  try 
   let line = read_line fd in
     match (parse_row line width) with
       | None -> failwith "Can't parse row"
       | Some row -> row :: (parse_matrix_aux fd width)
   with
     | EOF -> []
     | _ -> failwith "Unexpected error" 

type sized_matrix =
 | Matrix : (w:nat{w>0}) -> (h:nat{h>0}) -> (m:matrix cell w h) -> sized_matrix

let parse_matrix (fd:fd_read) : ML sized_matrix =
  let first_line = read_line fd in
    let width = strlen first_line in
      match parse_row first_line width with
        | None -> failwith "Can't parse first row"
        | Some first_line ->
      let rest = parse_matrix_aux fd width in
        if width = 0 then
           failwith "Width can't be zero"
        else 
          Matrix width (1 + List.Tot.length rest) (first_line :: rest )

// Interpret the neighborhood as a binary number
//  MSB-> ...
//        ...
//        ... <- LSB
let rec bin_to_nat_aux (input:list cell)  : (next_place_value:nat & (v:nat{v < next_place_value})) =
  match input with 
  | [] -> (| 1, 0 |)
  | On :: rest -> 
     let smaller = bin_to_nat_aux rest in
        (| op_Multiply 2 (dfst smaller),
           (dfst smaller) + (dsnd smaller) |)
  | Off :: rest -> 
     let smaller = bin_to_nat_aux rest in
        (| op_Multiply 2 (dfst smaller),
           (dsnd smaller) |)

let bin_to_nat (input:list cell) : nat =
  (dsnd (bin_to_nat_aux input))

let input_length_1 (input:(list cell){length input = 1}) :
  Lemma (dfst (bin_to_nat_aux input) = 2)
  = ()

let rec input_length_x (x:nat) (input:(list cell){length input = x}) :
  Lemma (dfst (bin_to_nat_aux input) = (pow2 x)) 
  = if x = 0 then
       ()
    else
       input_length_x (x-1) (tl input)
       
let bin9_to_nat (input:list cell{length input = 9}) : (n:nat{n<512}) =
  input_length_x 9 input; 
  (dsnd (bin_to_nat_aux input))

let example_matrix : matrix cell 3 3 = [
   [Off;Off;Off];
   [ On;Off;Off];
   [Off; On;Off]
]

let _ = print_string 
  (sprintf "I got %d\n" (bin9_to_nat (neighborhood example_matrix Off 1 1)))

let transition (rule:(list cell){length rule = 512}) (nn:(list cell){length nn=9}) : cell =
  index rule (bin9_to_nat nn)

let transition_matrix #w #h (m:matrix cell w h) 
  (rule:(list cell){length rule = 512}) (dv:cell)   
: Tot (matrix cell w h) =
  let map_row (y:nat{y<h}): (vector cell w) = 
    let row : (l:list(j:nat{0 <= j && j < w}){List.Tot.length l = w}) = (nat_range_no_really w) in
      map_vec (fun (x:nat{0 <= x && x < w}) -> transition rule (neighborhood m dv y x)) row
  in 
    nat_range_length 0 h;
    map_vec map_row (nat_range 0 h)


let expand_matrix #w #h (m:matrix cell w h) (n:nat)
  : (matrix cell (w+n+n) (h+n+n)) =
  let new_w = w+n+n in
  let new_h = h+n+n in
  let map_row (y:nat{y<new_h}): (vector cell (new_w)) = 
    let row : (l:list(j:nat{0 <= j && j < new_w}){List.Tot.length l = new_w}) = (nat_range_no_really new_w) in
      map_vec (fun (x:nat{0 <= x && x < new_w}) -> 
                 if y < n || x < n then
                   Off
                 else if y >= h+n || x >= w+n then
                   Off
                 else
                   value_at m (y-n) (x-n)
               ) row
  in 
    nat_range_length 0 new_h;
    map_vec map_row (nat_range 0 new_h)

let row_to_string #w (row:(vector cell w)) : Tot string =
  string_of_list
  ( List.Tot.map (fun c -> 
    match c with
    | Off -> '.'
    | On -> '#'
    )
   row)

let print_matrix #h #w (m:matrix cell w h) : ML unit =
  let print_row (r:(vector cell w)) : ML unit =
    FStar.IO.print_string ( (row_to_string r) ^ "\n" )
  in FStar.List.iter print_row m;
    print_string "\n"

let count_pixels #h #w (m:matrix cell w h ) : Tot int =
  List.Tot.fold_left
    (fun prev_count (row:(vector cell w)) -> 
      (List.Tot.fold_left 
         (fun count (c:cell) -> 
            match c with 
            | On -> count + 1
            | Off -> count
         )
         prev_count (List.Tot.list_unref row)))
  0 m

let parse_and_iterate (fn:string) (rule:string): ML unit =
  let ro = parse_row_aux (list_of_string rule) 512 in
  if None? ro then
     print_string "erorr parsing_rule\n"
  else 
  let rule = Some?.v ro in
  let fd = open_read_file fn in
    let m = parse_matrix fd in
      match m with
      | Matrix w h board ->
         print_matrix board;
         let m0 = expand_matrix board 2 in
         print_matrix m0;
         let m1 = transition_matrix m0 rule Off in  // TODO: something smart
           print_matrix m1;
           let m2 = transition_matrix m1 rule On in
             print_matrix m2;
             print_string (sprintf "num pixels=%d\n"
                          (count_pixels m2))

// let _ = parse_and_iterate "example.txt" example_rule
let _ = parse_and_iterate "input.txt" input_rule





