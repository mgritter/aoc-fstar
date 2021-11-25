module Part1

open FStar.List.Tot
open FStar.String
open FStar.IO
open FStar.All

type cell_contents =
  | Floor
  | EmptyChair
  | OccupChair
  | PermEmptyChair
  | PermOccupChair

let vector (a:Type) (len:nat) = (l:(list a){List.Tot.length l = len})

let matrix (a:Type) (width:nat{0<width}) (height:nat{0<height}) =
  (vector (vector a width) height)

let value_at #a #w #h (m:matrix a w h) (i:nat{0 <= i && i < h}) (j:nat{0 <= j && j < w}) : Tot a =
  List.Tot.index (List.Tot.index m i) j  

let neighbor_at #w #h (m:matrix cell_contents w h) (y:nat{0 <= y && y < h}) (x:nat{0 <= x && x < w}) 
  (dy:int{-1 <= dy && dy <= 1}) (dx:int{-1 <= dx && dx <= 1}) (old:list cell_contents) 
  : Tot (list cell_contents) =
  if (y = 0 && dy = -1) then
    old
  else if (x = 0 && dx = -1) then
    old
  else if (y = h - 1 && dy = 1) then
    old
  else if (x = w - 1 && dx = 1) then
    old
  else
    (value_at m (y + dy) (x+dx)) :: old

let neighborhood #w #h (m:matrix cell_contents w h) (y:nat{0 <= y && y < h}) (x:nat{0 <= x && x < w}) 
: Tot (list cell_contents) =
  neighbor_at m y x (-1) (-1)
   (neighbor_at m y x (-1) 0
    (neighbor_at m y x (-1) 1
  (neighbor_at m y x 0 (-1)
   (neighbor_at m y x 0 0
    (neighbor_at m y x 0 1
  (neighbor_at m y x 1 (-1)
   (neighbor_at m y x 1 0
    (neighbor_at m y x 1 1
      []))))))))

let rec num_occupied_neighbors (nn:list cell_contents) : Tot nat =
  match nn with 
  | [] -> 0
  | hd :: tl ->
    match hd with
    | Floor -> num_occupied_neighbors tl
    | EmptyChair -> num_occupied_neighbors tl
    | PermEmptyChair -> num_occupied_neighbors tl
    | OccupChair -> 1 + num_occupied_neighbors tl 
    | PermOccupChair -> 1 + num_occupied_neighbors tl

let transition (c:cell_contents) (nn:list cell_contents) : cell_contents =
  match c with
  | Floor -> Floor
  | EmptyChair -> if num_occupied_neighbors nn = 0 then OccupChair else EmptyChair
  | OccupChair -> if (num_occupied_neighbors nn) > 4 then EmptyChair else OccupChair
  | PermEmptyChair -> PermEmptyChair
  | PermOccupChair -> PermOccupChair


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

let transition_matrix #w #h (m:matrix cell_contents w h) : Tot (matrix cell_contents w h) =
  let map_row (y:nat{y<h}): (vector cell_contents w) = 
    let row : (l:list(j:nat{0 <= j && j < w}){List.Tot.length l = w}) = (nat_range_no_really w) in
      map_vec (fun (x:nat{0 <= x && x < w}) -> transition (value_at m y x) (neighborhood m y x)) row
    // map_vec (fun x -> Floor) (nat_range 0 w)
  in 
    nat_range_length 0 h;
    map_vec map_row (nat_range 0 h)

let parse_char (c:char) (l:list cell_contents) : (option (list cell_contents)) =
  match c with
  | 'L' -> Some (Cons EmptyChair l)
  | '.' -> Some (Cons Floor l)
  | _ -> None


let rec parse_row_aux (s:list char) (expected_len:nat) : Tot
 (option (vector cell_contents expected_len)) 
 (decreases expected_len) =
    if expected_len = 0 then
       match s with
         | [] -> Some []
         | _ -> None
    else
    let add_cell (c:cell_contents) (tl:list char) : (option (vector cell_contents expected_len)) =
       match (parse_row_aux tl (expected_len - 1)) with
       | None -> None
       | Some l -> Some (c :: l)
    in match s with 
    | [] -> None
    | '.' :: tl -> (add_cell Floor tl)
    | 'L' :: tl -> (add_cell EmptyChair tl)
    | _ -> None
    
let parse_row (s:string) (expected_len:nat) : (option (vector cell_contents expected_len)) =
  parse_row_aux (list_of_string s) expected_len

let rec parse_matrix_aux (fd:fd_read) (width:nat) : ML (list (vector cell_contents width)) =
  try 
   let line = read_line fd in
     match (parse_row line width) with
       | None -> failwith "Can't parse row"
       | Some row -> row :: (parse_matrix_aux fd width)
   with
     | EOF -> []
     | _ -> failwith "Unexpected error" 

type sized_matrix =
 | Matrix : (w:nat{w>0}) -> (h:nat{h>0}) -> (m:matrix cell_contents w h) -> sized_matrix

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

let row_to_string #w (row:(vector cell_contents w)) : Tot string =
  string_of_list
  ( List.Tot.map (fun c -> 
    match c with
    | Floor -> '.'
    | EmptyChair -> 'L'
    | OccupChair -> '#'
    | PermEmptyChair -> 'X'
    | PermOccupChair -> 'Z')
   row )

let print_matrix #h #w (m:matrix cell_contents w h) : ML unit =
  let print_row (r:(vector cell_contents w)) : ML unit =
    FStar.IO.print_string ( (row_to_string r) ^ "\n" )
  in let x = FStar.List.map print_row m in
    ()

let parse_and_iterate (fn:string): ML unit =
  let fd = open_read_file fn in
    let m = parse_matrix fd in
      match m with
      | Matrix w h board ->
         let m1 = transition_matrix board in
           print_matrix m1;
           let m2 = transition_matrix m1 in
             print_matrix m2

let _ = parse_and_iterate "example.txt"


(*
L.LL.LL.LL
LLLLLLL.LL
L.L.L..L..
LLLL.LL.LL
L.LL.LL.LL
L.LLLLL.LL
..L.L.....
LLLLLLLLLL
L.LLLLLL.L
L.LLLLL.LL
*)

