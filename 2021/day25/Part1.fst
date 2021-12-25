module Part1

open FStar.String
open FStar.IO
open FStar.All
open FStar.Printf
open FStar.List.Tot
  
type cell =
 | Empty
 | East
 | South

let vector (a:Type) (len:nat) = (l:(list a){List.Tot.length l = len})

let matrix (a:Type) (width:nat{0<width}) (height:nat{0<height}) =
  (vector (vector a width) height)

let value_at #a #w #h (m:matrix a w h) (i:nat{0 <= i && i < h}) (j:nat{0 <= j && j < w}) : Tot a =
  List.Tot.index (List.Tot.index m i) j  
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
    | '.' :: tl -> (add_cell Empty tl)
    | '>' :: tl -> (add_cell East tl)
    | 'v' :: tl -> (add_cell South tl)
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

let east_transition #w #h (m:matrix cell w h) (y:nat{y<h}) (x:nat{x<w}) : cell = 
 match value_at m y x with
 | Empty -> (
   let x_west = (x - 1) % w in
     Math.Lemmas.lemma_mod_lt (x-1) w;
     match value_at m y x_west with
     | East -> East
     | _ -> Empty
 )
 | East -> (
   let x_east = (x + 1) % w in
     Math.Lemmas.lemma_mod_lt (x+1) w;
     match value_at m y x_east with
     | Empty -> Empty
     | _ -> East
 )
 | South -> South

let east_test_case (m:matrix cell 10 10) :
  Lemma (requires (value_at m 0 8) = East /\
                  (value_at m 0 9) = Empty )      
        (ensures (east_transition m 0 9 ) = East /\
                 (east_transition m 0 8 ) = Empty)
        = ()
  

let east_doesnt_change_south #w #h (m:matrix cell w h) (y:nat{y<h}) (x:nat{x<w}) :
  Lemma (requires (value_at m y x) = South)
        (ensures (east_transition m y x ) = South)
        = ()

let south_transition #w #h (m:matrix cell w h) (y:nat{y<h}) (x:nat{x<w}) : cell = 
 match value_at m y x with
 | Empty -> (
   let y_north = (y - 1) % h in
     Math.Lemmas.lemma_mod_lt (y-1) h;
     match value_at m y_north x with
     | South -> South
     | _ -> Empty
 )
 | South -> (
   let y_south = (y + 1) % h in
     Math.Lemmas.lemma_mod_lt (y+1) h;
     match value_at m y_south x with
     | Empty -> Empty
     | _ -> South
 )
 | East -> East

let south_doesnt_change_east #w #h (m:matrix cell w h) (y:nat{y<h}) (x:nat{x<w}) :
  Lemma (requires (value_at m y x) = East)
        (ensures (south_transition m y x ) = East)
        = ()

let south_doesnt_change_east_2 #w #h (m:matrix cell w h) (y:nat{y<h}) (x:nat{x<w}) :
  Lemma (requires (value_at m y x) <> East)
        (ensures (south_transition m y x ) <> East)
        = ()

let transition_matrix #w #h (m:matrix cell w h) 
  (transition:(m:matrix cell w h) -> (y:nat{y<h}) -> (x:nat{x<w}) -> cell)
: Tot (matrix cell w h) =
  let map_row (y:nat{y<h}): (vector cell w) = 
    let row : (l:list(j:nat{0 <= j && j < w}){List.Tot.length l = w}) = (nat_range_no_really w) in
      map_vec (fun (x:nat{0 <= x && x < w}) -> transition m y x) row
  in 
    nat_range_length 0 h;
    map_vec map_row (nat_range 0 h)

// Why isn't this in F* standard library?  Only the one with ML effect exists.
let rec zip #a #b (l1:list a) (l2:list b{length l1 = length l2}) 
  : Tot (list (a*b))
= match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)

let matrix_equality #w #h (m1:matrix cell w h) (m2:matrix cell w h) : bool =
  List.Tot.for_all 
    (fun (p_rows:(a:(list cell){length a = w}*b:(list cell){length b = w}))  -> 
       List.Tot.for_all 
         (fun p_cells -> fst p_cells = snd p_cells)
       (zip (fst p_rows) (snd p_rows))
    )
  (zip m1 m2)

let row_to_string #w (row:(vector cell w)) : Tot string =
  string_of_list
  ( List.Tot.map (fun c -> 
    match c with
    | Empty -> '.'
    | East -> '>'
    | South -> 'v'
    )
   row)

let print_matrix #h #w (m:matrix cell w h) : ML unit =
  let print_row (r:(vector cell w)) : ML unit =
    FStar.IO.print_string ( (row_to_string r) ^ "\n" )
  in FStar.List.iter print_row m;
    print_string "\n"

let rec iterate_until_same #h #w (m:matrix cell w h) (n:nat) : ML nat =
  let next_n = n + 1 in
  let m1 = transition_matrix m east_transition in
  let m2 = transition_matrix m1 south_transition in
    print_string (sprintf "after %d steps:\n" next_n);
    print_matrix m2;
    if matrix_equality m m2 then (
      print_string (sprintf "first move where nothing moves: %d\n" next_n); next_n
    ) else (
      iterate_until_same m2 next_n
    )
      
let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let m = parse_matrix fd in
      match m with
      | Matrix w h board ->
        print_matrix board;
        let result = iterate_until_same board 0 in
          ()

//let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"
