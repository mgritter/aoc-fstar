module Part2

open FStar.List.Tot
open FStar.String
open FStar.IO
open FStar.All
open FStar.Printf

let vector (a:Type) (len:nat) = (l:(list a){List.Tot.length l = len})

let matrix (a:Type) (width:nat{0<width}) (height:nat{0<height}) =
  (vector (vector a width) height)

let value_at #a #w #h (m:matrix a w h) (i:nat{0 <= i && i < h}) (j:nat{0 <= j && j < w}) : Tot a =
  List.Tot.index (List.Tot.index m i) j  

let neighbor_at #w #h (m:matrix nat w h) (y:nat{0 <= y && y < h}) (x:nat{0 <= x && x < w}) 
  (dy:int{-1 <= dy && dy <= 1}) (dx:int{-1 <= dx && dx <= 1}) (old:list nat) 
  : Tot (list nat) =
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
    
let neighborhood #w #h (m:matrix nat w h) (y:nat{0 <= y && y < h}) (x:nat{0 <= x && x < w}) 
: Tot (list nat) =
  neighbor_at m y x (-1) 0
  (neighbor_at m y x 1 0
   (neighbor_at m y x 0 (-1)
     (neighbor_at m y x 0 1
      [])))

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
 (option (vector nat expected_len)) 
 (decreases expected_len) =
    if expected_len = 0 then
       match s with
         | [] -> Some []
         | _ -> None
    else
    let add_cell (c:nat) (tl:list char) : (option (vector nat expected_len)) =
       match (parse_row_aux tl (expected_len - 1)) with
       | None -> None
       | Some l -> Some (c :: l)
    in match s with 
    | [] -> None
    | '0' :: tl -> (add_cell 0 tl)
    | '1' :: tl -> (add_cell 1 tl)
    | '2' :: tl -> (add_cell 2 tl)
    | '3' :: tl -> (add_cell 3 tl)
    | '4' :: tl -> (add_cell 4 tl)
    | '5' :: tl -> (add_cell 5 tl)
    | '6' :: tl -> (add_cell 6 tl)
    | '7' :: tl -> (add_cell 7 tl)
    | '8' :: tl -> (add_cell 8 tl)
    | '9' :: tl -> (add_cell 9 tl)
    | _ -> None
    
let parse_row (s:string) (expected_len:nat) : (option (vector nat expected_len)) =
  parse_row_aux (list_of_string s) expected_len

let rec parse_matrix_aux (fd:fd_read) (width:nat) : ML (list (vector nat width)) =
  try 
   let line = read_line fd in
     match (parse_row line width) with
       | None -> failwith "Can't parse row"
       | Some row -> row :: (parse_matrix_aux fd width)
   with
     | EOF -> []
     | _ -> failwith "Unexpected error" 

type sized_matrix =
 | Matrix : (w:nat{w>0}) -> (h:nat{h>0}) -> (m:matrix nat w h) -> sized_matrix

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

let is_minimum #w #h (m:matrix nat w h) (y:nat{y<h}) (x:nat{x<w}) : (list (y:nat{y<h}*x:nat{x<w})) =
  if for_all (fun (n:nat) -> n > (value_at m y x)) (neighborhood m y x) then
    [(y,x)]
  else
    []

let find_local_minima #w #h (m:matrix nat w h) : Tot (list (y:nat{y<h}*x:nat{x<w})) =
  let map_row (y:nat{y<h}): (list (y:nat{y<h}*x:nat{x<w})) =
    let row : (l:list(j:nat{0 <= j && j < w}){List.Tot.length l = w}) = (nat_range_no_really w) in
      List.Tot.collect (fun (x:nat{0 <= x && x < w}) -> is_minimum m y x ) row
  in 
    nat_range_length 0 h;
    List.Tot.collect map_row (nat_range 0 h)

let rec sum_depths #w #h (m:matrix nat w h) (l:list (y:nat{y<h}*x:nat{x<w})) : nat =
   match l with
   | [] -> 0
   | (y,x) :: tl -> (1 + (value_at m y x)) + (sum_depths m tl )

let rec print_depths #w #h (m:matrix nat w h) (l:list (y:nat{y<h}*x:nat{x<w})) : ML unit =
   match l with
   | [] -> ()
   | (y,x) :: tl -> 
      print_string (sprintf "(%dx%d) " y x );
      print_depths m tl

type pairset = Set.set (nat*nat)

let rec dfs_size #w #h (m:matrix nat w h) (y:int) (x:int) (visited:pairset) : ML (nat*pairset) =
  if y >= h || y < 0 then
    (0,visited)
  else if x >= w || x < 0 then
    (0,visited)
  else if value_at m y x = 9 then
    (0,visited)
  else if Set.mem (y,x) visited then
    (0,visited)
  else
    let v0 = Set.union visited (Set.singleton (y,x)) in
      let (c1,v1) = dfs_size m (y+1) x v0 in
        let (c2,v2) = dfs_size m (y-1) x v1 in
          let (c3,v3) = dfs_size m y (x+1) v2 in
            let (c4,v4) = dfs_size m y (x-1) v3 in
             (1 + c1 + c2 + c3 + c4, v4)

let rec collect_all_region_size #w #h (m:matrix nat w h) (y:nat{y<=h}) (x:nat{x<=w}) 
 (visited:pairset) (basins:list nat) : ML (list nat) =
  if y = h then
    basins
  else if x = w then
    collect_all_region_size m (y+1) 0 visited basins
  else if value_at m y x = 9 then
    collect_all_region_size m y (x+1) visited basins
  else if Set.mem (y,x) visited then
    collect_all_region_size m y (x+1) visited basins
  else let (size,new_visit) = dfs_size m y x visited in
    collect_all_region_size m y (x+1) new_visit (size :: basins)

let rec print_sizes (l:list nat) : ML unit =
   match l with
   | [] -> ()
   | hd :: tl -> 
      print_string (sprintf "%d " hd );
      print_sizes tl

let product_of_top_three (l:list nat) : ML nat =
   let s = List.sortWith (fun (a:nat) (b:nat) -> a - b) l in
     let num = List.Tot.length s in
     if num < 3 then
        failwith "List too short"
     else (
        op_Multiply (List.Tot.index s (num-1)) 
          (op_Multiply (List.Tot.index s (num-2)) (List.Tot.index s (num-3)))
     )
     
let calc_part_2 (fn:string): ML unit =
  let fd = open_read_file fn in
    let m = parse_matrix fd in
      match m with
      | Matrix w h board ->
         let soln = collect_all_region_size board 0 0 Set.empty [] in
           print_sizes soln;
           print_string "\n";
           print_string (sprintf "product of values=%d\n" (product_of_top_three soln))

let _ = calc_part_2 "example.txt"
let _ = calc_part_2 "input.txt"

