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

let upd_at #a #w #h (m:matrix a w h) (i:nat{0 <= i && i < h}) (j:nat{0 <= j && j < w}) (v:a) 
  : Tot (matrix a w h) =
  let pre_y, row, post_y = List.Tot.split3 m i in
    assert( List.Tot.length row = w );
    let pre_x, _, post_x = List.Tot.split3 row j in
      List.Pure.lemma_split3_length m i;
      List.Pure.lemma_split3_length row j;
      assert( List.Tot.length pre_x = j );
      assert( List.Tot.length (v :: post_x) = w - j);
      let replacement_vec : (vector a w) = (pre_x @ (v :: post_x)) in
        assert( List.Tot.length pre_y = i );
        assert( List.Tot.length (replacement_vec :: post_y) = h - i);
        pre_y @ (replacement_vec :: post_y)


let neighbor_at #a #w #h (m:matrix a w h) (y:nat{y < h}) (x:nat{x < w}) 
  (dy:int{-1 <= dy && dy <= 1}) (dx:int{-1 <= dx && dx <= 1}) (old:list (y:nat{y<h}*x:nat{x<w})) 
  : Tot (list (y:nat{y<h}*x:nat{x<w})) = 
  if (y = 0 && dy = -1) then
    old
  else if (x = 0 && dx = -1) then
    old
  else if (y = h - 1 && dy = 1) then
    old
  else if (x = w - 1 && dx = 1) then
    old
  else
    ((y + dy),(x+dx)) :: old
    
let neighborhood #a #w #h (m:matrix a w h ) (y:nat{y<h}) (x:nat{x<w}) 
: Tot (list (y:nat{y<h}*x:nat{x<w})) = 
  neighbor_at m y x 0 (-1)
  (neighbor_at m y x (-1) 0
  (neighbor_at m y x 1 0
  (neighbor_at m y x 0 1
    [])))

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

// Leftist heap, following
// https://courses.cs.washington.edu/courses/cse326/08sp/lectures/05-leftist-heaps.pdf

type int_1 = (z:int{z >= -1})

noeq type heapnode : v:Type -> (npl:int_1) -> Type =
  | Null : #v:Type -> heapnode v (-1)
  | Node: #v:Type -> 
          npl_left:int_1 -> left:heapnode v npl_left -> 
          key:nat -> value:v -> 
          (npl_right:int_1{npl_right <= npl_left}) -> right:(heapnode v npl_right) -> 
          heapnode v (1 + (min npl_left npl_right))

let empty_heap (#v:Type) = Null

let singleton_heap (#v:Type) (key:nat) (value:v) : (heapnode v 0) =
  Node (-1) Null key value (-1) Null

// We don't have any way to decrease_key for this heap implementation.
// So, we will have to allow the same value to be inserted multiple times,
// and just check in our matrix whether we've already found the minimum value for it.

// Merge two leftist heaps
let rec merge_heaps (#v:Type) (#npl_a:int_1) (a:heapnode v npl_a) (#npl_b:int_1) (b:heapnode v npl_b) 
  : Tot (npl_result:int_1 & (heapnode v npl_result)) 
    (decreases %[a;b]) =
  if Null? a then
     (| npl_b, b |)
  else if Null? b then
     (| npl_a, a |)
  else if Node?.key a <= Node?.key b then (
     // a has the minimum key
     let new_left = Node?.left a in
     let npl_left = Node?.npl_left a in
     let new_tree = merge_heaps (Node?.right a) b in
     let npl_right = dfst new_tree in
     let new_right = dsnd new_tree in
        if npl_right <= npl_left then
           // Order is OK
           (| 1 + (min npl_left npl_right),
              Node npl_left new_left 
                   (Node?.key a) (Node?.value a)
                   npl_right new_right |)
        else
           // Invariant not OK, swap the trees to preserve it
           (| 1 + (min npl_left npl_right),
              Node npl_right new_right 
                   (Node?.key a) (Node?.value a)
                   npl_left new_left |)                      
  ) else 
     // b has the minimum key
     let new_left = Node?.left b in
     let npl_left = Node?.npl_left b in
     let new_tree = merge_heaps a (Node?.right b) in
     let npl_right = dfst new_tree in
     let new_right = dsnd new_tree in
        if npl_right <= npl_left then
           // Order is OK
           (| 1 + (min npl_left npl_right),
              Node npl_left new_left 
                   (Node?.key b) (Node?.value b)
                   npl_right new_right |)
        else
           // Invariant not OK, swap the trees to preserve it
           (| 1 + (min npl_left npl_right),
              Node npl_right new_right 
                   (Node?.key b) (Node?.value b)
                   npl_left new_left |)                      

let insert (#v:Type) (#npl_root:int_1) (root:heapnode v npl_root) (key:nat) (value:v) 
  : Tot (npl_result:int_1 & (heapnode v npl_result)) =
  merge_heaps root (singleton_heap key value)

let n0 : heapnode nat (-1) = Null
let n2 = insert #nat (dsnd (insert n0 2 2)) 1 1
let _ = assert_norm( (dsnd n2)
  == (Node 0 (Node (-1) Null 2 2 (-1) Null) 1 1 (-1) Null ))

noeq type pop_result : v:Type -> Type =
  | MinValue : (#v:Type) -> (key:nat) -> (value:v) -> (npl:int_1) -> (new_root:heapnode v npl) -> pop_result v
  
let pop_min (#v:Type) (#npl_root:int_1{npl_root >= 0}) (root:heapnode v npl_root)
 : Tot (pop_result v) =
 match root with 
 | Node npl_left left key value npl_right right ->
   let new_tree = merge_heaps left right in
     MinValue key value (dfst new_tree) (dsnd new_tree)

type distance =
  | Infinity
  | Finite : n:nat -> distance
  | Finished : n:nat -> distance

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

let start_matrix (w:nat{w>0}) (h:nat{h>0}) : Tot (matrix distance w h) =
  let map_row (y:nat{y<h}): (vector distance w) = 
    let row : (l:list(j:nat{0 <= j && j < w}){List.Tot.length l = w}) = (nat_range_no_really w) in
      map_vec (fun (x:nat{0 <= x && x < w}) -> 
         if x = 0 && y = 0 then
            Finite 0
         else
            Infinity)
      row
  in 
    nat_range_length 0 h;
    map_vec map_row (nat_range 0 h)

let finish_node #w #h (distances:matrix distance w h)
   (y:nat{y<h}) (x:nat{x<w}) (d_xy:nat) 
   : Tot (matrix distance w h) = 
   upd_at distances y x (Finished d_xy)

let print_distances #w #h (distances:matrix distance w h) : ML unit = 
    let map_row (row:(vector distance w)) : ML unit =
       List.iter (fun (d:distance) ->
         match d with 
         | Infinity -> print_string "∞|"
         | Finite n -> print_string (sprintf "%d|" n)
         | Finished n -> print_string (sprintf "F%d|" n)
        ) row;
       print_string "\n"
  in 
    List.iter map_row distances

let update_neighbors #w #h (weights:matrix nat w h) (distances:matrix distance w h)
   (y:nat{y<h}) (x:nat{x<w}) (d_xy:nat) 
   : Tot (matrix distance w h) = 
   List.Tot.fold_left (fun (m:matrix distance w h) (p:(ny:nat{ny<h}*nx:nat{nx<w})) ->
     // Update the distance to the lower of current value and d_xy + cost to enter
     // (ny,nx)
     let old_value = value_at m (fst p) (snd p) in
     let new_cost = d_xy + value_at weights (fst p) (snd p) in 
       match old_value with
       | Infinity -> upd_at m (fst p) (snd p) (Finite new_cost)
       | Finite old_cost -> if old_cost > new_cost then
           upd_at m (fst p) (snd p) (Finite new_cost)
         else
           m
       | Finished _ -> m
   ) distances (neighborhood distances y x)

let insert_neighbors #w #h (distances:matrix distance w h) 
    (y:nat{y<h}) (x:nat{x<w})    
    (npl:int_1) (pri_queue:heapnode (x:nat{x<w}*y:nat{y<h}) npl) 
  : Tot (npl_result:int_1 & (heapnode (x:nat{x<w}*y:nat{y<h}) npl_result)) =
   let start_queue : (npl:int_1 & (heapnode (x:nat{x<w}*y:nat{y<h}) npl)) = 
     (| npl, pri_queue |) in
   // Ack, type inferece totally failed on pq
   List.Tot.fold_left (fun (pq:(npl:int_1 & (heapnode (x:nat{x<w}*y:nat{y<h}) npl))) nn ->
     let new_cost = value_at distances (fst nn) (snd nn) in 
       match new_cost with
       | Infinity -> pq // shouldn't happen?       
        // Aaaugh I mixed up the order of the pairs between the two data structures
       | Finite cost -> (insert (dsnd pq) cost (snd nn, fst nn))
       | Finished _ -> pq  
   ) start_queue (neighborhood distances y x)

let rec dijkstras #w #h (weights:matrix nat w h) (distances:matrix distance w h) 
   (pq_npl:int_1) (pri_queue:heapnode (x:nat{x<w}*y:nat{y<h}) pq_npl) 
   : Dv (matrix distance w h) =
   if pq_npl = -1 then
     distances
   else
     match pop_min pri_queue with
     | MinValue key value npl new_root -> 
       let y = (snd #(x:nat{x<w}) #(y:nat{y<h}) value) in
       let x = (fst #(x:nat{x<w}) #(y:nat{y<h}) value) in
       let v = value_at distances y x in (
         // Proving the relationship between the distances matrix and the
         // contents of the priority queue is a good goal, but challenging.
         assume( ~ (Infinity? v) );
         match v with 
         | Finished _ ->
              dijkstras weights distances npl new_root
         | Finite n ->
            let new_distances_1 = finish_node distances y x n in
            let new_distances_2 = update_neighbors weights new_distances_1 y x n in
            let new_q = insert_neighbors new_distances_2 y x npl new_root in
              dijkstras weights new_distances_2 (dfst new_q) (dsnd new_q)
       )

#push-options "--z3rlimit 60"
// This query is very inconsistent, sometimes it succeeds right away and sometimes fails
let expand_matrix #w #h (m:matrix nat w h) : (matrix nat (op_Multiply 5 w) (op_Multiply 5 h)) =
  let w5 = (op_Multiply 5 w) in
  let h5 = (op_Multiply 5 h) in
  let map_row (y:nat{y<h5}): (vector nat w5) = 
    let row : (l:list(j:nat{0 <= j && j < w5}){List.Tot.length l = w5}) = (nat_range_no_really w5) in
      map_vec #(x:nat{0 <= x && x < w5}) #nat #w5 (fun (x:nat{0 <= x && x < w5}) -> 
         let orig_y = op_Modulus y h in
         let orig_x = op_Modulus x w in
         let dx = x / w in
         let dy = y / w in
         let manhattan_distance = dx + dy in
         let danger = value_at m orig_y orig_x + manhattan_distance in
         if danger > 9 then danger - 9 else danger)
      row
  in 
    nat_range_length 0 h5;
    map_vec map_row (nat_range 0 h5)
#pop-options

let find_minimum_path #w #h (m:matrix nat w h) : Dv distance =
   let dmatrix = dijkstras m (start_matrix w h) 0 (singleton_heap 0 (0,0)) in
     value_at dmatrix (h-1) (w-1)     

let calc_part_2 (fn:string): ML unit =
  let fd = open_read_file fn in
    let m = parse_matrix fd in
      match m with
      | Matrix w h board ->
         let soln = find_minimum_path (expand_matrix board) in
           match soln with
           | Finished v ->
             print_string (sprintf "Minimum-cost path: %d\n" v) 
           | Finite v ->
             print_string (sprintf "Finite value: %d\n" v)
           | Infinity ->
             print_string "Error, infinite value\n"

let _ = calc_part_2 "example.txt"
let _ = calc_part_2 "input.txt"

