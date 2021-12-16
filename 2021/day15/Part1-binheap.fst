module Part1

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


// Heap data structures
//
//       root  5  
//      /    \ 
// 3   X      Y  1
//    / \    
// 1 A   B 1

noeq type heapnode : v:Type -> num_nodes:nat -> Type =
  | Leaf : #v:Type -> heapnode v 0
  | Node: #v:Type -> 
          left_nn:nat -> left:heapnode v left_nn -> 
          key:nat -> value:v -> 
          (right_nn:nat{right_nn <= left_nn}) -> right:(heapnode v right_nn) -> 
          heapnode v (left_nn + right_nn + 1)

let empty_heap (v:Type) = Leaf

//        0 
//      1  0
//      1  1
//      2  1            X
//                     / \
//                    A   Y
//                   /   /
//                  B   C'
//      2 2 

// We don't have any way to decrease_key for this heap implementation.
// So, we will have to allow the same value to be inserted multiple times,
// and just check in our matrix whether we've already found the minimum value for it.

// Insert in a balanced fashion.
let rec insert (#v:Type) (#nn:nat) (root:heapnode v nn) (key:nat) (value:v) 
 : (heapnode v (nn + 1)) =
  match root with 
  | Leaf -> Node 0 Leaf key value 0 Leaf
  | Node left_nn left nk nv right_nn right -> 
         if key < nk then (
             // replace the current node
             if left_nn <= right_nn then
                // move the old key and value to the left
                Node (left_nn + 1) 
                   (insert left nk nv) 
                    key value right_nn right
             else 
                // move the old key and value to the right
                Node left_nn left key value (right_nn + 1)
                   (insert right nk nv)
         ) else if left_nn <= right_nn then
             // insert on the left
             Node (left_nn + 1) 
                (insert left key value) 
                nk nv right_nn right
         else 
             // insert on the right
             Node left_nn left nk nv (right_nn + 1)
                (insert right key value)

// Remove the root node.  Compare the keys, and move
// the minimum value to the root, and then rebalance the tree.
//
//      X       
//     / \   
//    L   R
//   
// case 1: min is R, n(L) = n(R), move R's into X and push the "hole" down the right
// case 2: min is R, n(L) > n(R), move R
// 
let rec pop_min (#v:Type) (#nn:{nat>0}) (root:heapnode v nn) : ((heapnode v (nn-1))*nat*v) =
  match root with
  | Node 0 Leaf nk nv 0 Leaf -> (Leaf,nk,nv)
  | Node 1 left nk nv 0 Leaf -> (left,nk,nv)
  | Node left_nn (Node _ _ left_key left_value _ _) nk nv 
         right_nn (Node _ _ right_key right_value _ _) -> 
         if left_key < right_key 


let calc_part_1 (fn:string): ML unit =
  let fd = open_read_file fn in
    let m = parse_matrix fd in
      match m with
      | Matrix w h board ->
         let soln = find_minimum_path board in
           admit()

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"

