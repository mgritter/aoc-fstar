module Part2

open FStar.Map
open FStar.String
open FStar.Char
open FStar.IO
open FStar.Printf
open FStar.All

let input : list (string*string) = [
"yw","MN";
"wn","XB";
"DG","dc";
"MN","wn";
"yw","DG";
"start","dc";
"start","ah";
"MN","start";
"fi","yw";
"XB","fi";
"wn","ah";
"MN","ah";
"MN","dc";
"end","yw";
"fi","end";
"th","fi";
"end","XB";
"dc","XB";
"yw","XN";
"wn","yw";
"dc","ah";
"MN","fi";
"wn","DG"
]

let example1 : list (string*string) = [
"start","A";
"start","b";
"A","c";
"A","b";
"b","d";
"A","end";
"b","end"
]

let example2 : list (string*string) = [
"dc","end";
"HN","start";
"start","kj";
"dc","start";
"dc","HN";
"LN","dc";
"HN","end";
"kj","sa";
"kj","HN";
"kj","dc"
]

type adj_map = (Map.t string (list string))

let empty_map () : adj_map =
  restrict Set.empty (const [])

let append_to_map (m:adj_map) (k:string) (v:string) : adj_map =
  if contains m k then
     upd m k (v :: (sel m k))
  else
     upd m k [v]

let ccA : char_code  = u32_of_char 'A'
let ccZ : char_code  = u32_of_char 'Z'

let is_big (cave:string) : bool =
  if strlen cave = 0 then
    true
  else
    let chars = list_of_string cave in
      let c = u32_of_char (List.Tot.hd chars) in
          UInt32.gte c ccA && UInt32.lte c ccZ

let is_little (cave:string) : bool =
  op_Negation (is_big cave)

let rec create_adjacency_map (l:list (string*string)) :  adj_map =
  match l with
  | [] -> empty_map ()
  | (s,t) :: tl ->
    let m = create_adjacency_map tl in 
      append_to_map
        (append_to_map m s t)
        t s

val fold_left: ('a -> 'b -> Dv 'a) -> 'a -> list 'b -> Dv 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl
  
let rec count_paths (m:adj_map) (curr:string) 
  (visited:Set.set (s:string{is_little s})) 
  (visited2:option (s:string{is_little s}))
  : Dv nat =
  if curr = "end" then
    1
  else if ( is_little curr && Set.mem curr visited && Some? visited2) then
    0
  else if ( is_little curr && curr = "start" && Set.mem curr visited ) then
    0
  else let neighbors = sel m curr in
    let new_visited2 =
      if is_little curr && Set.mem curr visited then (
         assert( None? visited2 );
         Some curr
      ) else visited2 
    in let new_visited = 
      if is_little curr then 
         Set.union (Set.singleton curr) visited
      else 
         visited
    in let visit_neighbor (tot:nat) (n:string) : Dv nat =
      tot + (count_paths m n new_visited new_visited2)
    in
      fold_left visit_neighbor 0 neighbors 

let rec count_paths_tot (max_length:nat) (m:adj_map) (curr:string) 
  (visited:Set.set (s:string{is_little s})) 
  (visited2:option (s:string{is_little s}))
  : Tot nat =
  if max_length = 0 then
    0
  else if curr = "end" then
    1
  else if ( is_little curr && Set.mem curr visited && Some? visited2) then
    0
  else if ( is_little curr && curr = "start" && Set.mem curr visited ) then
    0
  else let neighbors = sel m curr in
    let new_visited2 =
      if is_little curr && Set.mem curr visited then (
         assert( None? visited2 );
         Some curr
      ) else visited2 
    in let new_visited = 
      if is_little curr then 
         Set.union (Set.singleton curr) visited
      else 
         visited
    in let visit_neighbor (tot:nat) (n:string) : Tot nat =
      tot + (count_paths_tot (max_length - 1) m n new_visited new_visited2)
    in
      List.Tot.fold_left visit_neighbor 0 neighbors 

let rec tail_implies_subset (#a:eqtype) (l:(list a){Cons? l}) :
  Lemma ( Set.subset (Set.as_set (List.Tot.tl l)) (Set.as_set l)) =
   ()

let rec count_paths_decreases (m:adj_map) (curr:string) (visited2:option (s:string{is_little s}))
  (x:Set.set (s:string{is_little s})) (y:Set.set (s:string{is_little s}))
  (max_path_len:nat)
 : Lemma (ensures Set.subset x y ==> count_paths_tot max_path_len m curr x visited2 
            <= count_paths_tot max_path_len m curr y visited2 )
         (decreases max_path_len) =
   if max_path_len = 0 then
     ()
   else
     // TODO: show that the fold gives a sum of the recursive calls
     // then apply induction to each of those calls?
     count_paths_decreases m curr visited2 x y (max_path_len - 1);
     admit()

let solve_part_2 (input:list (string*string)) : ML unit =
  let m = create_adjacency_map input in
    let count = count_paths m "start" Set.empty None in
      print_string (sprintf "%d paths\n" count)

let _ = solve_part_2 example1
let _ = solve_part_2 example2
let _ = solve_part_2 input
  


    
