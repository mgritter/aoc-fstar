module Part1

open FStar.IO
open FStar.Printf
open FStar.All
open FStar.List.Tot
open FStar.List.Pure.Properties
open LeftistHeap

type amp =
  | Amber
  | Bronze
  | Copper
  | Desert

type position = (n:nat{n<=14})

(*
#############
#01 2 3 4 56#
###7#9#B#D###
  #8#A#C#E#
  #########
  *)
  
let neighbors (p:position) : (list position) =
  match p with
  | 0 -> [1]
  | 1 -> [0;2;7]
  | 2 -> [1;7;9;3]
  | 3 -> [2;9;11;4]
  | 4 -> [3;11;13;5]
  | 5 -> [4;13;6]
  | 6 -> [5]
  | 7 -> [1;2;8]
  | 8 -> [7]
  | 9 -> [2;3;10]
  | 10 -> [9]
  | 11 -> [3;4;12]
  | 12 -> [11]
  | 13 -> [4;5;14]
  | 14 -> [13]

let num_steps (from:position) (to:position) : nat = 
  let ordered_pair = if from < to then (from, to) else (to,from) in
  match ordered_pair with
  | (1,2) -> 2
  | (1,7) -> 2
  | (2,3) -> 2
  | (2,7) -> 2
  | (2,9) -> 2
  | (3,4) -> 2
  | (3,9) -> 2
  | (3,11) -> 2
  | (4,5) -> 2
  | (4,11) -> 2
  | (4,13) -> 2
  | (5,13) -> 2
  | _ -> 1

let rec distance (from:position) (to:position) : nat = 
  if from = to then 0 else  
  let ordered_pair = if from < to then (from, to) else (to,from) in
  assert( fst ordered_pair <= snd ordered_pair);
  match ordered_pair with
  | (x,8) -> 1 + distance x 7
  | (x,10) -> 1 + distance x 9
  | (x,12) -> 1 + distance x 11
  | (x,14) -> 1 + distance x 13
  | (x,7) -> 2 + min (distance x 1) (distance x 2) 
  | (x,9) -> 2 + min (distance x 2) (distance x 3) 
  | (x,11) -> 2 + min (distance x 3) (distance x 4) 
  | (x,13) -> 2 + min (distance x 4) (distance x 5) 
  | (0,1) -> 1
  | (0,6) -> 10
  | (0,x) -> 1 + op_Multiply 2 (x-1)
  | (1,6) -> 9
  | (1,x) -> op_Multiply 2 (x-1)
  | (2,6) -> 7
  | (2,x) -> op_Multiply 2 (x-2)
  | (3,6) -> 5
  | (3,x) -> op_Multiply 2 (x-3)
  | (4,6) -> 3
  | (4,5) -> 2
  | (5,6) -> 1
  

type amp_state = {
  color: amp;

  pos: position;  
  frozen: bool;  // cannot move again unless it can move into a room  
  finished: bool; // cannot move again
}

let is_home_position (a:amp_state) (p:position) : bool =
  match a.color with
  | Amber -> p = 7 || p = 8
  | Bronze -> p = 9 || p = 10
  | Copper -> p = 11 || p = 12
  | Desert -> p = 13 || p = 14

let some_home_position (a:amp_state) : position =
  match a.color with
  | Amber -> 7
  | Bronze -> 9
  | Copper -> 11
  | Desert -> 13

let inner_home_position (a:amp_state) : position =
  match a.color with
  | Amber -> 8
  | Bronze -> 10
  | Copper -> 12
  | Desert -> 14

let in_home_position (a:amp_state) : bool = is_home_position a a.pos

// Each position is occupied by an amp_state or None
type game_vec = (l:(list (option amp_state)){length l = 15})

type game_state =
  // Time to pick a new amp to move
  | PickNewAmp : (cost:nat) -> (v:game_vec) -> game_state

  // Move amp to a hallway position, freeze it when done, do not backtrack
  | MoveAmpToHallway : (cost:nat) -> (v:game_vec) -> (a:amp_state) -> (visited:list position) -> game_state

  // Move amp to one of its destination squares
  | MoveAmpToDest : (cost:nat) -> (v:game_vec) -> (a:amp_state) -> (visited:list position) -> game_state

let home_positions : list position = [ 7; 8; 9; 10; 11; 12; 13; 14 ]

let is_goal_state (g:game_state) : bool =
  match g with 
    | PickNewAmp _ v ->
       for_all (fun (a:option amp_state) -> Some? a && in_home_position (Some?.v a))
        (map (fun i -> index v i) home_positions)
    | _ -> false

let is_hallway (p:position) : bool = p <= 6

let step_cost (a:amp_state) : nat =
 match a.color with 
 | Amber -> 1
 | Bronze -> 10
 | Copper -> 100
 | Desert -> 1000

let has_only_matching_color (v:game_vec) (a:amp_state) 
  (p1:position) (p2:position) : bool = 
  match (index v p1, index v p2) with
  | (None,None) -> true
  | (None,Some x) -> x.color = a.color
  | (Some x,None) -> x.color = a.color
  | _ -> false
  
let is_home_available (v:game_vec) (a:amp_state) : bool =
  match a.color with
  | Amber -> has_only_matching_color v a 7 8  
  | Bronze -> has_only_matching_color v a 9 10
  | Copper -> has_only_matching_color v a 11 12
  | Desert -> has_only_matching_color v a 13 14

let replace_amp (g:game_vec) (old_pos:position) (new_state:amp_state) : game_vec =
  let (before, _, after) = split3 g old_pos in
    let after_delete = before @ (None :: after) in
      List.Pure.Properties.lemma_split3_length g old_pos;
      assert( length before = old_pos );
      assert( length (None::after) = 15 - old_pos);
      let (before, _, after) = split3 after_delete new_state.pos in
        List.Pure.Properties.lemma_split3_length after_delete new_state.pos;
        assert( length before = new_state.pos );
        assert( length ((Some new_state)::after) = 15 - new_state.pos );
        before @ ((Some new_state)::after)
  
let freeze_amp (g:game_vec) (a:amp_state) : game_vec =
  replace_amp g a.pos ({ a with frozen=true })

let finish_amp (g:game_vec) (a:amp_state) : game_vec =
  replace_amp g a.pos ({ a with finished=true })
  
let move_amp (g:game_vec) (a:amp_state) (p:position) : game_vec =
  replace_amp g a.pos ({ a with pos=p })

let move_amp2 (a:amp_state) (p:position) : amp_state =
  {a with pos=p}

// An admissible heuristic on moves
#push-options "--z3rlimit 15"
let heuristic (g:game_state) : nat =
  match g with
     | PickNewAmp c v 
     | MoveAmpToHallway c v _ _
     | MoveAmpToDest c v _ _ ->  
  fold_left (fun (t:nat) o ->
    match o with
    | None -> t
    | Some a -> t + (
      if in_home_position a then
        0
      else
      (op_Multiply (step_cost a) (distance a.pos (some_home_position a))))
    ) c v
#pop-options

let possible_moves (g:game_state) : Tot (list game_state) =
  match g with 
  | PickNewAmp c v -> 
     List.Tot.collect (fun oa ->
         match oa with
         | None -> []
         | Some a -> 
         if inner_home_position a = a.pos then
            [] // Do not move from the inner
         else if a.finished then
            [] // Do not move if we have solved it
         else if a.frozen then
            if is_home_available v a then
              // move to home only
              [MoveAmpToDest c v a [a.pos]]
            else
              // can't get to home, don't try
              []
         else // move to hallway first
            [MoveAmpToHallway c v a [a.pos]]
      ) v 
  | MoveAmpToHallway c v a visited ->
     // Forbid picking up an amp and then putting them down right away
     (if length visited < 2 then [] else
        [PickNewAmp c (freeze_amp v a)]) @
     List.Tot.collect (fun n ->
       if mem n visited then 
          [] // don't backtrack
       else if Some? (index v n) then
          [] // don't step on another amp
       else if mem n home_positions && (op_Negation (mem a.pos home_positions)) then
          [] // don't enter a home position unless we are in one already
       else [MoveAmpToHallway
              (c + op_Multiply (step_cost a) (num_steps a.pos n))
              (move_amp v a n)
              (move_amp2 a n)
              (n :: visited)]
     )
     (neighbors a.pos)
  | MoveAmpToDest c v a visited -> 
     (if in_home_position a && 
         Some? (index v (inner_home_position a )) then
       // Can stop if in a home position and the back home position is filled.
       [(PickNewAmp c (finish_amp v a))]
     else
       [])
     @
     (List.Tot.collect (fun n ->
       if mem n visited then 
          [] // don't backtrack
       else if Some? (index v n) then
          [] // don't step on another amp
       else if (mem n home_positions) && (op_Negation (is_home_position a n)) then
          [] // don't enter a home position other than our own
       else [MoveAmpToDest
              (c + op_Multiply (step_cost a) (num_steps a.pos n))
              (move_amp v a n)
              (move_amp2 a n)
              (n :: visited)]
     ) (neighbors a.pos))

(*
#############
#...........#
###D#A#D#C###
  #C#A#B#B#
  #########
*)

#push-options "--fuel 16"
let init_state : game_state =
  PickNewAmp 0 [
     None; // 0
     None; // 1
     None; // 2       
     None; // 3       
     None; // 4
     None; // 5
     None; // 6
     Some ({ color=Desert; pos=7; frozen=false;finished=false;});
     Some ({ color=Copper; pos=8; frozen=false;finished=false;});
     Some ({ color=Amber; pos=9; frozen=false;finished=false;});
     Some ({ color=Amber; pos=10; frozen=false;finished=false;});
     Some ({ color=Desert; pos=11; frozen=false;finished=false;});
     Some ({ color=Bronze; pos=12; frozen=false;finished=false;});
     Some ({ color=Copper; pos=13; frozen=false;finished=false;});
     Some ({ color=Bronze; pos=14; frozen=false;finished=false;});
   ]     

(*
#############
#...........#
###B#C#B#D###
  #A#D#C#A#
  #########
  *)
  
let example_state : game_state =
  PickNewAmp 0 [
     None; // 0
     None; // 1
     None; // 2       
     None; // 3       
     None; // 4
     None; // 5
     None; // 6
     Some ({ color=Bronze; pos=7; frozen=false;finished=false;});
     Some ({ color=Amber; pos=8; frozen=false;finished=false;});
     Some ({ color=Copper; pos=9; frozen=false;finished=false;});
     Some ({ color=Desert; pos=10; frozen=false;finished=false;});
     Some ({ color=Bronze; pos=11; frozen=false;finished=false;});
     Some ({ color=Copper; pos=12; frozen=false;finished=false;});
     Some ({ color=Desert; pos=13; frozen=false;finished=false;});
     Some ({ color=Amber; pos=14; frozen=false;finished=false;});
   ]     

let trivial_state : game_state =
  PickNewAmp 0 [
     None; // 0
     None; // 1
     None; // 2       
     None; // 3       
     None; // 4
     None; // 5
     None; // 6
     Some ({ color=Amber; pos=7; frozen=false;finished=false;});
     Some ({ color=Amber; pos=8; frozen=false;finished=false;});
     Some ({ color=Bronze; pos=9; frozen=false;finished=false;});
     Some ({ color=Bronze; pos=10; frozen=false;finished=false;});
     Some ({ color=Desert; pos=11; frozen=false;finished=false;});
     Some ({ color=Copper; pos=12; frozen=false;finished=false;});
     Some ({ color=Copper; pos=13; frozen=false;finished=false;});
     Some ({ color=Desert; pos=14; frozen=false;finished=false;});
   ]     
#pop-options

let print_vec (i:int) (o:option amp_state) : ML unit = 
  // print_string (sprintf " %d:" i);
  match o with 
  | None -> print_string "-"
  | Some a ->
  match a.color with
  | Amber -> print_string (if a.frozen then "a" else "A")
  | Bronze -> print_string (if a.frozen then "b" else "B")
  | Copper -> print_string (if a.frozen then "c" else "C")
  | Desert -> print_string (if a.frozen then "d" else "D")
    
let print_state (h:int) (g:game_state) : ML unit =
  match g with
  | PickNewAmp c v -> 
      print_string (sprintf "%d %d pick " h c);
      List.iteri print_vec v;
      print_string "\n"
  | MoveAmpToHallway c v a visited ->
      print_string (sprintf "%d %d move_hall %d " h c a.pos);
      List.iteri print_vec v;
      print_string "\n"
  | MoveAmpToDest c v a visited ->
      print_string (sprintf "%d %d move_dest %d " h c a.pos);
      List.iteri print_vec v;
      print_string "\n"

let test_part_1 () : ML unit = 
  let c1 = possible_moves init_state in
    List.iter (fun g1 -> 
       print_state 0 g1;
       print_string "-------------\n";
       List.iter (print_state 0) (possible_moves g1);
       print_string "\n"
       )
    c1

let rec insert_all (gs:list game_state) (#npl:int_1) (q:heapnode game_state npl) 
  : ((n:int_1) & (heapnode game_state n)) =
  match gs with 
  | [] -> (| npl, q |)
  | hd :: tl -> 
     let h = heuristic hd in
        insert_all tl (dsnd (insert q h hd))

// For uniqueness, check only the state not the cost,
// we will visit each state only in the minimum-cost way to get there
let zero_cost_state (g:game_state) : game_state =
  match g with
  | PickNewAmp c v -> PickNewAmp 0 v
  | MoveAmpToHallway c v a d -> MoveAmpToHallway 0 v a d
  | MoveAmpToDest c v a d -> MoveAmpToDest 0 v a d
  
let rec insert_all_2 (gs:list game_state) (s:Set.set game_state) 
 : (Set.set game_state) = 
  match gs with
  | [] -> s
  | hd :: tl -> 
    insert_all_2 tl (Set.union s (Set.singleton (zero_cost_state hd)))

let rec filter_already_visited (gs:list game_state) (s:Set.set game_state)
 : (list game_state) =
 match gs with
 | [] -> []
 | hd :: tl -> 
   if (Set.mem (zero_cost_state hd) s) then
     filter_already_visited tl s
   else
     hd :: (filter_already_visited tl s)

let rec find_minimum 
  (#npl:int_1) (queue:heapnode game_state npl) 
  (visited:Set.set game_state)  
  : ML (option game_state)
  = if npl < 0 then
      None
    else match pop_min queue with
    | MinValue cost g npl_root new_root ->
    if is_goal_state g then
       Some g
    else (
       print_state (heuristic g) g;
       let next_gs = possible_moves g in
       let new_gs = filter_already_visited next_gs visited in
       let next_q = insert_all new_gs new_root in
       let next_s = insert_all_2 new_gs visited in
         find_minimum (dsnd next_q) (next_s)
    )

let calc_part_1 (i:game_state) : ML unit = 
  match find_minimum (singleton_heap 0 i) (Set.singleton i) with
  | None -> print_string "No solution found\n"
  | Some g -> print_string "solution found!\n";
      print_state 0 g
    
let _ = calc_part_1 init_state


