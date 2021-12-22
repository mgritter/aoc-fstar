module Part1

open FStar.IO
open FStar.Printf
open FStar.All

// Player 1 starting position: 2
// Player 2 starting position: 1

// Board positions are 1 through 10

type die_value = (n:nat{1 <= n /\ n <= 100})

type board_position = (n:nat{1 <= n /\ n <= 10})

let max_score : nat = 2000

type game_state = {
  player_1_score : (n:nat{n<max_score});
  player_1_position : board_position;
  player_2_score : (n:nat{n<max_score});
  player_2_position : board_position;

  turn : (n:nat{n = 1 \/ n = 2});

  // deterministic die cycles between 1 and 100
  next_die : die_value; 
  num_die_rolls: nat
}

let is_game_won (g:game_state) : bool =
  g.player_1_score >= 1000 || g.player_2_score >= 1000

let advance_die (d:die_value) : die_value =
  if d = 100 then 1 else  d + 1

let advance_position (p:board_position) 
  (d0:die_value) (d1:die_value) (d2:die_value) : board_position =
  let new_p = (p + d0 + d1 + d2) % 10 in
    if new_p = 0 then 10 else new_p

let player_1_move (g:game_state{g.turn=1 /\ g.player_1_score<1000}) : 
  (h:game_state{h.turn = 2 /\ h.num_die_rolls = g.num_die_rolls + 3 /\ 
               h.player_2_score = g.player_2_score /\
               h.player_2_position =g.player_2_position}) =
  let d0 = g.next_die in
  let d1 = advance_die d0 in
  let d2 = advance_die d1 in
  let next_d = advance_die d2 in
  let new_p = advance_position g.player_1_position d0 d1 d2 in
  let new_score = g.player_1_score + new_p in
  { g with player_1_score=new_score;
    player_1_position=new_p;
    turn=2;
    next_die=next_d;
    num_die_rolls = 3 + g.num_die_rolls }

let player_2_move (g:game_state{g.turn=2 /\ g.player_2_score <1000} ) : 
  (h:game_state{h.turn = 1 /\ h.num_die_rolls = g.num_die_rolls + 3 /\ 
               h.player_1_score = g.player_1_score /\
               h.player_1_position =g.player_1_position}) =
  let d0 = g.next_die in
  let d1 = advance_die d0 in
  let d2 = advance_die d1 in
  let next_d = advance_die d2 in
  let new_p = advance_position g.player_2_position d0 d1 d2 in
  let new_score = g.player_2_score + new_p in
  { g with player_2_score=new_score;
    player_2_position=new_p;
    turn=1;
    next_die=next_d;
    num_die_rolls = 3 + g.num_die_rolls }

let move (g:game_state{g.player_1_score < 1000 /\ g.player_2_score < 1000}) 
 : Tot (h:game_state{h.player_1_score > g.player_1_score \/
                     h.player_2_score > g.player_2_score}) =
  if g.turn = 1 then
     player_1_move g
  else
     player_2_move g

let rec play_until_target_score (g:game_state) 
  : Tot game_state
    (decreases 4000 - g.player_1_score - g.player_2_score) = 
  if g.player_1_score >= 1000 || g.player_2_score >= 1000 then
     g
  else
     let next_g = (move g) in (
       assert( g.player_1_score + g.player_2_score <
               next_g.player_1_score + next_g.player_2_score );
       play_until_target_score next_g
     )
     
let init : game_state = {
    player_1_score=0;
    player_2_score=0;
    player_1_position=2;
    player_2_position=1;
    turn=1;
    next_die=1;
    num_die_rolls=0
  }

let example : game_state = {
    player_1_score=0;
    player_2_score=0;
    player_1_position=4;
    player_2_position=8;
    turn=1;
    next_die=1;
    num_die_rolls=0
  }

let calc_part_1 () : ML unit = 
  let final = play_until_target_score init in
  print_string (sprintf "Player 1 position %d score %d\n" final.player_1_position final.player_1_score );
  print_string (sprintf "Player 2 position %d score %d\n" final.player_2_position final.player_2_score );
  print_string (sprintf "num dice rolls %d\n" final.num_die_rolls);
  print_string (sprintf "answer = %d\n" 
    (op_Multiply (min final.player_1_score final.player_2_score)
        final.num_die_rolls))
        
let _ = calc_part_1()

