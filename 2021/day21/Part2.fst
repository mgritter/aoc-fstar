module Part2

open FStar.IO
open FStar.Printf
open FStar.All

// Player 1 starting position: 2
// Player 2 starting position: 1

// Board positions are 1 through 10

// Die is 1 through 3
// Play is to 21 points

// Player 1 wins if they get t

// Number of states: 10 * 10 board positions
// 21 * 21 scores
// Max score is 10, so we can win from 11, and have
// to handle scores up to 30

let state_space = op_Multiply (op_Multiply 31 31) (op_Multiply 10 10)
let max_score : nat = 30

// For example, the state p1 = 5 and p2 = X and score1 = 13 and score2 = Y 
// has predecessors
//  p1 = 5 - 3     1 way             
//  p1 = 5 - 4     3 ways
//  p1 = 5 - 5     1+1+3 1+3+1 3+1+1 2+2+1 2+1+2 2+2+2 6 ways
// The previous score must always have been 8

type die_value = (n:nat{1 <= n /\ n <= 3})

type board_position = (n:nat{1 <= n /\ n <= 10})

let reverse_position (p:board_position) (sum_of_three_dice:nat) : board_position =
  let new_p = (p - sum_of_three_dice) % 10 in
    if new_p = 0 then 10 else new_p

// G.f. (x+x^2+x^3 = 
// x^9 + 3 x^8 + 6 x^7 + 7 x^6 + 6 x^5 + 3 x^4 + x^3

// Returns the number of ways to get from a source board
// position to "dest" by rolling 3d3, in order
let backwards_3d3_distribution (dest:board_position) 
 : list (board_position*nat) =
    [ (reverse_position dest 3,1);
      (reverse_position dest 4,3);
      (reverse_position dest 5,6);
      (reverse_position dest 6,7);
      (reverse_position dest 7,6);
      (reverse_position dest 8,3);
      (reverse_position dest 9,1)
      ]

type game_state = {
  player_1_score : (n:nat{n<=max_score});
  player_1_position : board_position;
  player_2_score : (n:nat{n<=max_score});
  player_2_position : board_position;  
}

type to_index (g:game_state) : (n:nat{n<state_space}) =
  g.player_1_score +
  op_Multiply (max_score + 1) ( 
    g.player_2_score +
    op_Multiply (max_score+1) (
       (g.player_1_position-1) +
          op_Multiply 10 (g.player_2_position-1)))

type from_index (n:nat{n<state_space}) : (g:game_state) =
  { player_1_score = n % (max_score + 1);
    player_2_score = (n / (max_score + 1)) % (max_score + 1);
    player_1_position = (n / (max_score+1) / (max_score + 1)) % 10 + 1;
    player_2_position = (n / (max_score+1) / (max_score + 1) / 10) + 1
    }

let shift_and_mod (s:nat{s>0}) (m:nat{m>0}) (x:nat{x<m})
 : Lemma( ( op_Multiply x s ) / s % m = x)
 = Math.Lemmas.cancel_mul_div x s;
   assert( ( op_Multiply x s ) / s  = x);
   Math.Lemmas.small_mod x m;
   ()

let shift_and_mod2 (m:nat{m>0}) (x:nat{x<m}) (higher_digits:nat)
 : Lemma( (( op_Multiply higher_digits m ) + x) % m = x ) =
   Math.Lemmas.lemma_div_mod_plus x higher_digits m;
   Math.Lemmas.small_mod x m

let cancel_mul_div2 (a:nat) (n:nat{n>0}) (b:nat{b<n}): Lemma (((op_Multiply a n) + b) / n = a) = 
  Math.Lemmas.lemma_div_plus b a n;
  Math.Lemmas.small_div b n

#push-options "--z3rlimit 60"
let index_is_invertible_1 (g:game_state) :
 Lemma( (from_index (to_index g)).player_1_score = g.player_1_score) = 
 assert( (to_index g) % (max_score + 1) = g.player_1_score );
 ()

let index_is_invertible_2 (g:game_state) :
 Lemma( (from_index (to_index g)).player_2_score = g.player_2_score) = 
 ()
#pop-options

// TODO: prove correctness
let index_is_invertible (g:game_state) :
 Lemma( (from_index (to_index g)) = g) = 
 admit()
 

let predecessor_states_1 (g:game_state) : 
  (list (game_state * nat)) =
  if g.player_2_score >= 21 then
    [(g,1)]  // other player already one!  No move for player 1.
  else
    // If player 1 has won, then keep that count around
    // (but do not split the timeline.)
    List.Tot.append (if g.player_1_score >= 21 then [(g,1)] else [])
    (let previous_score = g.player_1_score - g.player_1_position in
       if previous_score < 0 then
         [] // impossible
       else if previous_score >= 21 then
         [] // player 1 can't move after winning
       else
         List.Tot.map
           (fun (pos_weight) ->
             ({ g with
               player_1_score=previous_score;
               player_1_position=(fst pos_weight);               
             },snd pos_weight)
           )
         (backwards_3d3_distribution g.player_1_position))

let predecessor_states_2 (g:game_state) : 
  (list (game_state * nat)) =
  if g.player_1_score >= 21 then
    [(g,1)]  // other player already won!  No move for player 2.
  else
    // If player 2 has won, then keep that count around
    List.Tot.append (if g.player_2_score >= 21 then [(g,1)] else [])
    (let previous_score = g.player_2_score - g.player_2_position in
       if previous_score < 0 then
         [] // impossible
       else if previous_score >= 21 then
         [] // player 2 can't move after winning
       else
         List.Tot.map
           (fun (pos_weight) ->
             ({ g with
               player_2_score=previous_score;
               player_2_position=(fst pos_weight);               
             },snd pos_weight)
           )
         (backwards_3d3_distribution g.player_2_position))

// To prove: if predecessor G returns H, then there is a move from G to H
// or they are the same and one player has won.

type player = (turn:nat{turn = 1 \/ turn=2})

let predecessor_states (turn:player) (g:game_state) : 
  (list (game_state * nat)) =
  if turn = 1 then
    predecessor_states_1 g
  else
    predecessor_states_2 g

type state_counts = (counts:(list nat){List.Tot.length counts = state_space})

// This is an improved version of mapi that provides a refinement on the index
// value (so it is within range) and guarantees the length matches.
// 
// using snoc seemed to be slower than this non-tail-recursive version
let rec mapi_init #a #b (orig:list a) (x:list a)
  (f:(n:nat{n < List.Tot.length orig}) -> a -> Tot b)
  (i:nat{i = List.Tot.length orig - List.Tot.length x})
: Tot (l:(list b){List.Tot.length l = List.Tot.length x}) =
match x with 
  | [] -> []
  | hd :: tl -> (f i hd) :: mapi_init orig tl f (i+1)

let mapi #a #b (l:list a) (f:(n:nat{n < List.Tot.length l}) -> a -> Tot b) 
 : Tot (ol:(list b){List.Tot.length ol = List.Tot.length l})
  = mapi_init l l f 0 

let transition_all_universes (turn:player) (counts:state_counts) : state_counts =
  let add_predecessors (i:nat{i<state_space}) c : nat =
    let this_universe : game_state = from_index i in
      let predecessor_universes = predecessor_states turn this_universe in
        FStar.List.Tot.fold_left #nat
          (fun tot (pred:(game_state*nat))  -> 
             (tot + 
             op_Multiply (snd pred) (List.Tot.index counts (to_index (fst pred)))) <: nat)
        0 predecessor_universes       
  in
  mapi counts add_predecessors

let is_game_won (g:game_state) : bool =
  g.player_1_score >= 21 || g.player_2_score >= 21


let rec all_universes_finished (i:nat) (counts:state_counts) 
: Tot bool (decreases state_space - i) =
  if i >= state_space then
     true
  else
     let c = List.Tot.index counts i in
       if c = 0 then
         all_universes_finished (i+1) counts
       else
         let g = from_index i in 
            if op_Negation (is_game_won g) then
               false
            else
               all_universes_finished (i+1) counts

let rec show_states (i:nat) (counts:state_counts) : ML unit = 
  if i >= state_space then 
    ()
  else
     let c = List.Tot.index counts i in
       if c = 0 then
         show_states (i+1) counts
       else
         let g = from_index i in 
            print_string (sprintf "[%d] %d: p1 score %d position %d, p2 score %d position %d\n"
                          i c g.player_1_score g.player_1_position g.player_2_score g.player_2_position );
            show_states (i+1) counts


let rec win_count (i:nat) (counts:state_counts) (p1:nat) (p2:nat) 
: Tot (nat*nat) (decreases state_space - i) =
  if i >= state_space then
     (p1,p2)
  else
     let c = List.Tot.index counts i in
       if c = 0 then
          win_count (i+1) counts p1 p2
       else
         let g = from_index i in 
            if g.player_1_score >= 21 then
               win_count (i+1) counts (p1+c) p2
            else
               win_count (i+1) counts p1 (p2+c)

let rec play_until_universes_finished (turn:player) (counts:state_counts) : ML state_counts =
  show_states 0 counts;
  if all_universes_finished 0 counts then
     counts
  else (
     print_string "next time step!\n";
     play_until_universes_finished 
       (if turn = 1 then 2 else 1)
       (transition_all_universes turn counts)
  )
  
let init : game_state = {
    player_1_score=0;
    player_2_score=0;
    player_1_position=2;
    player_2_position=1;
  }

let example : game_state = {
    player_1_score=0;
    player_2_score=0;
    player_1_position=4;
    player_2_position=8;
  }

let rec zero_vector (n:nat): (l:(list nat){List.Tot.length l = n}) =
  if n = 0 then [] else
  0 :: zero_vector (n-1)

let rec single_one (n:nat) (pos:nat{pos<n}) : (l:(list nat){List.Tot.length l = n}) =
  if pos = 0 then 1 :: (zero_vector (n-1))
  else 0 :: single_one (n-1) (pos-1)

let init_vector (g:game_state) : state_counts =
  single_one state_space (to_index g)

let calc_part_2 () : ML unit = 
  let init = init_vector init in
  let final = play_until_universes_finished 1 init in
  let counts = win_count 0 final 0 0 in
  print_string (sprintf "Player 1: %d\n" (fst counts));
  print_string (sprintf "Player 2: %d\n" (snd counts))
        
let _ = calc_part_2()

