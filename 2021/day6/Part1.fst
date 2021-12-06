module Part1

open FStar.IO
open FStar.Printf
open FStar.All
open FStar.Int32
open FStar.List.Tot
open FStar.Tactics
     
let int32_to_int (n:Int32.t) : int =
  Int32.v n

let parse_comma_separated_numbers (s:string) : Tot (list int) =
  FStar.List.Tot.map (fun x -> (int32_to_int (Int32.of_string x))) (FStar.String.split [','] s)  

let vector (a:Type) (len:nat) = (l:(list a){length l = len})

type fish_population = vector nat 9

let fish_step (p:fish_population) : fish_population =
  let new_state = [ 
    index p 1;  // 0
    index p 2;  // 1
    index p 3;  // 2
    index p 4;  // 3
    index p 5;  // 4
    index p 6;  // 5
    index p 7 + index p 0;  // 6' = 7' + 0'
    index p 8;  // 7
    index p 0 ]  // 8 
  in 
    assert_norm( length new_state = 9 );
    new_state

let nat_add (x:nat) (y:nat) : nat = x + y 

let sum (p:list nat) : nat =
  List.Tot.fold_left nat_add 0 p 

let is_zero (n:nat) = n = 0

let rec sum_is_zero_if_all_zeros (p: list nat) :
  Lemma (requires (sum p = 0))
        (ensures (for_all is_zero p))
   = match p with 
     | [] -> ()
     | hd :: tl ->
         fold_left_monoid nat_add 0 tl;
         assert( is_zero 0 );
         assert( sum tl = 0 );
         sum_is_zero_if_all_zeros tl
  
// The rare occasion when fuel helps!  We need to get to the 8th element,
// the operation fails with default fuel.
#push-options "--fuel 10 --ifuel 10"
let zero_population_gives_zero (p:fish_population) 
: Lemma (requires (sum p = 0))
        (ensures (sum (fish_step p) ) = 0)
   = sum_is_zero_if_all_zeros p; 
     assert( index p 0 = 0 ); 
     assert( index p 1 = 0 );
     assert( index p 2 = 0 );
     assert( index p 3 = 0 );
     assert( index p 4 = 0 );
     assert( index p 5 = 0 );
     assert( index p 6 = 0 );
     assert( index p 7 = 0 );
     assert( index p 8 = 0 );     
     ()
#pop-options

let rec fish_step_n (n:nat) (p:fish_population) : fish_population =
  if n = 0 then p else
  fish_step_n (n-1) (fish_step p)

let rec lemma_splitAt_fst_length (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires (n <= length l))
    (ensures (length (fst (splitAt n l)) = n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_fst_length (n-1) l'
  
let split3_recombine (l:list nat) (i:nat{i<length l}) (replacement:nat) 
                     (before:list nat) (orig:nat) (after:list nat)
 : Lemma (requires split3 l i = (before, orig, after) )
         (ensures length (before  @ [replacement] @ after) = length l)
     = assert( (before, orig :: after) = splitAt i l);
       lemma_splitAt_snd_length i l;       
       lemma_splitAt_fst_length i l;       
       assert( length (orig::after)  =  length l - i );
       assert( length (replacement::after)  =  length l - i );
       assert( length before = i );
       append_length [replacement] after;       
       append_length before (append [replacement] after);
       ()
 
let rec list_to_pop_aux (l:list int) (p:fish_population) : fish_population =
  match l with 
  | [] -> p
  | hd :: tl -> if hd < 0 then
      list_to_pop_aux tl p
    else if hd >= length p then
      list_to_pop_aux tl p
    else
      let before, n, after = split3 p hd in
        let new_pop = before @ [n+1] @ after in
           split3_recombine p hd (n+1) before n after;
           list_to_pop_aux tl new_pop

let list_to_pop (l:list int) : fish_population =
  let zero_pop = [0;0;0;0;0;0;0;0;0] in
    assert_norm( length zero_pop = 9 );
    list_to_pop_aux l zero_pop

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let fish = parse_comma_separated_numbers (read_line fd) in
      let initial_pop = list_to_pop fish  in
        let fish_step_18 = sum( fish_step_n 18 initial_pop ) in 
        let fish_step_80 = sum( fish_step_n 80 initial_pop ) in
        let fish_step_256 = sum( fish_step_n 256 initial_pop ) in
          print_string (sprintf "after 18 days = %d\n" fish_step_18 );
          print_string (sprintf "after 80 days = %d\n" fish_step_80 );
          print_string (sprintf "after 256 days = %d\n" fish_step_256 )

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"





