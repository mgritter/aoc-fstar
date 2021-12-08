module Part1

open FStar.Tactics
open FStar.IO
open FStar.Printf
open FStar.All
open FStar.String
open FStar.Int32
open FStar.List.Tot
  
// Hypothesis: the median value is the best meeting point
//  1000, 1, 1
//  999

let int32_to_int (n:Int32.t) : int =
  Int32.v n

// This is a workaround for the GitHub pretty-printer, which doesn't
// like single-quoted character values.
let comma = [FStar.Char.char_of_int 0x2c]

let parse_comma_separated_numbers (s:string) : Tot (list int) =
  FStar.List.Tot.map (fun x -> (int32_to_int (Int32.of_string x))) (FStar.String.split comma s)  

let rec summed_distance_to (l:list int) (meeting:int) : Tot nat =
  match l with
  | [] -> 0 
  | hd :: tl -> abs( hd  - meeting ) + summed_distance_to tl meeting

let summed_distance_based_on_count (l1:list int) (l2:list int) (meeting:int) :
 Lemma  (requires (forall x. count x l1 = count x l2))
        (ensures (summed_distance_to l1 meeting) = (summed_distance_to l2 meeting) ) =
   // maybe helpful?
   admit()

let num_lte (l:list int) (meeting:int) : nat =
  length (filter (fun x -> x <= meeting) l)

let num_gt (l:list int) (meeting:int) : nat =
  length (filter (fun x -> x > meeting) l)
  
let num_lt (l:list int) (meeting:int) : nat =
  length (filter (fun x -> x < meeting) l)

let num_gte (l:list int) (meeting:int) : nat =
  length (filter (fun x -> x >= meeting) l)

let num_eq (l:list int) (meeting:int) : nat =
  length (filter (fun x -> x = meeting) l)

let rec trichotomy (l:list int) (z:int)
 : Lemma (num_lt l z + num_gt l z + num_eq l z = length l) =
 match l with 
 | [] -> ()
 | hd :: tl -> trichotomy tl z

let rec summed_distance_to_neighbor_plus (l:list int) (meeting:int) :
  Lemma (ensures (summed_distance_to l (meeting+1)) = 
                 (summed_distance_to l meeting) +
                 (num_lte l meeting) - (num_gt l meeting )) =
  match l with 
  | [] -> ()
  | hd::tl -> 
     summed_distance_to_neighbor_plus tl meeting

let rec summed_distance_to_neighbor_minus (l:list int) (meeting:int) :
  Lemma (ensures (summed_distance_to l (meeting-1)) = 
                 (summed_distance_to l meeting) -
                 (num_lt l meeting) + (num_gte l meeting )) =
  match l with 
  | [] -> ()
  | hd::tl -> 
     summed_distance_to_neighbor_minus tl meeting

let rec sort_maintains_length #a (f:(a -> a -> Tot int)) (l:list a) 
 : Lemma (ensures (length l = length (sortWith f l))) 
         (decreases (length l)) =
  match l with
  | [] -> ()
  | pivot::tl ->
     let hi, lo = partition (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     sort_maintains_length f lo;
     sort_maintains_length f hi;
     append_length (sortWith f lo) (pivot::sortWith f hi)
 
let median (l:(list int){length l > 0}) : Tot int =
  let sorted = List.Tot.sortWith (fun x y -> x - y) l in
    let middle = (length sorted) / 2 in
       sort_maintains_length (fun x y -> x - y) l;
       index sorted middle

// 1 3 5 7
//   3 <- median may be the leftmost of the two middle elements
// 1 3 3 3 3 5
//     ^
//
let median_lemma (l:(list int){length l > 0})
 : Lemma (num_lt l (median l) = num_gt l (median l) /\ 
          num_lt l (median l) + 1 = num_gt l (median l) ) =
   admit()

// If the partition by < or > z is unbalanced, then we can improve the
// summed distance by moving in the corresponding direction.
let unbalanced_num_1 (l:list int{length l > 0}) (z:int)
 : Lemma (requires num_lt l z >= num_gte l z )
         (ensures summed_distance_to l z >= summed_distance_to l (z-1)) =   
   summed_distance_to_neighbor_minus l z

let unbalanced_num_2 (l:list int{length l > 0}) (z:int)
 : Lemma (requires num_lte l z <= num_gt l z )
         (ensures summed_distance_to l (z +1) <= summed_distance_to l z) =
   summed_distance_to_neighbor_plus l z

// If we move the target point, then lt and gt change as well
let rec change_partition (l:list int) (z:int)
 : Lemma (ensures num_lt l z <= num_lt l (z+1) /\
                  num_lte l z <= num_lte l (z+1) /\
                  num_gt l z >= num_gt l (z+1) /\
                  num_gte l z >= num_gte l (z+1))  =
   match l with
   | [] -> ()
   | hd :: tl -> change_partition tl z

#push-options "--z3rlimit 15"
let rec balanced_num_pos (l:list int{length l > 0}) (m:int) (z:int{z >= m})
 : Lemma (requires num_lt l m >= num_gte l m )
         (ensures num_lt l z >= num_gte l z /\ summed_distance_to l m <= summed_distance_to l z)
         (decreases (z-m)) =
   if m = z then
     ()
   else (
     balanced_num_pos l m (z-1);
     // num_lt l (z-1) >= num_gte l (z-1)
     // summed_distance_to l m <= summed_distance_to l (z-1)
     //
     // want to prove: summed_distance_to l z-1 <= summed_distance_to l z)
     // which is unbalanced_sum_1
     //
     // for that we need num_lt l z >= num_gte l z
     change_partition l (z-1);
     assert( num_lt l z >= num_lt l (z-1) );
     assert( num_gte l z <= num_gte l (z-1) ); 
     assert( num_lt l z >= num_gte l z );
     unbalanced_num_1 l z
   )

let rec balanced_num_neg (l:list int{length l > 0}) (m:int) (z:int{z <= m})
 : Lemma (requires num_lte l m <= num_gt l m )
         (ensures num_lte l z <= num_gt l z /\ summed_distance_to l m <= summed_distance_to l z)
         (decreases (m-z)) =
   if m = z then
     ()
   else (
     balanced_num_neg l m (z+1);
     change_partition l z;
     assert( num_lte l z <= num_lte l (z+1) );
     assert( num_gt l z >= num_gt l (z+1) ); 
     assert( num_gt l z >= num_lte l z );
     unbalanced_num_2 l z
   )
#pop-options

// OK, the two theorems above show that if the number of points equal to the median were zero,
// then all other points would be no better than m.  How can we expand this
// to including points equal to m?  (There must be at least one.)
// ... and, I still didn't solve the problem of demonstrating that the median as calculated
// actually has the property that numbers < m and numbers > m are balanced.
// (Defining exactly what that balance is seems difficult to due division rounding down, too.)

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let crabs = parse_comma_separated_numbers (read_line fd) in
      if length crabs = 0  then
        print_string "bad input"
      else
      let med = median crabs in
        let soln = summed_distance_to crabs med in
          print_string (sprintf "distance to %d is %d\n" med soln )

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"
