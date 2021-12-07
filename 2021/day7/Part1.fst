module Part1

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

let parse_comma_separated_numbers (s:string) : Tot (list int) =
  FStar.List.Tot.map (fun x -> (int32_to_int (Int32.of_string x))) (FStar.String.split [','] s)  

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

let rec median_minimizes_distance (l:list int{length l > 0}) (z:int)
 : Lemma (summed_distance_to l z >= summed_distance_to l (median l)) =
   admit()

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
