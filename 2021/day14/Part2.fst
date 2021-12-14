module Part2

open FStar.IO
open FStar.All
open FStar.String
open FStar.Map
open FStar.Printf

// PP -> B
// pair PP -> PB BP

type rule =
 | Rule : first:char -> second:char -> result:char -> rule

type polymer = Map.t (char*char) nat

let rec string_to_polymer_aux (c:list char) (p:polymer) : polymer =
  match c with
  | [] -> p
  | hd :: [] -> p
  | a :: b :: tl ->
     string_to_polymer_aux (b :: tl) 
       (upd p (a,b) (1 + (sel p (a,b))))

let string_to_polymer (s:string) : polymer =
  string_to_polymer_aux (list_of_string s) (Map.const 0)
  
let parse_rule (s:string) : ML rule =
  let elements = String.list_of_string s in
    if FStar.List.length elements <> 7 then
       failwith "Bad rule"
    else
       Rule (FStar.List.Tot.index elements 0) (FStar.List.Tot.index elements 1) (FStar.List.Tot.index elements 6)

let rec parse_input (fd:fd_read) : ML (list rule) =
   try
     let c = parse_rule (read_line fd) in
         c :: (parse_input fd)
   with
   | EOF -> []
   | _ -> failwith "unknown error"

let rec single_step (rules:list rule) (p:polymer) (new_p:polymer) 
  : polymer =
  match rules with 
  | [] -> new_p
  | r :: tl -> 
    let old_count = sel p (Rule?.first r, Rule?.second r) in
      // A B  -> AC  CB
      let pair1 = (Rule?.first r, Rule?.result r) in
      let pair2 = (Rule?.result r, Rule?.second r) in
      let new_count1 = upd new_p pair1 (old_count + (sel new_p pair1)) in
      let new_count2 = upd new_count1 pair2 
                       (old_count + (sel new_count1 pair2)) in
         single_step tl p new_count2
      
let rec multiple_steps (n:nat) (p:polymer) (rules:list rule) 
  : polymer =
  if n = 0 then p
  else multiple_steps (n-1) (single_step rules p (Map.const 0)) rules

let all_elements : list char = ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L'; 'M'; 'N'; 'O'; 'P'; 'Q'; 'R'; 'S'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z']

let rec product (a:list char) (b:list char) : (list (char*char)) =
  match a with 
  | [] -> []
  | hd :: tl ->
      List.Tot.append 
        (List.Tot.map (fun x -> (hd,x)) b)
        (product tl b)
      
let all_pairs : list (char*char) = product all_elements all_elements

let rec count_elements_aux (pairs:list (char*char)) (p:polymer) (m:Map.t char nat) : (Map.t char nat) =
  match pairs with
  | [] -> m
  | pair :: tl ->
        let pair_count = sel p pair in
          let m1 = (upd m (fst pair) (pair_count + (sel m (fst pair)))) in
            let m2 = (upd m1 (snd pair) (pair_count + (sel m1 (snd pair)))) in
               count_elements_aux tl p m2

let halve_all_counts (m:Map.t char nat) : (Map.t char nat) =
    map_val #nat #nat (fun x -> x / 2) m

let count_elements (p:polymer) (init:(list char){Cons? init}): (Map.t char nat) =
  // The polymer has pairs, but we want to count individual elements.
  // ABC = AB BC, so B / 2 is correct, but A / 2 and C / 2 are not correct. 
  let fc = List.Tot.index init 0 in
  let lc = List.Tot.index init (List.Tot.length init - 1) in
  // FIXME: what if they're both the same character?
  let adjusted_count = (upd (upd (Map.const 0) fc 1) lc 1) in
  let doubled_count = count_elements_aux all_pairs p adjusted_count in
  halve_all_counts doubled_count

let rec orig_count_elements_aux (l:list char) (m:Map.t char nat) : (Map.t char nat) =
  match l with
  | [] -> m
  | hd :: tl -> orig_count_elements_aux tl (upd m hd (1 + (sel m hd)))  

let orig_count_elements (l:list char) : (Map.t char nat) =
  orig_count_elements_aux l (Map.const 0)

// TODO
let counts_are_equivalent (l:(list char){Cons? l}) :
  Lemma (ensures Map.equal
         (orig_count_elements l) 
         (count_elements (string_to_polymer_aux l (Map.const 0)) l)) =
         admit()

let rec min_element (l:(list char){Cons? l}) (m:Map.t char nat) : nat =
  match l with
  | [x] -> sel m x
  | hd :: tl -> let min = min_element tl m in
      let hd_count = sel m hd in
        if hd_count = 0 then
           min
        else if hd_count < min || min = 0 then
           hd_count
        else 
           min

let rec max_element (l:(list char){Cons? l}) (m:Map.t char nat) : nat =
  match l with
  | [x] -> sel m x
  | hd :: tl -> let max = max_element tl m in
      let hd_count = sel m hd in
        if hd_count = 0 then
           max
        else if hd_count > max then
           hd_count
        else 
           max

let calc_part_2 (fn:string) (start:string) : ML unit =
  let fd = open_read_file fn in
    let rules = parse_input fd in
       let init = list_of_string start in
       if List.Tot.length init = 0 then
         print_string "length too short"
       else
       let init_polymer = string_to_polymer start in 
       let polymer40 = multiple_steps 40 init_polymer rules in
       let counts = count_elements polymer40 init in
       let min_count = min_element all_elements counts in
       let max_count = max_element all_elements counts in
          print_string (sprintf "min %d max %d answer=%d\n"
              min_count max_count
              (max_count - min_count))
          
let _ = calc_part_2 "example.txt" "NNCB"
let _ = calc_part_2 "input.txt" "KFVHFSSVNCSNHCPCNPVO"
