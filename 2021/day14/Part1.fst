module Part1

open FStar.IO
open FStar.All
open FStar.String
open FStar.Map
open FStar.Printf

type rule =
 | Rule : first:char -> second:char -> result:char -> rule

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

let find_rule (rules:list rule) (c0:char) (c1:char) : (option (x:rule{Rule?.first x = c0 && Rule?.second x = c1})) =
  List.Tot.find (fun (r:rule) -> Rule?.first r = c0 && Rule?.second r = c1) rules

// Question: how does F* know that this return value is nonempty, and so the result
// can be fed back into single_step?
let rec single_step (polymer:(list char){Cons? polymer}) (rules:list rule) : (list char) =
  match polymer with
  | c0 :: c1 :: rest -> (
      match find_rule rules c0 c1 with
      | None -> c0 :: (single_step (c1::rest) rules)
      | Some r -> c0 :: (Rule?.result r) :: (single_step (c1::rest) rules)      
  )
  | c0 :: [] -> [c0]

let rec multiple_steps (n:nat) (polymer:(list char){Cons? polymer}) (rules:list rule) 
  : (list char) =
  if n = 0 then polymer
  else multiple_steps (n-1) (single_step polymer rules) rules

let all_elements : list char = ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L'; 'M'; 'N'; 'O'; 'P'; 'Q'; 'R'; 'S'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z']

let rec count_elements_aux (l:list char) (m:Map.t char nat) : (Map.t char nat) =
  match l with
  | [] -> m
  | hd :: tl -> count_elements_aux tl (upd m hd (1 + (sel m hd)))  

let count_elements (l:list char) : (Map.t char nat) =
  count_elements_aux l (Map.const 0)

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

let calc_part_1 (fn:string) (start:string) : ML unit =
  let fd = open_read_file fn in
    let rules = parse_input fd in
       let init = list_of_string start in
       if List.Tot.length init = 0 then
         print_string "length too short"
       else
       let result10 = multiple_steps 10 (list_of_string start) rules in
       let counts = count_elements result10 in
       let min_count = min_element all_elements counts in
       let max_count = max_element all_elements counts in
          print_string (sprintf "length %d min %d max %d answer=%d\n"
              (List.Tot.length result10) min_count max_count
              (max_count - min_count))
          
let _ = calc_part_1 "example.txt" "NNCB"
let _ = calc_part_1 "input.txt" "KFVHFSSVNCSNHCPCNPVO"
