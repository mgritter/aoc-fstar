module Part1

open FStar.IO
open FStar.Printf
open FStar.All
open FStar.Int32
open FStar.Set

type line_coords = { x1:int; y1:int; x2:int; y2:int}
type point = { x:int; y:int}

let int32_to_int (n:Int32.t) : int =
  Int32.v n

let parse_comma_separated_numbers (s:string) : Tot (list int) =
  FStar.List.Tot.map (fun x -> (int32_to_int (Int32.of_string x))) (FStar.String.split [','] s)  

// 483,540 -> 845,178
let parse_line_coords (s:string) : ML line_coords =
  let nums = parse_comma_separated_numbers s in
    if FStar.List.length nums <> 4 then
       failwith "Bad coordinates"
    else
       { x1=(FStar.List.Tot.index nums 0);
         y1=(FStar.List.Tot.index nums 1);
         x2=(FStar.List.Tot.index nums 2);
         y2=(FStar.List.Tot.index nums 3) }       

let rec parse_input (fd:fd_read) : ML (list line_coords) =
   try
     let c = parse_line_coords (read_line fd) in
         c :: (parse_input fd)
   with
   | EOF -> []
   | _ -> failwith "unknown error"

let is_horizontal (line:line_coords) : bool =
   line.y1 = line.y2 

let is_vertical (line:line_coords) : bool =
   line.x1 = line.x2 

// n is between a and b, inclusive
let between (n:int) (a:int) (b:int) : bool =
   ( a <= n && n <= b ) ||
   ( b <= n && n <= a )

type point_on_line (line:line_coords) =
   (p:point{(is_horizontal line /\ between p.x line.x1 line.x2) \/
                        (is_vertical line /\ between p.y line.y1 line.y2)})
                        
let rec points_on_horizontal_line
      (line:line_coords{is_horizontal line}) 
      (x_p:int{between x_p line.x1 line.x2})
  :  Tot (list (point_on_line line))
     (decreases (abs (x_p - line.x2))) =
  let first_point : (point_on_line line) =
      { x = x_p; y = line.y1 } in
  if line.x1 < line.x2 then
     if x_p = line.x2 then
        [first_point]
     else   
        first_point :: 
        (points_on_horizontal_line line (x_p + 1))
  else
     if x_p = line.x2 then
        [first_point]
     else   
        first_point :: 
        (points_on_horizontal_line line (x_p - 1))

let rec points_on_vertical_line
      (line:line_coords{is_vertical line}) 
      (y_p:int{between y_p line.y1 line.y2})
  :  Tot (list (point_on_line line))
     (decreases (abs (y_p - line.y2))) =
  let first_point : (point_on_line line) =
      { x = line.x1; y = y_p } in
  if line.y1 < line.y2 then
     if y_p = line.y2 then
        [first_point]
     else   
        first_point :: 
        (points_on_vertical_line line (y_p + 1))
  else
     if y_p = line.y2 then
        [first_point]
     else   
        first_point :: 
        (points_on_vertical_line line (y_p - 1))

let points_on_line (l:line_coords) : (list (point_on_line l)) =
  if is_horizontal l then
     points_on_horizontal_line l l.x1
  else if is_vertical l then
     points_on_vertical_line l l.y1
  else
     []

type points_on_some_line = set (p:point{exists (l:line_coords) . point_on_line l})

// Can we add l1 <> l2?  How
type points_on_two_lines = set 
  (p:point{exists (l1:line_coords) (l2:line_coords) . point_on_line l1 /\ point_on_line l2 })

type list_of_dup_points = list
  (p:point{exists (l1:line_coords) (l2:line_coords) . point_on_line l1 /\ point_on_line l2 })

let rec process_points_on_line (l:line_coords) (ps:(list (point_on_line l))) 
  (s1:points_on_some_line) (s2:points_on_two_lines) (l2:list_of_dup_points)
  : Tot (points_on_some_line * points_on_two_lines * list_of_dup_points ) =
  match ps with 
  | [] -> (s1,s2 , l2)
  | p :: tl -> if mem p s1 then (
      if mem p s2 then
        process_points_on_line l tl s1 s2 l2       
      else
        let new_s2 = (union s2 (singleton p)) in 
          process_points_on_line l tl s1 new_s2 (p::l2)
    ) else
      process_points_on_line l tl (union s1 (singleton p)) s2 l2
    
let rec process_points (l:list line_coords) (s1:points_on_some_line) (s2:points_on_two_lines) (l2:list_of_dup_points)
 : Tot list_of_dup_points =
 match l with
 | [] -> l2
 | hd :: tl -> let ps = points_on_line hd in
     let new_sets = process_points_on_line hd ps s1 s2 l2 in
       process_points tl (new_sets._1) (new_sets._2) (new_sets._3)
      

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let coords = parse_input fd in
       let dup_points = process_points coords (empty) (empty) [] in
         print_string (sprintf "num of duplicate points: %d\n" 
                 (List.Tot.length dup_points))


// let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"
