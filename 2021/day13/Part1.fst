module Part1

open FStar.IO
open FStar.All
open FStar.Printf

type point = { x:int; y:int }

let int32_to_int (n:Int32.t) : int =
  Int32.v n

let parse_comma_separated_numbers (s:string) : Tot (list int) =
  FStar.List.Tot.map (fun x -> (int32_to_int (Int32.of_string x))) (FStar.String.split [','] s)  

let parse_point (s:string) : ML point =
  let nums = parse_comma_separated_numbers s in
    if FStar.List.length nums <> 2 then
       failwith "Bad coordinates"
    else
       { x=(FStar.List.Tot.index nums 0);
         y=(FStar.List.Tot.index nums 1) }

let rec parse_input (fd:fd_read) : ML (list point) =
   try
     let c = parse_point (read_line fd) in
         c :: (parse_input fd)
   with
   | EOF -> []
   | _ -> failwith "unknown error"

//   ----------------|-----------------
//       X          <-Y
//       X

let fold_point_along_x (ax:int) (p:point) : point =
    if p.x <= ax then
      p
    else
      { y=p.y; x= (ax - (abs (p.x-ax))) }

let fold_point_along_y (ay:int) (p:point) : point =
    if p.y <= ay then
      p
    else
      { x=p.x; y= (ay - (abs (p.y-ay))) }

let distance_from_axis_is_unchanged (ax:int) (p:point) :
  Lemma (ensures abs (ax - p.x) = abs (ax - (fold_point_along_x ax p).x) )
  = ()

let rec fold_points (fold_func : point->point) (l:list point) (visited:Set.set point) : list point =
  match l with 
  | [] -> []
  | hd :: tl ->
     let new_point = fold_func hd in
       if Set.mem new_point visited then
          fold_points fold_func tl visited
       else
          new_point :: ( fold_points fold_func tl (Set.union visited (Set.singleton new_point)))

let rec fold_in_order (folds:list (point->point)) (l:list point) : list point =
  match folds with 
  | [] -> l
  | ff :: tl ->
     let after = fold_points ff l Set.empty in
        fold_in_order tl after

// Unusual warning:
// (Warning 290) SMT may not be able to prove the types of folds at <input>(61,23-61,28) (Prims.list (_: Part1.point -> Prims.Tot Part1.point)) and folds at <input>(61,23-61,28) (Prims.list (_: Part1.point -> Prims.Tot Part1.point)) to be equal, if the proof fails, try annotating these with the same type

// fold along y=7
// fold along x=5
let example1 : list (point->point) = [
  fold_point_along_y 7;
  fold_point_along_x 5  
]

let part1 : list (point->point) = [
  fold_point_along_x 655  
]

let calc_part_1 (fn:string) (ffs: list (point->point)) : ML unit =
  let fd = open_read_file fn in
    let coords = parse_input fd in
       let result = fold_in_order ffs coords in
         print_string (sprintf "num points = %d\n" (List.Tot.length result))

let _ = calc_part_1 "example.txt" example1
let _ = calc_part_1 "input.txt" part1
