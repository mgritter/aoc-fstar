module Part2

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

let y_coord_is_unchanged (ax:int) (p:point) :
  Lemma (ensures p.y = (fold_point_along_x ax p).y )
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

let rec folded_points_respects_visited (ff:point->point) (l:list point) (visited:Set.set point) (p:point)
  : Lemma (requires Set.mem p visited)
          (ensures ~ (List.Tot.mem p (fold_points ff l visited)))
  = match l with
    | [] -> ()
    | hd :: tl -> 
        if (ff hd) = p then (
           assert( fold_points ff tl visited =
                  fold_points ff l visited );
           folded_points_respects_visited ff tl visited p
        ) else if Set.mem (ff hd) visited then (
           folded_points_respects_visited ff tl visited p
        ) else (
           // assert( ~ ( Set.mem (ff hd) visited ) );
           folded_points_respects_visited ff tl 
                (Set.union visited (Set.singleton (ff hd))) p
           // ~ (List.Tot.mem p (fold_points ff tl (visited union ... )))
           //assert( ~(List.Tot.mem p ( (ff hd) :: (fold_points ff tl 
           //                         (Set.union visited (Set.singleton (ff hd)))))));
           //assert( (ff hd) :: (fold_points ff tl (Set.union visited 
           //                         (Set.singleton (ff hd)))) =
           //        (fold_points ff l visited) )
        )

let not_member_implies_count_0 (#a:eqtype) (l:list a) (v:a) :
  Lemma (requires ~ (List.Tot.mem v l))
        (ensures List.Tot.count v l = 0)
   = List.Tot.mem_count l v
   
let rec folded_points_are_deduplicated (ff:point->point) (l:list point) (visited:Set.set point) (p:point)
  : Lemma ( List.Tot.count p (fold_points ff l visited) <= 1 )
  = match l with 
    | [] -> ()
    | hd :: tl -> 
       let first_point = (ff hd) in
       let new_set = (Set.union visited (Set.singleton first_point)) in
       if Set.mem first_point visited then 
           folded_points_are_deduplicated ff tl visited p
       else if p = first_point then (
           folded_points_respects_visited ff tl new_set first_point;
           List.Tot.mem_count (fold_points ff tl new_set) p;
           assert( List.Tot.count p (fold_points ff tl new_set) = 0 )
       ) else (
           folded_points_are_deduplicated ff tl new_set p           
       )
    
let rec fold_in_order (folds:list (point->point)) (l:list point) : list point =
  match folds with 
  | [] -> l
  | ff :: tl ->
     let after = fold_points ff l Set.empty in
        fold_in_order tl after

// fold along y=7
// fold along x=5
let example1 : list (point->point) = [
  fold_point_along_y 7;
  fold_point_along_x 5  
]

let part1 : list (point->point) = [
  fold_point_along_x 655  
]

let part2 : list (point->point) = [
  fold_point_along_x 655;
  fold_point_along_y 447;
  fold_point_along_x 327;
  fold_point_along_y 223;
  fold_point_along_x 163;
  fold_point_along_y 111;
  fold_point_along_x 81;
  fold_point_along_y 55;
  fold_point_along_x 40;
  fold_point_along_y 27;
  fold_point_along_y 13;
  fold_point_along_y 6;  
]

// result will have height 6 and width 40

let rec print_list (l:list point) : ML unit = 
  match l with 
  | [] -> print_string "\n"
  | p :: tl -> (
    print_string (sprintf "(%d,%d) " p.x p.y );
    print_list tl
  )
  
let rec print_matrix (y:int) (x:int) (max_y:int) (max_x:int) (l:list point) : ML unit = 
  if List.Tot.mem ({x=x;y=y}) l then
    print_string "#"
  else
    print_string "." ;
  if x = max_x then (
    print_string "\n";
    if y = max_y then ()
    else 
      print_matrix (y+1) 0 max_y max_x l
  ) else 
      print_matrix y (x+1) max_y max_x l
     

let calc_part_2 (fn:string) (ffs: list (point->point)) : ML unit =
  let fd = open_read_file fn in
    let coords = parse_input fd in
       let result = fold_in_order ffs coords in
         print_string (sprintf "num points = %d\n" (List.Tot.length result));
         print_list result;
         print_matrix 0 0 6 40 result

let _ = calc_part_2 "example.txt" example1
let _ = calc_part_2 "input.txt" part2
