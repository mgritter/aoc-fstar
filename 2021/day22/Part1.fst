module Part1

open FStar.IO
open FStar.Printf
open FStar.All
open FStar.List.Tot

let coord = (x:int{-50 <= x /\ x <= 50} )

let num_cells = 1030301

// We're going to iterate over all the cells
// run through the list of instructions for each one
// and determine its final state

type cube_state =
 | On
 | Off
 
type reboot_step = {
 value: cube_state; 
 x_min: int;
 x_max: int;
 y_min: int;
 y_max: int;
 z_min: int;
 z_max: int; 
}

let point_in_step (x:int) (y:int) (z:int) (step:reboot_step) : bool =
 step.x_min <= x && x <= step.x_max &&
 step.y_min <= y && y <= step.y_max &&
 step.z_min <= z && z <= step.z_max

let point_in_step_model (x:int) (y:int) (z:int) (step:reboot_step) 
 : Lemma (
   x < step.x_min \/ x > step.x_max \/
   y < step.y_min \/ y > step.y_max \/
   z < step.z_min \/ z > step.z_max ==>
   point_in_step x y z step = false)
   =()


let rec apply_rules (x:int) (y:int) (z:int) (curr:cube_state) (steps:list reboot_step) : 
 Tot cube_state (decreases steps) =
  match steps with
  | [] -> curr
  | hd :: tl -> if point_in_step x y z hd then
      apply_rules x y z (hd.value) tl
   else
      apply_rules x y z curr tl

let apply_rules_fast (x:int) (y:int) (z:int) (def:cube_state) (steps:list reboot_step) :
  Tot cube_state = 
  match find (point_in_step x y z) (rev steps) with
  | Some s -> s.value
  | None -> def

let rec fast_is_same (x:int) (y:int) (z:int) (def:cube_state) (steps:list reboot_step) 
 : Lemma (ensures apply_rules_fast x y z def steps =
          apply_rules x y z def steps )
        (decreases steps)
 = admit()

let rec count_cubes (curr_x:coord) (curr_y:coord) (curr_z:coord) (steps:list reboot_step) (cubes_on:nat) :
 Tot nat 
 (decreases %[50-curr_x;50-curr_y;50-curr_z]) =
 let is_on = (if Off? (apply_rules_fast curr_x curr_y curr_z Off steps) then 0 else 1) in
   if curr_z = 50 then
     if curr_y = 50 then
       if curr_x = 50 then
         // end of loop
         cubes_on + is_on
       else
         count_cubes (curr_x + 1) (-50) (-50) steps (cubes_on + is_on)
     else
         count_cubes curr_x (curr_y+1) (-50) steps (cubes_on + is_on)
   else
       count_cubes curr_x curr_y (curr_z+1) steps (cubes_on + is_on)

let int32_to_int (n:Int32.t) : int =
  Int32.v n

let parse_on_or_off (s:string) : option cube_state =
  if s = "on" then Some On 
  else if s = "off" then Some Off
  else None
  
let parse_comma_separated_numbers (s:string) : list int =
  map (fun x -> (int32_to_int (Int32.of_string x))) (String.split [','] s) 

let parse_step (s:string) : option reboot_step =
  let toks = String.split [','] s in
  if length toks < 7 then 
     None
  else match parse_on_or_off (index toks 0) with
  | None -> None
  | Some v -> (
     let coords =  map (fun x -> (int32_to_int (Int32.of_string x))) (tl toks) in
       Some ({
         value = v;
         x_min = index coords 0;
         x_max = index coords 1;
         y_min = index coords 2;
         y_max = index coords 3;
         z_min = index coords 4;
         z_max = index coords 5;
       })
  )

let rec read_steps (fd:fd_read) : ML (list reboot_step) =  
   try
     let line = read_line fd in
       match parse_step line with
       | None -> failwith ( "parsing error on line " ^ line )
       | Some s -> s :: (read_steps fd)
   with
   | EOF -> []
   | _ -> failwith "unknown error"

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
  let steps = read_steps fd in
  if length steps = 0  then
    print_string "no steps\n"
  else
  let count = count_cubes (-50) (-50) (-50) steps 0 in
    print_string (sprintf "Cubes on: %d\n" count)
    
let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"


  
