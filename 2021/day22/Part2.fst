module Part2

open FStar.IO
open FStar.Printf
open FStar.All
open FStar.List.Tot
open FStar.Classical
  
// We're going to iterate over all the cells
// run through the list of instructions for each one
// and determine its final state

type cube_state =
 | On
 | Off
 
type reboot_step = {
 value: cube_state; 
 x_min: int;
 x_max: (n:int{n>=x_min});
 y_min: int;
 y_max: (n:int{n>=y_min});
 z_min: int;
 z_max: (n:int{n>=z_min}); 
}


let max x y = if x >= y then x else y

let intersects (s1:reboot_step) (s2:reboot_step) : bool =
  // exists (x,y,z) such that 
  //  s1.x_min <= x <= s1.x_max and s2.x_min <= x <= s2.x_max 
  // 
  s1.x_min <= s2.x_max && s2.x_min <= s1.x_max &&
  s1.y_min <= s2.y_max && s2.y_min <= s1.y_max &&
  s1.z_min <= s2.z_max && s2.z_min <= s1.z_max

let intersect_with (c1:reboot_step) (c2:reboot_step{intersects c1 c2}) : reboot_step =
  { value=c1.value;
    x_min= max c1.x_min c2.x_min;
    x_max= min c1.x_max c2.x_max;
    y_min= max c1.y_min c2.y_min;
    y_max= min c1.y_max c2.y_max;
    z_min= max c1.z_min c2.z_min;
    z_max= min c1.z_max c2.z_max
    }

let area (c:reboot_step) : nat =
  op_Multiply 
    (c.x_max - c.x_min + 1)
    (op_Multiply 
      (c.y_max - c.y_min + 1)
      (c.z_max - c.z_min + 1))

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

let intersect_model (s1:reboot_step) (s2:reboot_step) 
 : Lemma  ( requires intersects s1 s2 )
          ( ensures 
           (exists x y z . (point_in_step x y z s1) /\ (point_in_step x y z s2 )))
 = let x0 = min s1.x_max s2.x_max in
   let y0 = min s1.y_max s2.y_max in
   let z0 = min s1.z_max s2.z_max in    
    assert(point_in_step x0 y0 z0 s1);
    assert(point_in_step x0 y0 z0 s2)

let intersect_lowers_area (c1:reboot_step) (c2:reboot_step)
 : Lemma ( requires intersects c1 c2) 
         ( ensures (area (intersect_with c1 c2)) <= (area c1) /\
                   (area (intersect_with c1 c2)) <= (area c2))
  = let i = intersect_with c1 c2 in 
    assert (i.x_max <= c1.x_max);
    assert (i.x_max <= c2.x_max);
    assert (i.y_max <= c1.y_max);
    assert (i.y_max <= c2.y_max);
    assert (i.z_max <= c1.z_max);
    assert (i.z_max <= c2.z_max);
    
    assert (i.x_min >= c1.x_min); 
    assert (i.x_min >= c2.x_min);
    assert (i.y_min >= c1.y_min);
    assert (i.y_min >= c2.y_min);
    assert (i.z_min >= c1.z_min);
    assert (i.z_min >= c2.z_min);

    assert ( (i.x_max - i.x_min) <= (c1.x_max - c1.x_min) ); 
    assert ( (i.x_max - i.x_min) <= (c2.x_max - c2.x_min) );
    assert ( (i.y_max - i.y_min) <= (c1.y_max - c1.y_min) );
    assert ( (i.y_max - i.y_min) <= (c2.y_max - c2.y_min) );
    assert ( (i.z_max - i.z_min) <= (c1.z_max - c1.z_min) );
    assert ( (i.z_max - i.z_min) <= (c2.z_max - c2.z_min) );

    assert ( (i.x_max - i.x_min) >= 0);
    assert ( (i.y_max - i.y_min) >= 0);
    assert ( (i.z_max - i.z_min) >= 0);
            
    admit()  // TODO: finish

let rec trim_to (bounding:reboot_step) (cs : list reboot_step )
 : Tot (l:(list reboot_step){length l <= length cs}) =
 match cs with 
 | [] -> []
 | hd::tl -> if intersects hd bounding then
    (intersect_with hd bounding) :: (trim_to bounding tl)
  else
    trim_to bounding tl

let trim_to_preserves_value (c1:reboot_step) (c2:reboot_step)
 : Lemma (requires intersects c2 c1)
         (ensures length (trim_to c1 [c2]) = 1 /\
                  (hd (trim_to c1 [c2])).value = c2.value )
                  = ()

let rec trim_limits_area (bb:reboot_step) (cs:list reboot_step) 
: Lemma ( for_all (fun c -> area c <= area bb) (trim_to bb cs))
  = match cs with
    | [] -> ()
    | hd :: tl -> 
      if intersects hd bb then (
        intersect_lowers_area hd bb;
        trim_limits_area bb tl
      ) else (
        trim_limits_area bb tl
      )

(*
steps processed in forward order

+ A     // light up all of A
- B     // turn off anything already lit in A
+ C     // light up everything in C that is not already lit in (A,B)
- D     // turn off anything already lit in (A,B,C)
+ E     // light up everyting in E not already list in (A,B,C,D)
*)

// TODO: prove that the result is actually a nat!

let rec count_cubes (steps:list reboot_step) (prev_steps:list reboot_step) 
: Tot int
  (decreases %[(length steps + length prev_steps);(length steps)])=
  match steps with
  | [] -> 0
  | c :: tl ->
    lemma_snoc_length (prev_steps,c);
    if Off? c.value then (
       0
       - (count_cubes (trim_to c prev_steps) [] )       
       + (count_cubes tl (snoc (prev_steps,c)))
    ) else
       (area c)
       - (count_cubes (trim_to c prev_steps) [] )       
       + (count_cubes tl (snoc (prev_steps,c)))

let count_cubes_lemma1 (c:reboot_step) :
  Lemma (requires On? c.value )
        (ensures count_cubes [c] [] = area c)
  = ()

let count_cubes_lemma2 (c:reboot_step) :
  Lemma (requires Off? c.value )
        (ensures count_cubes [c] [] = 0)
  = ()

let count_cubes_lemma3 (c:reboot_step) :
  Lemma (requires On? c.value )
        (ensures count_cubes [c] [c] = 0)
  = ()

let count_cubes_lemma4 (c1:reboot_step) (c2:reboot_step) :
  Lemma (requires On? c1.value /\ On? c2.value /\ intersects c2 c1)
        (ensures count_cubes [c1;c2] [] = 
           (area c1) + (area c2) - (area (intersect_with c2 c1))
        )
  = ()

let count_cubes_lemma5 (c1:reboot_step) (c2:reboot_step) :
  Lemma (requires On? c1.value /\ Off? c2.value /\ intersects c2 c1)
        (ensures count_cubes [c1;c2] [] = 
           (area c1) - (area (intersect_with c2 c1))
        )
  = ()


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
       if index coords 1 >= index coords 0 &&
          index coords 3 >= index coords 2 &&
          index coords 5 >= index coords 4 then       
       Some ({
         value = v;
         x_min = index coords 0;
         x_max = index coords 1;
         y_min = index coords 2;
         y_max = index coords 3;
         z_min = index coords 4;
         z_max = index coords 5;
       })
       else 
       None // invalid region (zero area)
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

let rec combinations_2 #a (l: list a) : (list (a*a)) =
  match l with
  | [] -> []
  | hd :: tl -> List.Tot.append
     (List.Tot.map (fun x -> (hd,x)) tl)
     (combinations_2 tl)

let calc_part_2 (fn:string) : ML unit =
  let fd = open_read_file fn in
  let steps = read_steps fd in
  let count = count_cubes steps [] in
      print_string (sprintf "Cubes on: %d\n" count)

let debug_part_2 (fn:string) : ML unit =
  let fd = open_read_file fn in
  let steps = read_steps fd in
  if length steps < 2 then
    print_string "input_too_short"
  else
  let c0 = index steps 0 in
  let c1 = index steps 1 in  
  let count = count_cubes [c0; c1] [] in
      print_string (sprintf "area c0 = %d\n" (area c0));
      print_string (sprintf "area c1 = %d\n" (area c1));
      if intersects c0 c1 then
        print_string (sprintf "area c0 intersect c1 = %d\n" (area (intersect_with c0 c1)))
      else ();
      print_string (sprintf "Cubes on: %d\n" count)
    
let _ = calc_part_2 "example2.txt"
let _ = calc_part_2 "input.txt"


// No!  bad Mark!  Off-by-one error below!

// on x=-5..47,y=-31..22,z=-19..33   area = 143312
// on x=-44..5,y=-27..21,z=-14..35   area = 115248

// both:
//    x=-5..5,y=-27..21,z  -14..33  area = 22560
  
