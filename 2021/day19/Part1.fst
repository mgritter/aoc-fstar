module Part1

open FStar.String
open FStar.IO
open FStar.All
open FStar.Printf
open FStar.List.Tot

type beacon = {
  x: int;
  y: int;
  z: int
}

// Which axis the probe is facing
type orientation =
  | XPlus
  | XMinus
  | YPlus
  | YMinus
  | ZPlus
  | ZMinus

// The axes we're not facing can be in one of four rotations
// up is Y+, right is X+
// up is X-, right is Y+
// up is Y-, right is X-
// up is X+, right is Y-
type rotation =
  | PlusPlus
  | MinusPlus
  | MinusMinus
  | PlusMinus

type pos_and_dir = {
  // absolute position
  x: int;
  y: int;
  z: int;

  // absolute orientation
  axis: orientation;

  rot: rotation
}

type scanner = {
  id: nat;

  // relative offsets of beacons within range
  beacons: list beacon;

  position: (option pos_and_dir);

  // absolute offsets of beacons
  abs_beacons: list beacon
}

// scanner 0 is going to be fixed to be Z+
// with Y + as up  and X + as right
// So translate other beacon coordinates into that system

// Map the relative axis (x,y, or z) to our positive Z axis.
let permute_axis (axis:orientation) (relative:beacon) : Tot beacon =
  match axis with
  | ZPlus -> relative
  | ZMinus -> { x=0 - relative.x; y=relative.y; z = 0 - relative.z }
  | XPlus -> { x=0 - relative.z; y=relative.y; z=relative.x }
  | XMinus -> { x= relative.z; y=relative.y; z= 0 -relative.x }
  | YPlus -> { x = relative.x; y = relative.z; z = 0 -relative.y }  
  | YMinus -> { x = relative.x; y = 0 - relative.z; z = relative.y }  

let rotate_axis (rot:rotation) (relative:beacon) : Tot beacon =
  match rot with
  | PlusPlus -> relative
  // 90 degrees clockwise
  | PlusMinus -> { x = relative.y; y = 0 - relative.x; z = relative.z }
  // 180 degrees
  | MinusMinus -> { x = 0 - relative.x; y = 0 - relative.y; z = relative.z }
  // 270 degrees
  | MinusPlus -> { x = 0 - relative.y; y = relative.x; z = relative.z }

let to_absolute (p:pos_and_dir) (relative:beacon) : Tot beacon =
  let oriented = rotate_axis p.rot (permute_axis p.axis relative) in
    { x = oriented.x - p.x; 
      y = oriented.y - p.y; 
      z = oriented.z - p.z }

let to_absolute_is_invertible (p:pos_and_dir) (relative:beacon) :
  Lemma (exists (p_inv:pos_and_dir) . to_absolute p_inv (to_absolute p relative) = relative )
  = admit()  // TODO

type unplaced_scanner = (s:scanner{None? s.position /\ length s.abs_beacons = 0 })

type placed_scanner = (s:scanner{Some? s.position /\ 
                                s.abs_beacons = map (to_absolute (Some?.v s.position)) s.beacons})

// For each unplaced scanner U:  
// * Loop over the placed scanners P:
// * Loop over all 24 orientations
// * Loop over all U's beacons B1
// * Loop over all P's beacons B2
//   Assume B1 == B2, does that produce 12 matches?
//   If so, place U

// Given two lists of absolute beacon coordinates, do at least 12 match?
let rec at_least_n_matches (n:nat) (a1:list beacon) (a2:Set.set beacon) : Tot bool =
  if n = 0 then 
     true
  else match a1 with
  | [] -> false
  | hd::tl -> if Set.mem hd a2 then
     at_least_n_matches (n-1) tl a2 
   else
     at_least_n_matches n tl a2 

// ulib's as_set' is in the .fsti only, and we get the following error in OCaml:
// 169 |              FStar_Set.union (FStar_Set.singleton hd) (FStar_Set.as_set' tl))
//                                                              ^^^^^^^^^^^^^^^^^
// Error: Unbound value FStar_Set.as_set'
let rec as_set' (#a:eqtype) (l:list a) : Set.set a =
  match l with
  | [] -> Set.empty
  | hd::tl -> Set.union (Set.singleton hd) (as_set' tl)

let at_least_12_matches (a1:list beacon) (a2:list beacon) : Tot bool =
  at_least_n_matches 12 a1 (as_set' a2)

// Given an absolute beacon position and a relative beacon position,
// and a guessed orientation for the second scanner, determine the
// position of the second scanner
let assume_match (relative:beacon) (axis:orientation) (rot:rotation) (absolute:beacon) :
  Tot pos_and_dir =
  let oriented = rotate_axis rot (permute_axis axis relative) in
  {
     x=oriented.x - absolute.x; 
     y=oriented.y - absolute.y;
     z=oriented.z - absolute.z;
     axis=axis;
     rot=rot
  }

let match_is_inverse (absolute:beacon) (relative:beacon) (axis:orientation) (rot:rotation) :
  Lemma ( to_absolute (assume_match relative axis rot absolute) relative = absolute )
  = ()

let rec try_alternatives #a #c (in_list:list a) (does_it_work:a -> option c)
 : Tot (option c) =
 match in_list with
 | [] -> None
 | hd :: tl -> match does_it_work hd with
     | Some x -> Some x
     | None -> try_alternatives tl does_it_work

let try_to_find_matching_beacon (unplaced:unplaced_scanner) (placed:placed_scanner)     
    (axis:orientation) (rot:rotation) (relative1:beacon)
    : option pos_and_dir =
   try_alternatives placed.abs_beacons
      (fun absolute2 -> let p = assume_match relative1 axis rot absolute2 in
         if at_least_12_matches 
           (map (to_absolute p) unplaced.beacons)
           placed.abs_beacons then
             Some p
         else
           None)
               
let try_all_beacons (unplaced:unplaced_scanner) (placed:placed_scanner)     
    (axis:orientation) (rot:rotation) : option pos_and_dir = 
   try_alternatives unplaced.beacons
      (try_to_find_matching_beacon unplaced placed axis rot) 

let try_all_rot (unplaced:unplaced_scanner) (placed:placed_scanner)     
    (axis:orientation) : option pos_and_dir = 
   try_alternatives [PlusPlus; MinusPlus; MinusMinus; PlusMinus]
      (try_all_beacons unplaced placed axis) 
   
let try_all_axes (unplaced:unplaced_scanner) (placed:placed_scanner)     
    : option pos_and_dir = 
   try_alternatives [ZPlus; ZMinus; XPlus; XMinus; YPlus; YMinus] 
      (try_all_rot unplaced placed) 

let try_to_place (placed:list placed_scanner) 
    (unplaced:unplaced_scanner) : option pos_and_dir = 
    try_alternatives placed (try_all_axes unplaced)

let rec place_some_scanner (placed:list placed_scanner) 
    (unplaced:list unplaced_scanner) (prev:list unplaced_scanner)
  : Tot (option (placed_scanner * (list unplaced_scanner))) =
  match unplaced with
  | [] -> None
  | u :: tl -> match try_to_place placed u with
     | Some p -> Some ({id=u.id;
                      beacons=u.beacons;
                      position=Some p;
                      abs_beacons = map (to_absolute p) u.beacons},
                      append prev tl)
     | None -> place_some_scanner placed tl (snoc (prev,u))               

let int32_to_int (n:Int32.t) : int =
  Int32.v n

let parse_comma_separated_numbers (s:string) : list int =
  map (fun x -> (int32_to_int (Int32.of_string x))) (String.split [','] s) 

let parse_scanner (fd:fd_read) : ML unplaced_scanner =
  let first_line = (String.split [' '] (read_line fd)) in  
  if length first_line < 3 then
     failwith "Line too short"
  else
     let id = (int32_to_int (Int32.of_string (index first_line 2))) in
     if id < 0 then
       failwith "negative ID"
     else
     let rec parse_beacons (prev:list beacon) : ML unplaced_scanner =
       let line = read_line fd in
         if strlen line = 0 then
            { id=id;
              beacons=prev;
              position=None;
              abs_beacons=[] }
         else
           let csv = parse_comma_separated_numbers line in
             if length csv < 3 then
                failwith "too few coordinates"
             else
                // F* picked pos_and_dir instead of beacon 
                parse_beacons ((({
                   x=index csv 0;
                   y=index csv 1;
                   z=index csv 2
                }) <: beacon) :: prev)
      in parse_beacons []

let rec parse_scanners (fd:fd_read) : ML (list unplaced_scanner) =
  try 
   let s = parse_scanner fd in
      s :: (parse_scanners fd)
   with
     | EOF -> []
     | _ -> failwith "Unexpected error" 

let rec try_to_place_all_beacons (unplaced:list unplaced_scanner) (placed:list placed_scanner)
 : Tot (list placed_scanner) 
   (decreases length unplaced) =
   match place_some_scanner placed unplaced [] with
   | None -> placed
   | Some (p,up) -> 
       if length up >= length unplaced then
          placed
       else
          try_to_place_all_beacons up (p::placed)
   
let rec print_placed (placed:list placed_scanner) : ML unit =
  match placed with
  | [] -> ()
  | hd :: tl -> print_string (sprintf "ID=%d position (%d,%d,%d)\n"
               hd.id 
               (Some?.v hd.position).x 
               (Some?.v hd.position).y
               (Some?.v hd.position).z);
              print_placed tl


let rec print_beacons (beacons:list beacon) : ML unit =
  match beacons with
  | [] -> ()
  | hd :: tl -> print_string (sprintf "%d,%d,%d\n"
               hd.x hd.y hd.z);
              print_beacons tl

let debug01 (p0:placed_scanner) (p1:unplaced_scanner) : ML unit = 
    print_string "relative 1:\n";
    print_beacons (p1.beacons);
    List.iter(fun a ->
       List.iter (fun b ->
        let pd = { x=(68); y=(-1246); z=(-43); axis=a; rot=b} in
        print_string "\nabsolute 1:\n";
        print_beacons (map (to_absolute pd) (p1.beacons)))
       [PlusPlus; PlusMinus; MinusPlus; MinusMinus])
       [ZPlus; ZMinus; XPlus; XMinus; YPlus; YMinus]

let rec count_beacons (placed:list placed_scanner) (l_abs:list beacon) (s:Set.set beacon) (card_s:nat): Tot nat =
  match l_abs with
  | [] -> ( 
     match placed with
       | [] -> card_s
       | next :: remaining -> count_beacons remaining next.abs_beacons s card_s
  )
  | a :: rest ->
     if Set.mem a s then
        count_beacons placed rest s card_s
     else
        count_beacons placed rest (Set.union s (Set.singleton a)) (card_s + 1)
     
let calc_part_1 (fn:string) : ML unit =
   let fd = open_read_file fn in
      let scanners = parse_scanners fd in
        if length scanners < 2 then
           failwith "not enough scanners parsed"
        else
        let p0 = {
            x=0;
            y=0;
            z=0;
            axis=ZPlus;
            rot=PlusPlus
        } in
        let placed0 = {
          id=(hd scanners).id;
          beacons=(hd scanners).beacons;
          position=Some p0;
          abs_beacons = (map (to_absolute p0) (hd scanners).beacons)
        } in
        let placed = try_to_place_all_beacons 
           (tl scanners)
           [ placed0 ] in
        print_placed placed;
        if length placed < length scanners then
            print_string "Could not place all scanners!"
        else
            let c = count_beacons placed [] Set.empty 0 in
              print_string (sprintf "%d total beacons\n" c )

let _ = calc_part_1 "example.txt" 
let _ = calc_part_1 "input.txt" 

// FIXME: we're doing a lot of redundant comparisons, once we check 0 vs. N, we don't need to do
// it again on a later iteration.
