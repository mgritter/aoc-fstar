module Part3

open FStar.IO
open FStar.Printf
open FStar.All

open BoatEffect
open Boat

let update_x (x:int) : BOAST unit
  (requires (fun _ -> True))
  (ensures (fun b0 _ b1 -> b1.x = x /\ b0.y = b1.y /\ b0.heading = b1.heading))
  = let r = get_coords() in 
     set_coords ({r with x=x}) // needs parentheses to parse

let update_y (y:int) : BOAST unit
  (requires (fun _ -> True))
  (ensures (fun b0 _ b1 -> b1.y = y /\ b0.x = b1.x /\ b0.heading = b1.heading))
  = let r = get_coords() in 
     set_coords ({r with y=y}) // needs parentheses to parse

let update_h (h:bearing) : BOAST unit
  (requires (fun _ -> True))
  (ensures (fun b0 _ b1 -> b1.heading = h /\ b0.x = b1.x /\ b0.y = b1.y))
  = let r = get_coords() in 
     set_coords ({r with heading=h}) // needs parentheses to parse
     

//  0
//  ^
//  |
//  |
//  o--> 90 
// 

let left (b:bearing) : Boat unit = 
  let c = get_coords() in
    update_h (( c.heading - b ) % 360)

let right (b:bearing) : Boat unit =
  let c = get_coords() in
    update_h (( c.heading + b ) % 360)

let north (l:int) : BOAST unit 
  (requires (fun _ -> True ))
  (ensures (fun h0 _ h1 -> h0.x = h1.x /\ h0.heading = h1.heading )) =
  let c = get_coords() in
    update_y (c.y + l)

let south (l:int) : BOAST unit 
  (requires (fun _ -> True ))
  (ensures (fun h0 _ h1 -> h0.x = h1.x /\ h0.heading = h1.heading )) =
  let c = get_coords() in
    update_y (c.y - l)

let east (l:int) : BOAST unit 
  (requires (fun _ -> True ))
  (ensures (fun h0 _ h1 -> h0.y = h1.y /\ h0.heading = h1.heading )) =
  let c = get_coords() in
    update_x (c.x + l)

let west (l:int) : BOAST unit 
  (requires (fun _ -> True ))
  (ensures (fun h0 _ h1 -> h0.y = h1.y /\ h0.heading = h1.heading )) =
  let c = get_coords() in
    update_x (c.x - l)

let forward (l:int) : Boat unit =
  let c = get_coords() in
  match c.heading with
  | 0 -> north l
  | 90 -> east l
  | 180 -> south l
  | 270 -> west l

let manhattan_distance (x:int) (y:int) : int =
  abs x + abs y

let ship_distance () : Boat int =
  let c = get_coords() in
  manhattan_distance c.x c.y

let init_boat () : Boat unit =
  set_coords initial_state

let example () : Boat unit =
 forward 10;
 north 3;
 forward 7;
 right 90;
 forward 11

// FStar.IO uses the ALL_h template instantiated with heap.
let print_distance () : ML unit =
  init_boat();
  example();
  // navigate();
  let d = ship_distance() in
    print_string (sprintf "%d\n" d)

let _ = print_distance()
