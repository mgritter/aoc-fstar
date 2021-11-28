module Part2

open FStar.IO
open FStar.Heap
open FStar.ST
open FStar.Printf
open FStar.All
open FStar.Tactics
  
// Waypoint relative coordinates
val wx : ref int
let wx = ST.alloc 10

val wy : ref int
let wy = ST.alloc 1

type bearing = (h:int{h = 0 \/ h = 90 \/ h = 180 \/ h = 270})

// Ship coordinates
val sx : ref int
let sx = ST.alloc 0

val sy : ref int
let sy = ST.alloc 0


//  0       (0,x)
//  ^
//  |
//  |
//  o--> 90     (x,0)
// 

// (x,0) -> (0,x)
// (0,y) -> (-y,0)

let left_rotate (b:bearing) (o:int*int) : (int*int) =
  let ox = fst o in
  let oy = snd o in
  match b with 
  | 0 -> (oy, ox)
  | 90 -> (0 - oy, ox)
  | 180 -> (0 - ox, 0 - oy)
  | 270 -> (oy, 0 - ox)

let right_rotate (b:bearing) (o:int*int) : (int*int) =
  let ox = fst o in
  let oy = snd o in
  match b with 
  | 0 -> (oy, ox)
  | 90 -> (oy, 0 - ox)
  | 180 -> (0 - ox, 0 - oy)
  | 270 -> (0 - oy, ox)

let left_and_right_are_inverses (b:bearing) (x:int) (y:int) : Lemma
  (ensures (left_rotate b (right_rotate b (x,y))) = (x,y))
 = ()

let left (b:bearing) : St unit =
  let r = left_rotate b (!wx, !wy) in
    wx := fst r;
    wy := snd r

let right (b:bearing) : St unit =
  let r = right_rotate b (!wx, !wy) in
    wx := fst r;
    wy := snd r

let north (l:int) : ST unit 
  (requires (fun _ -> True ))
  (ensures (fun h0 _ h1 -> modifies (only wy) h0 h1)) =
  wy := ( !wy + l )

let south (l:int) : ST unit
  (requires (fun _ -> True ))
  (ensures (fun h0 _ h1 -> modifies (only wy) h0 h1)) =
  wy := ( !wy - l )

let east (l:int) : ST unit
  (requires (fun _ -> True ))
    (ensures (fun h0 _ h1 -> modifies (only wx) h0 h1)) =
  wx := ( !wx + l )

let west (l:int) : ST unit
  (requires (fun _ -> True ))
    (ensures (fun h0 _ h1 -> modifies (only wx) h0 h1)) =
  wx := ( !wx - l )

let forward (l:int) : St unit =
  sx := (!sx + op_Multiply l !wx);
  sy := (!sy + op_Multiply l !wy)

let manhattan_distance (x:int) (y:int) : int =
  abs x + abs y

let ship_distance () : St int = 
  manhattan_distance !sx !sy

val navigate : unit -> St unit

let example () : St unit =
 forward 10;
 north 3;
 forward 7;
 right 90;
 forward 11

#set-options "--z3rlimit 120"
let navigate () : St unit =
 west 4
; north 5
; forward 23
; east 1
; left 90
; north 5
; forward 62
; west 2
; left 90
; forward 56
; west 1
; left 90
; west 1
; south 4
; forward 69
; right 90
; forward 40
; right 90
; forward 86
; south 4
; forward 94
; north 4
; right 180
; forward 2
; west 4
; right 90
; south 5
; right 180
; west 3
; south 1
; east 2
; forward 79
; right 90
; south 4
; left 90
; north 5
; forward 6
; left 90
; north 2
; forward 92
; right 90
; west 2
; right 90
; forward 99
; east 2
; forward 72
; west 4
; south 3
; right 90
; west 4
; left 90
; west 2
; south 3
; forward 89
; west 2
; north 1
; forward 27
; left 90
; south 1
; right 90
; forward 14
; north 4
; left 90
; north 2
; forward 23
; west 4
; left 90
; forward 18
; north 1
; right 180
; forward 92
; north 1
; left 90
; forward 32
; south 1
; left 180
; north 4
; west 5
; south 1
; east 4
; north 2
; right 90
; south 2
; right 90
; east 1
; forward 89
; right 90
; south 5
; forward 5
; forward 16
; north 3
; forward 68
; right 90
; north 4
; left 180
; forward 22
; north 2
; right 90
; south 5
; right 180
; east 3
; forward 68
; right 90
; forward 55
; left 90
; forward 4
; east 4
; forward 87
; east 1
; left 90
; left 180
; south 1
; west 5
; south 1
; south 5
; west 3
; forward 67
; north 5
; south 3
; forward 37
; west 2
; forward 48
; south 2
; left 180
; south 3
; right 90
; east 5
; left 90
; forward 3
; right 90
; north 3
; west 5
; left 90
; north 1
; forward 85
; right 180
; north 5
; right 90
; west 5
; south 3
; left 180
; east 5
; north 3
; forward 35
; right 180
; west 2
; forward 54
; north 4
; left 180
; forward 90
; south 3
; east 5
; forward 34
; west 2
; right 270
; forward 24
; east 2
; forward 71
; right 90
; forward 66
; west 4
; south 3
; forward 47
; south 2
; left 270
; forward 69
; north 5
; forward 91
; west 5
; left 90
; east 1
; south 1
; left 270
; forward 91
; west 3
; north 4
; east 1
; forward 52
; right 90
; north 4
; forward 17
; north 1
; forward 27
; right 90
; north 4
; west 2
; right 90
; west 2
; forward 84
; west 2
; forward 13
; right 90
; west 4
; north 2
; right 90
; west 5
; forward 52
; left 90
; east 3
; forward 49
; right 90
; west 1
; right 90
; forward 93
; right 90
; east 5
; forward 34
; left 90
; forward 72
; south 2
; left 90
; east 1
; right 90
; forward 12
; east 2
; north 2
; left 90
; forward 28
; left 180
; east 5
; right 180
; east 4
; right 180
; forward 43
; north 3
; forward 85
; west 4
; south 3
; east 5
; right 270
; forward 45
; west 4
; left 90
; north 5
; right 180
; north 2
; forward 51
; east 3
; south 5
; west 3
; north 5
; right 180
; north 3
; forward 99
; west 3
; forward 80
; south 5
; east 5
; forward 56
; west 4
; forward 54
; west 4
; forward 90
; south 4
; forward 85
; west 4
; forward 49
; west 2
; east 5
; right 180
; forward 75
; west 4
; right 90
; north 2
; left 90
; south 4
; left 270
; south 5
; forward 77
; south 5
; right 90
; south 4
; right 90
; north 5
; west 4
; forward 47
; east 5
; south 5
; right 90
; south 5
; forward 30
; south 3
; forward 25
; west 1
; north 5
; left 90
; north 3
; forward 15
; west 1
; north 1
; forward 47
; west 3
; north 4
; west 4
; west 3
; forward 4
; west 2
; left 270
; west 1
; north 2
; forward 84
; right 90
; forward 6
; right 180
; west 3
; right 180
; west 4
; south 1
; forward 92
; east 1
; north 1
; west 2
; right 180
; north 4
; west 4
; forward 38
; left 90
; west 1
; left 90
; east 3
; right 180
; west 5
; right 180
; forward 45
; right 90
; east 2
; north 3
; left 90
; forward 35
; right 180
; east 4
; north 5
; left 90
; forward 2
; north 1
; right 90
; forward 20
; left 90
; west 3
; forward 64
; left 90
; forward 98
; left 90
; north 2
; forward 36
; right 270
; south 1
; right 90
; forward 100
; east 1
; north 1
; left 90
; forward 46
; north 1
; north 4
; east 2
; left 270
; north 3
; west 1
; forward 84
; south 3
; forward 33
; north 5
; east 1
; forward 37
; north 2
; east 3
; north 4
; left 270
; forward 44
; left 180
; forward 57
; east 4
; north 2
; left 90
; north 5
; west 1
; left 180
; south 3
; left 90
; east 3
; left 90
; east 2
; left 270
; south 3
; forward 70
; left 90
; east 4
; right 90
; east 4
; south 3
; forward 16
; east 3
; north 2
; forward 51
; right 180
; east 4
; north 3
; forward 52
; right 90
; north 2
; right 90
; south 3
; left 90
; east 2
; forward 74
; left 90
; west 4
; right 180
; west 3
; south 3
; forward 2
; north 4
; left 180
; east 3
; forward 38
; east 3
; forward 37
; right 90
; forward 68
; right 180
; forward 62
; west 4
; north 3
; forward 70
; east 5
; forward 50
; north 3
; forward 6
; right 180
; forward 25
; north 4
; right 90
; forward 10
; left 90
; forward 53
; south 1
; forward 32
; right 90
; forward 69
; south 2
; west 4
; south 5
; right 90
; forward 10
; right 90
; forward 39
; west 3
; forward 55
; east 4
; forward 16
; west 1
; left 90
; east 1
; left 270
; north 1
; east 4
; forward 94
; north 2
; west 2
; forward 23
; north 3
; forward 51
; left 180
; south 1
; forward 83
; left 90
; north 3
; right 90
; forward 5
; north 1
; left 90
; forward 80
; east 4
; east 1
; forward 51
; right 180
; forward 14
; left 90
; forward 28
; left 90
; west 1
; left 180
; north 3
; right 90
; east 5
; forward 21
; right 90
; east 5
; forward 95
; right 180
; south 2
; east 1
; forward 69
; right 90
; south 3
; forward 83
; west 5
; forward 7
; south 4
; right 90
; forward 4
; west 4
; left 90
; south 5
; forward 67
; right 90
; west 2
; forward 59
; north 5
; right 90
; forward 63
; east 3
; left 90
; east 1
; south 3
; left 90
; east 5
; right 90
; forward 40
; west 2
; left 90
; forward 86
; east 1
; north 1
; east 3
; forward 25
; left 180
; forward 3
; right 180
; forward 47
; south 5
; forward 94
; left 180
; forward 10
; south 3
; west 2
; forward 95
; south 3
; left 90
; forward 38
; north 4
; right 90
; forward 51
; left 90
; forward 27
; east 1
; forward 93
; north 1
; forward 27
; left 180
; east 5
; south 1
; east 4
; north 3
; left 90
; north 3
; west 3
; south 1
; left 180
; east 2
; east 2
; forward 34
; east 1
; south 4
; east 4
; forward 77
; forward 49
; west 4
; north 3
; forward 46
; left 90
; east 1
; forward 85
; right 180
; south 4
; east 3
; right 90
; north 1
; right 90
; forward 8
; east 1
; forward 40
; right 180
; east 5
; forward 68
; forward 15
; right 180
; west 5
; forward 24
; forward 30
; left 90
; left 90
; forward 65
; east 5
; left 180
; forward 44
; left 90
; west 2
; forward 28
; east 2
; left 180
; south 4
; forward 91
; left 90
; forward 41
; east 3
; forward 100
; right 90
; west 2
; south 2
; forward 87
; right 90
; west 5
; forward 43
; west 3
; south 3
; forward 53
; south 3
; forward 29
; east 3
; forward 83
; left 90
; forward 85
; north 1
; east 3
; left 90
; east 2
; left 180
; east 5
; south 2
; north 1
; right 90
; forward 67
; east 5
; right 180
; forward 88
; south 4
; right 90
; east 5
; forward 72
; west 4
; north 2
; right 90
; north 2
; left 90
; south 5
; forward 2
; right 180
; east 5
; right 180
; forward 92
; east 2
; forward 90
; left 180
; east 2
; left 90
; west 4
; south 4
; right 90
; south 4
; left 90
; south 4
; left 180
; forward 54
; east 5
; left 270
; forward 80
; east 5
; north 3
; forward 84
; south 4
; forward 13
; south 3
; west 4
; forward 90
; west 3
; north 3
; forward 65
; east 4
; forward 33
; left 90
; west 4
; forward 97
; north 1
; right 90
; south 3
; left 90
; forward 71
; right 90
; left 90
; forward 99
; east 2
; right 90
; forward 76
; north 3
; right 90
; north 3
; forward 49
; right 180
; north 5
; north 3
; west 4
; forward 24
; west 1
; forward 79
; left 90
; forward 59
; right 90
; forward 73
; right 180
; forward 53
; south 5
; forward 72
; east 5
; forward 40
; east 2
; forward 28
; west 1
; forward 96
; north 2
; right 90
; west 5
; north 3
; east 1
; north 1
; left 90
; east 1
; forward 85
; left 90
; forward 45
; south 4
; west 2
; forward 77
; north 4
; right 270
; east 1
; right 90
; east 1
; forward 32
; south 5
; forward 93
; west 4
; forward 38
; north 1
; west 2
; right 180
; south 2
; forward 44
; left 90
; south 1
; east 1
; south 2
; east 5
; north 4
; east 2
; south 4
; west 4
; forward 27

let print_distance () : ML unit =
  //example();
  navigate();
  let d = ship_distance() in
    print_string (sprintf "%d\n" d)

let _ = print_distance()
