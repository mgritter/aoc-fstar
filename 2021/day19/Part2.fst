module Part2

open FStar.List.Tot
open FStar.Printf
open FStar.All
open FStar.IO

let positions : list (int*int*int) = [
(1164,1250,-15);
(2306,1164,-24);
(3477,-1147,2567);
(3623,-9,3737);
(3533,3667,159);
(3651,2454,-15);
(2316,2427,-3);
(2307,2338,1261);
(2341,-1264,1211);
(2426,-1264,2514);
(3490,1240,1188);
(2424,1251,1267);
(2354,-1125,3678);
(2413,1237,3623);
(2457,48,4796);
(1185,91,2525);
(2394,-32,3766);
(2361,-82,2400);
(1152,-1250,1236);
(2296,97,1318);
(1232,-18,1286);
(16,-29,-2262);
(23,18,-1148);
(-1276,97,1275);
(34,39,1212);
(0,0,0)
]

let manhattan_distance (a:int*int*int) (b:int*int*int) : int =
  abs( a._1 - b._1 ) + 
  abs( a._2 - b._2 ) + 
  abs( a._3 - b._3 )

let rec combinations_2 #a (l: list a) : (list (a*a)) =
  match l with
  | [] -> []
  | hd :: tl -> List.Tot.append
     (List.Tot.map (fun x -> (hd,x)) tl)
     (combinations_2 tl)
     

let max_manhattan_distance (scanners:list (int*int*int)) : int =
  List.Tot.fold_left (fun best pair ->
     let m = manhattan_distance (fst pair) (snd pair) in
        if m > best then m else best )
     0 (combinations_2 scanners)

let calc_part_2 _ : ML unit =
  print_string (sprintf "max distance=%d\n" (max_manhattan_distance positions))

let _ = calc_part_2()

