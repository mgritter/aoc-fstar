module Part1

open FStar.Heap
open FStar.String
open FStar.Printf
open FStar.IO
open FStar.All
open FStar.List.Tot
open FStar.ST
  
let vector (a:Type) (len:nat) = (l:(list a){List.Tot.length l = len})

let matrix (a:Type) (width:nat{0<width}) (height:nat{0<height}) =
  (vector (vector a width) height)

type octopus =
  | Flashed : octopus
  | Normal : nat -> octopus
  
let octopi = matrix (ref octopus) 10 10

type coord = (y:nat{y<10}*x:nat{x<10})

let value_at #a #w #h (m:matrix a w h) (i:nat{0 <= i && i < h}) (j:nat{0 <= j && j < w}) : Tot a =
  List.Tot.index (List.Tot.index m i) j  

let neighbor_at (m:matrix (ref octopus) 10 10) (y:nat{y < 10}) (x:nat{x < 10}) 
  (dy:int{-1 <= dy && dy <= 1}) (dx:int{-1 <= dx && dx <= 1}) (old:list coord) 
  : Tot (list coord) =
  if (y = 0 && dy = -1) then
    old
  else if (x = 0 && dx = -1) then
    old
  else if (y = 10 - 1 && dy = 1) then
    old
  else if (x = 10 - 1 && dx = 1) then
    old
  else
    ((y + dy),(x+dx)) :: old
    
let neighborhood (m:matrix (ref octopus) 10 10) (y:nat{0 <= y && y < 10}) (x:nat{0 <= x && x < 10}) 
: Tot (list coord) =
  neighbor_at m y x (-1) (-1)
  (neighbor_at m y x 0 (-1)
  (neighbor_at m y x 1 (-1)
  (neighbor_at m y x (-1) 0
  (neighbor_at m y x 1 0
  (neighbor_at m y x (-1) 1
  (neighbor_at m y x 0 1
  (neighbor_at m y x 1 1
    [])))))))

let rec parse_row_aux (s:list char) (expected_len:nat) : St
 (option (vector (ref octopus) expected_len)) 
 (decreases expected_len) =
    if expected_len = 0 then
       match s with
         | [] -> Some []
         | _ -> None
    else
    let add_octopus (o:ref octopus) (tl:list char) : St (option (vector (ref octopus) expected_len)) =
       match (parse_row_aux tl (expected_len - 1)) with
       | None -> None
       | Some l -> Some (o :: l)
    in match s with 
    | [] -> None
    | '0' :: tl -> (add_octopus (ST.alloc (Normal 0)) tl)
    | '1' :: tl -> (add_octopus (ST.alloc (Normal 1)) tl)
    | '2' :: tl -> (add_octopus (ST.alloc (Normal 2)) tl)
    | '3' :: tl -> (add_octopus (ST.alloc (Normal 3)) tl)
    | '4' :: tl -> (add_octopus (ST.alloc (Normal 4)) tl)
    | '5' :: tl -> (add_octopus (ST.alloc (Normal 5)) tl)
    | '6' :: tl -> (add_octopus (ST.alloc (Normal 6)) tl)
    | '7' :: tl -> (add_octopus (ST.alloc (Normal 7)) tl)
    | '8' :: tl -> (add_octopus (ST.alloc (Normal 8)) tl)
    | '9' :: tl -> (add_octopus (ST.alloc (Normal 9)) tl)
    | _ -> None
    
let parse_row (s:string) : St (option (vector (ref octopus) 10)) =
  parse_row_aux (list_of_string s) 10

let rec parse_matrix_aux (fd:fd_read)  : ML (list (vector (ref octopus) 10)) =
  try 
   let line = read_line fd in
     match parse_row line with
       | None -> failwith "Can't parse row"
       | Some row -> row :: (parse_matrix_aux fd)
   with
     | EOF -> []
     | _ -> failwith "Unexpected error" 

let parse_matrix (fd:fd_read) : ML octopi =
  let m = parse_matrix_aux fd in
     if length m <> 10 then
        failwith "Wrong number of rows"
     else
        m

let zero_to_nine : (l:(list (n:nat{n <= 9})){length l = 10}) =
  let lit = [0;1;2;3;4;5;6;7;8;9] in
    assert_norm( length lit = 10 );
    lit

let map_vec #a #b #n (f:a -> Tot b) (l:(list a){List.Tot.length l = n}) : Tot (vector b n) =
  List.Tot.map f l

let print_octopi (m:octopi) : ML unit =
  let map_row (y:nat{y<10}) : ML unit =
      let map_o (x:nat{x < 10}) : ML unit = 
        match !(value_at m y x) with
        | Flashed -> print_string "."
        | Normal v -> print_string (sprintf "%d" v)
      in (
        List.iter map_o zero_to_nine ;
        print_string "\n"
      )
  in 
    List.iter map_row zero_to_nine

// Adds 1 to all octopi and return any that flash this step
let add1_octopi (m:octopi) : ML (list coord) =
  let map_row (y:nat{y<10}) : ML (list coord) =
      let map_o (x:nat{x < 10}) : ML (list coord) =
        match !(value_at m y x) with
        | Flashed -> []
        | Normal v -> (
          (value_at m y x) := Normal (v+1);
          if v + 1 > 9 then
             [(y,x)]
          else
             []             
        )
      in List.collect map_o zero_to_nine
  in 
    List.collect map_row zero_to_nine

let count_and_reset_flashed_octopi (m:octopi) : ML nat =
  let map_row (col_count:nat) (y:nat{y<10}) : ML nat =
      let map_o (row_count:nat) (x:nat{x < 10}) : All nat 
        (requires fun _ -> true)
        (ensures fun h0 _ h1 -> 
            (modifies (only (value_at m y x)) h0 h1)
            /\ Normal? ( sel h1 (value_at m y x)))
      = 
        match !(value_at m y x) with
        | Flashed -> 
          (
            (value_at m y x) := Normal 0;
            (row_count + 1)
          )
        | Normal v -> row_count
      in List.fold_left map_o col_count zero_to_nine
  in 
    List.fold_left map_row 0 zero_to_nine

// Increments neighbors of a flashed octopus and 
// returns any that are now exactly 10 so that they also flash
let add1_octopi_list (m:octopi) (n:list coord) : ML (n:list coord) =
  let f (c:coord) : ML (list coord) =
    let y = fst c in let x = snd c in
    match !(value_at m y x) with
     | Flashed -> []
     | Normal v -> (
          (value_at m y x) := Normal (v+1);
          if v + 1 = 10 then // If > 10, it will already be on the list
             [(y,x)]
          else
             []           
     )
  in
    List.collect f n

let rec update_flashed_octopi (m:octopi) (l:list coord) : ML unit =
  match l with
  | [] -> ()
  | (y,x) :: tl ->
    match !(value_at m y x) with
    | Flashed -> update_flashed_octopi m tl
    | Normal _ -> (
       (value_at m y x) := Flashed;       
       let n = neighborhood m y x in
          let new_flashed = add1_octopi_list m n in
             update_flashed_octopi m (List.Tot.append tl new_flashed )       
    )

let step (m:octopi) : ML nat = 
  let flashed = add1_octopi m in
    update_flashed_octopi m flashed;
    count_and_reset_flashed_octopi m

let rec steps (m:octopi) (n:nat) (tot:nat) : ML nat = 
  if n = 0 then tot
  else let flashed = step m in
    print_string (sprintf "step %d flashes %d tot %d\n" n flashed (tot + flashed));
    steps m (n-1) (tot + flashed)

let calc_part_1 (fn:string): ML unit =
  let fd = open_read_file fn in
    let m = parse_matrix fd in
       let f = steps m 100 0 in
          print_octopi m;
          print_string "\n";
          print_string (sprintf "num flashes = %d\n" f )

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"


