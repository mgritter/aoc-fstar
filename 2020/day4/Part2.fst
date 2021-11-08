module Part2

open FStar.IO
open FStar.Pervasives.Native
open FStar.Map
open FStar.All
open FStar.Option
open FStar.String
open FStar.Printf

// Only machine types have parsing routines built-in?
type uint64 = FStar.UInt64.t

type passport = { 
  ecl:option string; 
  pid:option string;
  hcl:option string;
  byr:option uint64;
  iyr:option uint64;
  eyr:option uint64;
  cid:option uint64;
  hgt:option string;
}

val construct_passport : (kv:Map.t string (option string)) -> passport 
let construct_passport kv = {
   ecl = sel kv "ecl";
   pid = sel kv "pid";
   cid = mapTot UInt64.of_string (sel kv "cid");
   hcl = sel kv "hcl"; 
   byr = mapTot UInt64.of_string (sel kv "byr");
   iyr = mapTot UInt64.of_string (sel kv "iyr");
   eyr = mapTot UInt64.of_string (sel kv "eyr");
   hgt = sel kv "hgt";   
}

let valid_passport (p:passport) : bool =
  (isSome p.pid) &&
  (isSome p.hcl) &&
  (isSome p.ecl) &&
  (isSome p.hgt) &&
  (isSome p.byr) &&
  (isSome p.iyr) &&
  (isSome p.eyr)

let valid_range (lower:int) (upper:int) (v:option uint64) : bool =
  match v with 
  | Some x -> lower <= UInt64.v x && UInt64.v x <= upper
  | None -> false

let valid_ecl (v:option string) : bool =
  match v with
  | Some "amb" -> true
  | Some "blu" -> true
  | Some "brn" -> true
  | Some "gry" -> true
  | Some "grn" -> true
  | Some "hzl" -> true
  | Some "oth" -> true
  | Some _ -> false
  | None -> false

type height =
  | InvalidHeight : height
  | Centimeters : uint64 -> height
  | Inches : uint64 -> height

let parse_height (v:option string) : Tot height =
  match v with
  | None -> InvalidHeight
  | Some x -> let l = length x in
      if l < 2 then
         InvalidHeight
      else
           match (sub x (l-2) 2) with
           | "in" -> Inches (UInt64.of_string (sub x 0 (l-2) ))
           | "cm" -> Centimeters (UInt64.of_string (sub x 0 (l-2)))
           | _ -> InvalidHeight

let valid_height (v:option string) : Tot bool =
  match (parse_height v) with
  | InvalidHeight -> false
  | Centimeters x -> 150 <= UInt64.v x && UInt64.v x <= 193
  | Inches x -> 59 <= UInt64.v x && UInt64.v x <= 76
  
let valid_hcl (v:option string) : Tot bool =
  match v with
  | None -> false
  | Some x -> if (length x) = 7 then
       let cs = list_of_string x in
         (List.Tot.hd cs = '#' &&
          List.Tot.for_all (fun c -> c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5' || c = '6' || c = '7' || c = '8' || c = '9' || c = 'a' || c = 'b' || c = 'c' || c = 'd' || c = 'e' || c = 'f')
         ( List.Tot.tail cs))
     else
       false

let valid_pid (v:option string) : Tot bool =
  match v with
  | None -> false
  | Some x -> if (length x) = 9 then
       List.Tot.for_all 
         (fun c -> c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5' || c = '6' || c = '7' || c = '8' || c = '9') 
         (list_of_string x)
     else
       false

let valid_passport_2 (p:passport) : bool =
  (valid_range 1920 2002 p.byr) &&
  (valid_range 2010 2020 p.iyr) &&
  (valid_range 2020 2030 p.eyr) &&
  (valid_height p.hgt) &&
  (valid_hcl p.hcl ) &&
  (valid_ecl p.ecl ) &&
  (valid_pid p.pid )

val get_default: option 'a -> 'a -> Tot 'a
let get_default o def = match o with 
  | Some x -> x
  | None -> def
  
let print_passport (p:passport) : ML unit =
    print_string (sprintf "[pid=%s cid=%uL hcl=%s ecl=%s hgt=%s byr=%uL iyr=%uL eyr=%uL] %b\n"
           (get_default p.pid "none")
           (get_default p.cid (UInt64.uint_to_t 0))
           (get_default p.hcl "none")
           (get_default p.ecl "none")
           (get_default p.hgt "none")
           (get_default p.byr (UInt64.uint_to_t 0))
           (get_default p.iyr (UInt64.uint_to_t 0))
           (get_default p.eyr (UInt64.uint_to_t 0))
           (valid_passport p))

      
// Detour: splitting the list always returns a nonempty list!  It might just the original
// string.  But, split is not implemented in F* but in ML so it doesn't look like we have 
// any information about it to work with
let split_returns_list (x:string) :
  Lemma (ensures (Cons? (String.split [':'] x)))
        = admit()
    
let string_to_key (s : string) : string =
  split_returns_list s;
  List.Tot.hd (String.split [':'] s)

let string_to_val (s : string) : option string =
  split_returns_list s;
  Some (List.Tot.last (String.split [':'] s))

val add_keys : (l:string) -> (m:Map.t string (option string)) -> Tot (Map.t string (option string))
let add_keys line orig_map =
  List.Tot.fold_left (fun m kv -> (upd m (string_to_key kv) (string_to_val kv)))
        orig_map        
        (String.split [' '] line)

// This only works correctly if there is not a blank line at the end 
// of input.
val parse_line_aux : (fd:fd_read) -> (prev: list passport) -> (current: Map.t string (option string)) -> ML (list passport)
let rec parse_line_aux fd prev current =
  try
    let line = read_line fd in
       match line with
       | "" -> parse_line_aux fd ((construct_passport current) :: prev) (const None)
       | _ -> parse_line_aux fd prev (add_keys line current)
    with
    | EOF -> (construct_passport current) :: prev
    | _ -> []

let parse (filename:string) : ML (list passport) =
  let fd = open_read_file filename in
    parse_line_aux fd [] (const None)

let echo_file (input_file:string) : ML unit = 
  FStar.List.iter print_passport (parse input_file)

let count_valid (input_file:string) : ML int =
  FStar.List.length (FStar.List.filter valid_passport (parse input_file))

let count_valid_2 (input_file:string) : ML int =
  FStar.List.length (FStar.List.filter valid_passport_2 (parse input_file))

let show_valid_count (input_file:string) : ML unit = 
  print_string (sprintf "%d valid passports\n" (count_valid_2 input_file) )

// let start = echo_file "example.txt"
// let start = show_valid_count "example.txt"

let start = show_valid_count "input.txt"

  

