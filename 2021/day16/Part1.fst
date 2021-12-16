module Part1

open FStar.String
open FStar.IO
open FStar.All
open FStar.Printf
open FStar.List.Tot
  
type message =
 | Literal : (version:nat) -> (value:nat) -> message
 | Operator : (version:nat) -> (operands:list message) -> message

type bit =
 | Zero
 | One
 
let input = "020D708041258C0B4C683E61F674A1401595CC3DE669AC4FB7BEFEE840182CDF033401296F44367F938371802D2CC9801A980021304609C431007239C2C860400F7C36B005E446A44662A2805925FF96CBCE0033C5736D13D9CFCDC001C89BF57505799C0D1802D2639801A900021105A3A43C1007A1EC368A72D86130057401782F25B9054B94B003013EDF34133218A00D4A6F1985624B331FE359C354F7EB64A8524027D4DEB785CA00D540010D8E9132270803F1CA1D416200FDAC01697DCEB43D9DC5F6B7239CCA7557200986C013912598FF0BE4DFCC012C0091E7EFFA6E44123CE74624FBA01001328C01C8FF06E0A9803D1FA3343E3007A1641684C600B47DE009024ED7DD9564ED7DD940C017A00AF26654F76B5C62C65295B1B4ED8C1804DD979E2B13A97029CFCB3F1F96F28CE43318560F8400E2CAA5D80270FA1C90099D3D41BE00DD00010B893132108002131662342D91AFCA6330001073EA2E0054BC098804B5C00CC667B79727FF646267FA9E3971C96E71E8C00D911A9C738EC401A6CBEA33BC09B8015697BB7CD746E4A9FD4BB5613004BC01598EEE96EF755149B9A049D80480230C0041E514A51467D226E692801F049F73287F7AC29CB453E4B1FDE1F624100203368B3670200C46E93D13CAD11A6673B63A42600C00021119E304271006A30C3B844200E45F8A306C8037C9CA6FF850B004A459672B5C4E66A80090CC4F31E1D80193E60068801EC056498012804C58011BEC0414A00EF46005880162006800A3460073007B620070801E801073002B2C0055CEE9BC801DC9F5B913587D2C90600E4D93CE1A4DB51007E7399B066802339EEC65F519CF7632FAB900A45398C4A45B401AB8803506A2E4300004262AC13866401434D984CA4490ACA81CC0FB008B93764F9A8AE4F7ABED6B293330D46B7969998021C9EEF67C97BAC122822017C1C9FA0745B930D9C480"

let hex_digit_to_bits (c:char) : Tot (list bit) =
  match c with
  | '0' -> [ Zero; Zero; Zero; Zero ]
  | '1' -> [ Zero; Zero; Zero; One ]
  | '2' -> [ Zero; Zero;  One; Zero ]
  | '3' -> [ Zero; Zero;  One; One ]
  | '4' -> [ Zero; One; Zero; Zero ]
  | '5' -> [ Zero; One; Zero; One ]
  | '6' -> [ Zero; One;  One; Zero ]
  | '7' -> [ Zero; One;  One; One ]
  | '8' -> [ One; Zero; Zero; Zero ]
  | '9' -> [ One; Zero; Zero; One ]
  | 'A' -> [ One; Zero;  One; Zero ]
  | 'B' -> [ One; Zero;  One; One ]
  | 'C' -> [ One; One; Zero; Zero ]
  | 'D' -> [ One; One; Zero; One ]
  | 'E' -> [ One; One;  One; Zero ]
  | 'F' -> [ One; One;  One; One ]
  | _ -> []
  
let rec hex_chars_to_binary (l:list char) : (list bit) =
  match l with 
  | [] -> []
  | c :: tl -> List.Tot.append (hex_digit_to_bits c) (hex_chars_to_binary tl)

noeq type parse_result : a:Type -> Type =
  | OK : #a:Type -> value:a -> rest:list bit -> parse_result a
  | Error : #a:Type -> what:string -> parse_result a

let map_result #a #b (f:a->b) (r:parse_result a) : (parse_result b) =
  match r with 
  | OK v rest -> OK (f v) rest
  | Error what -> Error what

// First n elmements of a list
let rec first_n #a (n:nat) (l:(list a){length l >= n}) : (x:(list a){length x = n}) =
  if n = 0 then []
  else match l with
  | hd :: tl -> hd :: (first_n (n-1) tl)

// Sublist of a list starting at i and taking n elements
let rec sublist #a (i:nat) (n:nat) (l:(list a){length l >= i+n}) : (x:(list a){length x = n}) =
  if n = 0 then []
  else if i > 0 then match l with
  | hd :: tl -> (sublist (i-1) n tl)
  else match l with
  | hd :: tl -> hd :: (sublist 0 (n-1) tl)

let suffix #a (skip:nat{skip > 0}) (l:(list a){length l >= skip}) : (x:(list a){length x < length l}) =
  sublist skip (length l - skip) l

// MSB first to natural number
let rec bin_to_nat_aux (input:list bit) (prev:nat) : nat =
  match input with 
  | [] -> prev
  | One :: rest -> bin_to_nat_aux rest ((op_Multiply 2 prev) + 1)
  | Zero :: rest -> bin_to_nat_aux rest (op_Multiply 2 prev)

let bin_to_nat (input:list bit) : nat =
  bin_to_nat_aux input 0
  
let _ = assert( bin_to_nat [One;Zero;One] = 5 )

// 1xxxx -> xxxx and continue
// 0xxxx -> xxxx and stop
let rec parse_continued_bits (input:list bit) (prev:list bit) 
 : Tot (parse_result (list bit))
   (decreases length input) =
  if length input < 5 then
    Error "5-bit sequence expected"
  else match index input 0 with
  | One -> parse_continued_bits (suffix 5 input) (append prev (sublist 1 4 input))
  | Zero -> OK (append prev (sublist 1 4 input)) (suffix 5 input)

let parse_integer (input:list bit) : parse_result nat =
  map_result bin_to_nat (parse_continued_bits input [])

let parse_literal (version:nat) (input:list bit) : Tot (parse_result message) =
  map_result (fun (value:nat) -> Literal version value)
    (parse_integer input)

let rec parse_packet (input:list bit) 
: Tot (parse_result message) 
  (decreases %[length input;0]) =
  if length input < 6 then
    Error (sprintf "too short, %d bits" (length input))
  else
    let version = bin_to_nat (sublist 0 3 input) in
    let type_id = bin_to_nat (sublist 3 3 input) in
    match type_id with
    | 4 -> parse_literal version (suffix 6 input)
    | _ -> parse_operator version (suffix 6 input)
and parse_operator (version:nat) (input:list bit) 
: Tot (parse_result message) 
  (decreases %[length input;0]) =
    if length input < 1 then
      Error "missing length type id"
    else
      match (index input 0) with
      | Zero -> map_result (fun (operands:list message) -> Operator version operands)
            (parse_operator_by_length (suffix 1 input))
      | One -> map_result (fun (operands:list message) -> Operator version operands)
            (parse_operator_by_packets (suffix 1 input))
and parse_operator_by_length (input:list bit) 
: Tot (parse_result (list message)) 
   (decreases %[length input;0]) =
    if length input < 15 then
      Error "length field too short"
    else
      let bit_length = bin_to_nat (first_n 15 input) in
          if length input < 15 + bit_length then
             Error "packet not long enough"
          else
             match parse_list_until_end (sublist 15 bit_length input) [] with
                | OK v _ -> OK v (suffix (15 + bit_length) input)
                | Error e -> Error e
and parse_list_until_end (input:list bit) (prev:list message) 
: Tot (parse_result (list message)) 
   (decreases %[length input;1]) =
    if length input = 0 then
       OK prev input
    else match parse_packet input with
       | Error e -> Error ("parse_list_until_end: " ^ e)       
       | OK v rest -> if length rest < length input then
          parse_list_until_end rest (List.Tot.snoc (prev, v))
        else
          Error "message parsing did not consume any characters"       
and parse_operator_by_packets (input:list bit)
: Tot (parse_result (list message)) 
   (decreases %[length input;0]) =
    if length input < 11 then
      Error "count field too short"
    else
      let packet_count = bin_to_nat (first_n 11 input) in
          parse_list_until_zero (suffix 11 input) packet_count []
and parse_list_until_zero (input:list bit) (count:nat) (prev:list message)
: Tot (parse_result (list message))
   (decreases %[length input;1]) =
    if count = 0 then
       OK prev input
    else if length input = 0 then
       Error (sprintf "premature end of list, count %d" count)
    else match parse_packet input with
       | Error e -> Error ("parse_list_until_zero: " ^ e)
       | OK v rest -> if length rest < length input then
          parse_list_until_zero rest (count - 1) (List.Tot.snoc (prev,v))
        else
          Error "message parsing did not consume any characters"       

let print_bits (m:list bit) : ML unit = 
  List.iter (fun b -> match b with
     | Zero -> print_string "0"
     | One -> print_string "1"
  ) m;
  print_string "\n"
  
let rec print_message (m:message) : ML unit =
  match m with 
  | Literal version value -> 
     print_string (sprintf "(Literal v%d %d) " version value)
  | Operator version operands ->
     print_string (sprintf "(Operator v%d " version);
     List.iter print_message operands;
     print_string ")"

// operands << Operator version operands, but
// the individual messages in operands are not << the original message?
// So can't prove termination.
let rec sum_versions (m:message) : ML nat =
  match m with 
  | Literal version value -> version
  | Operator version operands ->
     version + (List.fold_left (fun (t:nat) m -> t + (sum_versions m)) 0 operands)

let example1 = "D2FE28"
let example2 = "38006F45291200"
let example3 = "EE00D40C823060"
let example4 = "8A004A801A8002F478"
let example5 = "620080001611562C8802118E34"
let example6 = "C0015000016115A2E0802F182340"
let example7 = "A0016C880162017C3686B18A3D4780"

let solve_part_1 (input:string) : ML unit =
  let b = hex_chars_to_binary (list_of_string input) in
    // print_bits b;
    match parse_packet b with
    | Error e -> print_string ( "Error: " ^ e ^ "\n" )
    | OK m _ -> print_message m; 
         print_string "\n";
         print_string (sprintf "Sum of versions=%d\n" (sum_versions m))

//let _ =solve_part_1 example1
//let _ =solve_part_1 example2
//let _ =solve_part_1 example3
let _ =solve_part_1 example4
let _ =solve_part_1 example5
let _ =solve_part_1 example6
let _ =solve_part_1 example7
let _ = solve_part_1 input
  
// example 5:
// 011000
//  1 subpackets 00000000010
//   000000
//    0 bits 000000000010110 = 22 bits 
//      000100 01010 literal 10
//      101100 01011 literal 11 
//   001000
//    1 subpackets 00000000010 
//      000100 01100
//      011100 01101
// 00
