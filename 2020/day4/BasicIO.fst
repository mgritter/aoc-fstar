module BasicIO

open FStar.IO
open FStar.All

let input_file : string = "example.txt"

val cat_file_to_file : fd_read -> fd_write -> ML unit
let rec cat_file_to_file in_fd out_fd =
  try
    let line = read_line in_fd in
      write_string out_fd line;
      write_string out_fd "\n";
      cat_file_to_file in_fd out_fd
  with
  | EOF -> ()
  | _ -> ()
  
val cat_file : (filename : string) -> ML unit

let cat_file filename =
  let fd = open_read_file filename in
      cat_file_to_file fd stdout

let main = cat_file input_file
