module Aki

open FStar.IO

let ascii_aki : list string = [
" ___                 ___\n";
" >_ \   _ _ _ _ _   / _<\n";
"< <, Y``         ''Y .> >\n";
" \ (`  .-.-._.-.-.  ') /\n";
" ( ` .'  _     _  `. ' )\n";
" )  (   (')___(')   )  ( \n";
"(  ('      `Y'      `)  )\n";
"(   (.  `.__|__.'  .)   )\n";
" (.  (._         _.)  .)\n";
"  (_   `- - - - -'   _)\n";
"    `-._ _ ___ _ _.-´  \n"]

let print_aki () : FStar.All.ML unit =
  List.iter print_string ascii_aki
  
