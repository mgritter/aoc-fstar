module Test

open FStar.List.Tot

val zero_to_eleven (_:unit) : (l:list (n:nat{n<12}){length l = 12})
let zero_to_eleven _ = 
  let x = [0;1;2;3;4;5;6;7;8;9;10;11] in
    assert_norm( length x = 12);
    x





