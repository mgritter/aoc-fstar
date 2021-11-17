module ExampleInspect

open FStar.Tactics

let show_an_arrow_expr () : Tac unit =
  let t = (quote (fun (x:int) (y:int) -> x + y )) in
     print "Term: ";
     print (term_to_ast_string t);
     exact t

let addition : int -> int -> int = synth_by_tactic show_an_arrow_expr

let show_term _ : Tac unit = 
  let t = (`(fun (z:int) -> z)) in
    print (term_to_ast_string t);
  let t2 = (`(fun (z:int{z<2}) -> z)) in
    print (term_to_ast_string t2);
  exact (quote 1)

let foo : int = synth_by_tactic show_term


