module ExampleInspect

open FStar.Tactics

let show_an_arrow_expr () : Tac unit =
  let t = (quote (fun (x:int) (y:int) -> x + y )) in
     print "Term: ";
     print (term_to_ast_string t);
     exact t

let addition : int -> int -> int = synth_by_tactic show_an_arrow_expr
