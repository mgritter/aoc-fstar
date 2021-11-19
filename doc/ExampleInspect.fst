module ExampleInspect

open FStar.Tactics

let show_an_arrow_expr () : Tac unit =
  let t = (quote (fun (x:int) (y:int) -> x + y )) in
     print "Term: ";
     print (term_to_ast_string t);
     exact t

let addition : int -> int -> int = synth_by_tactic show_an_arrow_expr

let show_term _ : Tac unit = 
  print "Term 1\n";
  let t = (`(fun (z:int) -> z)) in
    print (term_to_ast_string t);
  print "Term 2\n";
  let t2 = (`(fun (z:int{z<2}) -> z)) in
    print (term_to_ast_string t2);
  print "Term 3\n";
  let t3 = (`(let rec f (x:nat) : nat = if x = 0 then 2 else 3 + f (x - 1) in f(5))) in
    print (term_to_ast_string t3);
  print "Term 4\n";
  let t4 = (`(let f (x:nat) : Lemma( x + 1 = 1 + x ) = () in f)) in
    print (term_to_ast_string t4);
  print "Term 5\n";
  let t5 = (`((x:nat) -> Lemma( x + 1 = 1 + x ))) in
    print (term_to_ast_string t5);
  print "Term 5\n";
  let t5 = (`((x:nat) -> Lemma( x + 1 = 1 + x ))) in
    print (term_to_ast_string t5);
  exact (quote 1)

let foo : int = synth_by_tactic show_term


