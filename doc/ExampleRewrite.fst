module ExampleRewrite

open FStar.Tactics

// Match fun x -> <constant integer>
let match_constant (t:term) : Tac int =
  match inspect t with
  | Tv_Abs binder body -> 
     ( print ("binder: " ^ (binder_to_string binder));
       print ("body: " ^ (term_to_ast_string body));
       match body with 
     | Tv_Const (C_Int v) -> v
     | _ -> fail "not an integer constant"
     )
  | _ -> fail "not an abtraction"
                 
val rewrite_constant : (int->int)  -> Tac unit
let rewrite_constant f = 
  let t1 = (quote f) in
    print ("original term: " ^ (term_to_ast_string t1));
    let t2 = norm_term_env (top_env()) [delta] t1 in
      print ("after delta: " ^ (term_to_ast_string t2));    
      let orig_int = match_constant t2 in
        (exact (quote (fun x -> (op_Multiply orig_int 2))))


let a (x:int) : int = 5

let foo: int->int = synth_by_tactic (fun () -> rewrite_constant a)

let _ = assert( foo 3 = 10 )

    
  
