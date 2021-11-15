module ExampleSynth

open FStar.Tactics

let rec fib n : Tac unit = if n < 2 then exact (`1) else (apply (`(+)); fib (n - 1); fib (n - 2))

let f3 : int = synth_by_tactic (fun () -> fib 3)

let _ = assert( f3 = 3 )

let f8 : int = synth_by_tactic (fun () -> solve_then (fun () -> fib 8) compute)

let i_only_add_threes (x:int{x<10}) (y:int{x+y=3}) = x+y
let three_gen _ : Tac unit = dump "a"; apply (quote i_only_add_threes); dump_all true "b"; (exact (quote 1)); dump "c"; (exact (quote 2))

[@@expect_failure]
let three : int = synth_by_tactic three_gen

let one_plus_two_is_three _ : Lemma (2 + 1 = 3 == true) = ()

let three_gen_2 _ : Tac unit = 
  dump "a"; apply (quote i_only_add_threes); 
  dump_all true "b"; (exact (quote 1)); 
  dump "c"; apply_lemma (`one_plus_two_is_three); 
  dump "d"; exact (quote ())

let three : int = synth_by_tactic three_gen_2
