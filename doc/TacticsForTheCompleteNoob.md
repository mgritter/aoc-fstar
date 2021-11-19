# F* Tactics for the Complete Noob

Tactics in F* are a very general mechanism which can be used to simplify
proofs, generate code, or even extend the compiler. But this generality comes
with a steep learning curve. This document is an attempt to explain how to
get started using and writing tactics in F*, from the perspective of a
software practitioner rather than a programming language researcher.

You should probably have worked through a F* tutorial first before attempting this
material; https://fstar-lang.org/tutorial/tutorial.html is IMO better than the incomplete
version at https://www.fstar-lang.org/tutorial/

### Other sources for learning about F* tactics:
* [Intro to tactics](https://people.csail.mit.edu/cpitcla/fstar.js/TacticsTutorial.html) -- a very basic introduction; shows how to show the outstanding goals, and to split goals, but not much else.
* ["Meta-F*: Proof Automation with SMT, Tactics, and Metaprograms"](https://fstar-lang.org/papers/metafstar/) -- an academic research paper from 2019
   * Contains an explanation of the means by which tactics access the proof state or the language structure.
   * This points to a directory of examples, most of which lack any explanation: https://github.com/FStarLang/FStar/tree/master/examples/tactics
* The source code for the `FStar.Tactics.*` modules themselves: https://github.com/FStarLang/FStar/tree/master/ulib -- somewhat hard to navigate, most methods lack documentation
   * The web documentation is out-of-date and badly formatted; see for example https://fstarlang.github.io/docs/FStar.Tactics.PatternMatching.html lacks all the nice tutorial given in https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Tactics.PatternMatching.fst; see https://people.csail.mit.edu/cpitcla/fstar.js/FStar.Tactics.PatternMatching.html for a nicely-formatted version.

## What is a tactic?

The simplest starting point is that a tactic, in F*, is a function that manipulates the
goals of a proof.  (This is not a complete picture.)

Whenever we want to assert something, we can call a function with type `unit -> Tac unit` to
manipulate the goal state.  This can either complete the proof, or leave goals that are simple
enough for the SMT solver to solve by itself.

`Tac` is an effect defined using FStar's effects system. This allows FStar to reason about
our tactic, as a stateful computation.

In the course of manipulating the goal state, we could also use function with return type
`Tac term` to create new terms.  Such functions can also be used in other contexts to
generate code.

## Using tactics to understand your proof state

When you're writing a complicated proof, you might lose track of what's being sent to the
solver. Did you use a lemma correctly?

You can dump out "everything that you know" by setting up a tactic that calls "dump".  Here's
a simple example where we're trying to prove that if two strings both have length zero, then
they are equal.

```FStar
open FStar.Tactics

let all_strings_of_length_zero_are_equal (s:string{strlen s=0}) (t:string{strlen t=0}) 
  : Lemma (ensures (s=t)) = 
    string_of_list_of_string s;
    assert_by_tactic True (fun () -> dump "here");
```

The dump output looks like this:

```
here @ ...-fstar/lib/StringLemmas.fst(89,4-89,20)
Goal 1/1
s: s: string{strlen s = 0}
t: t: string{strlen t = 0}
p: pure_post unit
uu___: forall (pure_result: unit). s = t ==> p pure_result
pure_result: unit
uu___'0: string_of_list (list_of_string s) == s
--------------------------------------------------------------------------------
squash l_True
(*?u141*) _
```

The goal we used in `assert_by_tactic` appears at the bottom.  Since we just used "True", it
isn't very interesting.

What's being show above the line is the
[Typing context](https://en.wikipedia.org/wiki/Typing_environment)
Each is a type assignment in the environment.  The parameters `s` and `t` are shown,
along with the refined types we specified for them.

``uu___'0`` contains the expansion of the existing Lemma we introducted.  In this example,
the solver isn't able to finish proving the lemma, because we haven't yet told it anything
about `t`.  If we add `string_of_list_of_string t` then we get another couple lines:

```
pure_result'0: unit
uu___'1: string_of_list (list_of_string t) == t
```

This addition is sufficient to establish the lemma.  When you have five or six lines, or
multiple arguments to your lemmas, this expanded view might be helpful to see what's going on,
even before using any real tactics.

### What are all those other variables in the output?

The `Lemma` shorthand is actually an "effect", and some of the variables behind its
implementation in terms of the `Pure` effect are shown.  The `p`, `uu___` and `pure_result`
type judgements come from the `Pure` effect that backs `Lemma`.  The definitions
are:

```FStar
effect Lemma (a: Type) (pre: Type) (post: (squash pre -> Type)) (pats: list pattern) =
  Pure a pre (fun r -> post ())

effect Pure (a: Type) (pre: pure_pre) (post: pure_post' a pre) =
  PURE a
    (fun (p: pure_post a) -> pre /\ (forall (pure_result: a). post pure_result ==> p pure_result))
```

## Building terms

To create tactics for proofs, you're probably going to have to know something about how to
create F* `term`s. For this we use the [FStar.Reflection] modules, as well as the `Tac`
effect.

We can run a tactic to provide a value using `synth_by_tactic`:

```FStar
val synth_by_tactic : (#t:Type) -> (unit -> Tac unit) -> Tot t
```

The goal of the tactic is the inferred type `t` of the call. Thinking of this in terms of dependent types,
we are asked to "prove" that there is an object of type `t`, by creating one.

The FStar examples directory includes this example: https://github.com/FStarLang/FStar/blob/master/examples/tactics/SolveThen.fst

```FStar
open FStar.Tactics

let rec fib n : Tac unit = if n < 2 then exact (`1) else (apply (`(+)); fib (n - 1); fib (n - 2))

let f3 : int = synth_by_tactic (fun () -> fib 3)

let f8 : int = synth_by_tactic (fun () -> solve_then (fun () -> fib 8) compute)
```

As explained in the previous section, we can debug the tactic by inserting a `dump` call.  If we do

```FStar
let f3 : int = synth_by_tactic (fun () -> dump "hello"; fib 3)
```

We get something like this, showing the goal (with no known type bindings) is to create an `int`:

```
hello @ …ples/tactics/SolveThen.fst(22,42-22,54)
Goal 1/1
--------------------------------------------------------------------------------
int
(*?u27*) _
```

If we place the `dump` after `fib 3`, then the goal is empty because it's already been satisfied.

The type of an F* expression or statement is `term`. Various methods exist for creating terms; the example above shows
quoting and application.

### Quoting and unquoting

The easiest way to create a `term` is by quoting an expression.  This creates a term that is identical to the
quoted value.  In the example above, you see ``(`1)`` used to create a term containing the literal `1`.  

We can also switch from a term back to a value, using `unquote` from the `Tactics` library.

A term preceded by `` ` `` is a static quotation: all terms are represented as-is, so a variable `x` becomes a free variable, even if it is defined
in context.

`quote` is a dynamic quotation: every free variable is replaced by its current values first.  (In the Meta-F* paper, it says that the
keyword is `dquote` but this does not appear in the current source code.)

Finally, Meta-F* provides "anti-quotations", which substitute a term into a quoted value, represented by `` `#x `` where `x` is an expression
of type `term`.  For example, `` `(1 + `#e) `` returns the term consisting of the application of `+` to the constant `1` and the term `e`.

The alternate antiquote `` `@x `` works when `x` is a value instead of a term.

### Terms to Tac units

The type of `fib` in the example above is not `Tac term`, it is `Tac unit`. That is because it's a tactic that satisfies
the goal of building a `nat`.  It uses two utility functions that operator on goals:

```FStar
val exact (t : term) : Tac unit
```

`exact` takes a term and satisfies a goal, if the goal has the same type as `t`, given the typing context of the goal.

In the example above, the goal is `nat`, the term `(quote 1)` has type `nat`, and so it satisfies the goal.

```FStar
val apply (t : term) : Tac unit
```

`apply` is a weird beast. It takes a `term` and attempts to apply it to arguments that are themselves new goals!  This process stops
when `t arg1 arg2 ... argN` is of the right type for the goal.

That is why `apply`'s only argument in the example above is `(quote (+))`.  The arguments are introduced separted by semicolons, because they
are separate expressions.

Here's an example in slow motion:

```FStar
let i_only_add_threes (x:int{x<10}) (y:int{x+y=3}) = x+y
let three_gen _ : Tac unit = dump "a"; apply (quote i_only_add_threes); dump_all true "b"; (exact (quote 1)); dump "c"; (exact (quote 2))
let three : int = synth_by_tactic three_gen
```

Our start goal is any `int`
```
a @ …fstar/doc/ExampleSynth.fst(14,29-14,37)  
Goal 1/1
--------------------------------------------------------------------------------
int
(*?u25*) _
```


After `apply` we have two goals (but `dump` will only show one of them, we need to use `dump_all`):

```
b @ …fstar/doc/ExampleSynth.fst(14,72-14,89)  
Goal 1/4 (new_problem: logical guard for TOP)
--------------------------------------------------------------------------------
Type0
l_True

Goal 2/4 (apply arg)
--------------------------------------------------------------------------------
y: int{(*?u33*) _ + y = 3}
(*?u35*) _

Goal 3/4 (apply arg)
--------------------------------------------------------------------------------
x: int{x < 10}
(*?u33*) _

Goal 4/4 (proofstate_of_goal_ty)
--------------------------------------------------------------------------------
int
i_only_add_threes (*?u33*) _ (*?u35*) _
```

After we satisfy the goal for `x` we are left with just one goal, but `exact` doesn't actually satisfy it:

```
c @ …tar/doc/ExampleSynth.fst(14,110-14,118)  
Goal 1/1
--------------------------------------------------------------------------------
squash ((*?u33*) _ + 1 = 3 == true)
(*?u40*) _
```

That is because `2` has not been judged to have type `z:int{z+1=3}`, so a new goal has been introduced to prove a statement of that type.

```
(Error 228) user tactic failed: `exact: 2 : int does not exactly solve the goal squash ((*?u33*) _ + 1 = 3 == true) (witness = (*?u40*) _)`
```

Here's a cheesy way to make the code generation succeed: prove a lemma that results in the squashed type we need, and then apply it.

```FStar
let one_plus_two_is_three _ : Lemma (2 + 1 = 3 == true) = ()

let three_gen_2 _ : Tac unit = 
  dump "a"; apply (quote i_only_add_threes); 
  dump_all true "b"; (exact (quote 1)); 
  dump "c"; apply_lemma (`one_plus_two_is_three); 
  dump "d"; exact (quote ())

let three : int = synth_by_tactic three_gen_2
```

The final `exact (quote ())` is because the lemma has an argument of type `unit`.

### Dumping the abstract syntax tree

With these tools, we can bootstrap our knowledge of "how do I build X" by getting a tactic to print it for us in terms of the abstract
syntax tree.  We can use `dump` as the example above, or `print` which only shows the string and not the context.

```FStar
open FStar.Tactics

let show_an_arrow_expr () : Tac unit =
  let t = (quote (fun (x:int) (y:int) -> x + y )) in
     print "Term: ";
     print (term_to_ast_string t);
     exact t

let addition : int -> int -> int = synth_by_tactic show_an_arrow_expr
```

gives output

```
TAC>> Term: 
TAC>> Tv_Abs ((x:Prims.int), Tv_Abs ((y:Prims.int), Tv_App (Tv_App (Tv_FVar Prims.op_Addition, Tv_Var (x:Prims.int)), Tv_Var (y:Prims.int))))
```

Here's a more complicated complicated example:

```FStar
let rec f (x:nat) : nat = if x = 0 then 2 else 3 + f (x - 1) in f(5)
```

parses as

```
Tv_Let (
  true,
  (f:_),
  Tv_Abs (
    (x:Prims.nat),
    Tv_Match (
      Tv_App (Tv_App (Tv_FVar Prims.op_Equality, Tv_Var (x:Prims.nat)), C_Int 0),
      None,
      [(_pat, C_Int 2);
       (_pat, Tv_App (
           Tv_App (Tv_FVar Prims.op_Addition, C_Int 3),
	   Tv_App (Tv_Var (f:_),
	           Tv_App (Tv_App(Tv_FVar Prims.op_Subtraction, Tv_Var (x:Prims.nat)),
			   C_Int 1))))])),
  Tv_App (Tv_Var (f:_), C_Int 5))
```

Each of the given constructors can be found in `FStar.Reflection.Data.fsti`.  But why are they prefixed with `Tv_`?

### Term views

The `term` type represents variables using a [locally nameless representation](https://chargueraud.org/research/2009/ln/main.pdf).
What this means is that bound variables (function arguments) are given a "de Bruijn index" rather than a lexical name.  The advantage:
F* doesn't need to do alpha-renaming by converting variable names to avoid collisions.  The disadvantage: terms end up numbered by how many
abstractions (lambdas) they are from the start of the expression, so they still do have to be renumbered, and it's hard to read.  Thus, any
output you see will probably have gone to some lengths to avoid showing you the de Bruijn index at all!

So, while you can perform operations on terms directly, if you inspect a `term` it is via a `term_view`.  You can convert back and forth
with a pair of functions:

```FStar
(** View a term in a fully-named representation *)
val inspect : term -> Tac term_view

(** Pack a term view on a fully-named representation back into a term *)
val pack    : term_view -> Tac term
```

> The term_view type provides the “one-level-deep” structure of a term: metaprograms must call
> `inspect` to reveal the structure of the term, one constructor at
> a time. The view exposes three kinds of variables: bound variables, `Tv_BVar`;
> named local variables `Tv_Var`; and top-level fully qualified names, `Tv_FVar`.
> Bound variables and local variables are distinguished since the internal abstract
> syntax is locally nameless. For metaprogramming, it is usually simpler to use a
> fully-named representation, so we provide `inspect` and `pack` functions that open
> and close binders appropriately to maintain this invariant. Since opening binders
> requires freshness, `inspect` has effect `Tac`. [Martinez et al 2019](https://fstar-lang.org/papers/metafstar/) 

### Factory functions for terms

While we can use `pack` on a expression created by the `term_view` constructors, the `Tactics` library also provides a large set of `mk_XXX`
functions to construct terms directly; these are found in `FStar.Tactics.Derived.fst` 

#### Application

```FStar
val mk_app (t : term) (args : list argv) : Tot term
```

`mk_app` creates an application.  An `argv` is pair consisting of a `term` and a qualification, which may be
`Q_Implicit` for implicit arguments, `Q_Explicit` for explicit arguments, or `Q_Meta of term` which doesn't seem to be used much.

If all the arguments are explicit then you can use

```FStar
val mk_e_app (t : term) (args : list term) : Tot term 
```

#### Basic data types

```FStar
val mk_stringlit (s : string) : term
```

Creates a string literal from a string.

```FStar
val mk_strcat (t1 t2 : term) : term
```

Creates an expression of the form `(strcat t1 t2)`.

```FStar
val mk_cons (h t : term) : term
```

Creates an expression of the form `(Cons h t)`

```FStar
val mk_cons_t (ty h t : term) : term
```

If you need to specify the type of a cons-expression, this variant takes the type `ty`.

```FStar
val rec mk_list (ts : list term) : term
```

Create a list literal.

```FStar
val mktuple_n (ts : list term) : term
```

Create a tuple (up to arity 8) from a list of terms inorder.

```FStar
val mkpair (t1 t2 : term) : term
```

Create a tuple of size two, a term of the form `(t1, t2)`.

(Note that the latter two depart from convention by not having an understore after `mk`.)

#### Arrow types and abstractions

```FStar
val mk_arr (bs: list binder) (cod : comp) : Tac term
val mk_tot_arr (bs: list binder) (cod : term) : Tac term
val mk_tot_arr_ln (bs: list binder) (cod : term) : Tot term 
```

These three functions create an arrow type.  `binders` are function arguments, while `comp` is the effect type.
The corresponding `comp_view` has constructors for total functions, `Lemma`s, and general effects.  The return type is part
of `comp`.

`mk_arr` fails explicitly if you try to give it an empty list of arguments.  `mk_tot_arr` instead assumes that the binder list is nonempty,
so presumably it fails in a less-explicit fashion.  `mk_tot_arr_ln` has the same definition, execpt that effect `Tot` instead of `Tac`.

TODO: advice on when to use each?  Or is this merely a library design bug?

```FStar
var mk_abs (args : list binder) (t : term) : Tac term
```

`mk_abs` creates an "abstraction", i.e., a `fun` term or lambda expression.

### Binders, how do they work?

A "binder" is a variable binding in an abstraction, i.e., a function parameter.

```FStar
val inspect_binder : binder -> bv * (aqualv * list term)
val pack_binder    : bv -> aqualv -> list term -> binder
```

`bv` is a bound variable.  `aqualv` is the `Q_Implicit` or `Q_Explicit` we saw above that are used when performing a function application.
But what is the list of terms?  It appears to be "attributes", but... comments in the files suggest this isn't common.

```
let binder_to_string (b : binder) : string =
    bv_to_string (bv_of_binder b) //TODO: print aqual, attributes
```

Inside the `bv` is a name, index, and type:

```
type bv_view = {
    bv_ppname : string;
    bv_index : int;
    bv_sort : typ;
}
```

You can use `name_of_bv` and `type_of_bv` to extract these directly from a `bv`.

### Example: modifying a function.

Let's take a constant function, and synthesize a function that has double its value.  The tactic will fail if
the function body is not a constant integer.

How do we match a function?  Piece by piece, painfully.  (This is why there's a pattern-matching engine implemented in
`FStar.Tactics.PatternMatching`.)  Here's the code to make sure that our term is an abstraction, and that its body is
an integer constant:

```FStar
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
```

Now, how do we get the function we want to operate on?  One way would be quoting it before giving it to the tactic, but that's somewhat
unwieldly. Instead, we can look up the value passed in (a variable) in the environment.

```FStar
val rewrite_constant : (int->int)  -> Tac unit
let rewrite_constant f = 
  let t1 = (quote f) in
    print ("original term: " ^ (term_to_ast_string t1));
    let t2 = norm_term_env (top_env()) [delta] t1 in
      print ("after delta: " ^ (term_to_ast_string t2));    
      let orig_int = match_constant t2 in
        (exact (quote (fun x -> (op_Multiply orig_int 2))))
```

Here, `(quote f)` produces the dynamic value of the parameter, but as we'll see, that only goes one layer down.  It binds to the name of the
function that gets passed in, not it content.  So, the next step is to apply normalization (the same thing F* would do while evaluating!).
the `norm_term_env` takes an environment (an `env`), a list of normalization steps to apply, and a `term`.  It then applies those steps
to the term; in this case we use `delta` which "unfolds names." We might pick something like `primops` to evaluate any arithmetic, if we wanted
to handle more complicated constant expressions.

Once we've extracted the constant value, creating the function is straightforward with dynamic quoting.

```FStar
let a (x:int) : int = 5

let foo: int->int = synth_by_tactic (fun () -> rewrite_constant a)

let _ = assert( foo 3 = 10 )
```

The output:

```
TAC>> original term: Tv_FVar ExampleRewrite.a
TAC>> after delta: Tv_Abs ((x:Prims.int), C_Int 5)
TAC>> binder: (x:Prims.int)
TAC>> body: C_Int 5
```

## Automating simple induction proofs

In the F* tutorial, you were given a function like this:

```FStar
val factorial: x:nat -> Tot int
let rec factorial n = 
  if n = 0 then 1 else n * (factorial (n - 1))
```

and asked to prove a lemma like this:

```FStar
let rec factorial_is_positive x : Lemma(factorial x > 0) =
  match x with
  | 0 -> ()
  | _ -> factorial_is_positive (x - 1)
```

Could we write a tactic that sets up simple recursive proofs of this sort?  So that all
we need is to write something like:

```FStar
let factorial_is_positive_auto x = 
  assert (factorial x > 0) by (recurse_on_nat 0)
```

### Understanding what the solver actually did

What did the Z3 solver actually see in order to check the original lemma?  We can ask F*
to dump all its queries to the Z3 solver

```
fstar.exe --log_types --log_queries Example.fst
```

If we look in the resulting `queries-Example.smt2` file there's a lot of goop.  For example,
here's the query F* performed to ensure that the subtraction in the factorial definition
resulted in a Nat (and that the recursion terminated!)

```
; Encoding query formula : ~(n = 0 = true) ==> (forall (b: Prims.bool). n = 0 == b ==> n - 1 >= 0 /\ n - 1 << n)
```

Eventually we get this statement of first-order logic:

```
; Encoding query formula : forall (p: Prims.pure_post Prims.unit).
;   (forall (pure_result: Prims.unit). Example.factorial x > 0 ==> p pure_result) ==>
;   (forall (k: Prims.pure_post Prims.unit).
;       (forall (x: Prims.unit). {:pattern Prims.guard_free (k x)} p x ==> k x) ==>
;       (x == 0 ==> (forall (any_result: Prims.unit). k any_result)) /\
;       (~(x = 0) ==>
;         (forall (b: Prims.nat).
;             x == b ==>
;             x - 1 >= 0 /\ x - 1 << x /\
;             (forall (return_val: x: Prims.nat{x << x}).
;                 return_val == x - 1 ==>
;                 (forall (pure_result: Prims.unit). Example.factorial (x - 1) > 0 ==> k pure_result))
;         )))
```

but fortunately we don't have to understand effects to make progress. If we squint our eyes
a little bit we can see that the solver is being asked to prove a conjuction

* If x = 0, then the type of the unit return value holds.  (There is only one `Prims.unit`!)
* If x <> 0, then factorial (x-1) > 0 implies the type as well.

### Introducing a lemma programatically

Here's our first step: how do we introduce a lemma we already know?  We use
`FStar.Tactics.Derived.apply_lemma`, which takes an argument of type `term`.
It solves a goal of type `squash phi` if the term is a `Lemma` that ensures `phi`.

```FStar
let appeal_to_lemma : Tac unit =
  dump "before";
  apply_lemma (`factorial_is_positive);
  dump "after"

let factorial_is_positive2 x = 
  assert( factorial x > 0) by appeal_to_lemma ()
```

The "before" dump shows our goal:

```
before @ .../aoc-fstar/doc/Example.fst(16,2-16,15)
Goal 1/1
x: nat
--------------------------------------------------------------------------------
squash (factorial x > 0)
(*?u34*)
```

The "after" dump shows that it has been satisfied; no goals remain.

```
after @ .../aoc-fstar/doc/Example.fst(18,2-18,14) 
```

### Writing a lemma

What if we construct the lemma _inside_ the tactic instead of outside?

```FStar
let appeal_to_new_lemma () : Tac unit =
  dump "before";
  let rec temporary_lemma (y:nat) : Lemma(factorial(y) > 0) = 
     if y = 0 then ()
     else temporary_lemma (y-1) in
    apply_lemma (quote temporary_lemma);
    dump "after"

let factorial_is_positive3 (x:nat) = 
  assert (factorial x > 0) by appeal_to_new_lemma()
```

We get a warning from F*:

```
(Warning 242) Definitions of inner let-rec temporary_lemma and its enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types (Also see: Example.fst(31,10-31,25))
```

and a monster goal in "after"

```
after @ …k/aoc-fstar/doc/Example.fst(35,4-35,16)  
SMT goal 1/1
x: nat
--------------------------------------------------------------------------------
squash (forall (y: nat).
      (*could not prove post-condition*)
      forall (p: pure_post unit).
        (forall (pure_result: unit). factorial y > 0 ==> p pure_result) ==>
        (forall (k: pure_post unit).
            (forall (x: unit). {:pattern guard_free (k x)} p x ==> k x) ==>
            (y = 0 == true ==> (forall (any_result: unit). k any_result)) /\
            (~(y = 0 = true) ==>
              (forall (b: bool).
                  y = 0 == b ==>
                  (forall (y: nat)
                      (temporary_lemma:
                      (y: nat{y << y} -> FStar.Pervasives.Lemma (ensures factorial y > 0))).
                      (*could not prove post-condition*)
                      forall (p: pure_post unit).
                        (forall (pure_result: unit). factorial y > 0 ==> p pure_result) ==>
                        (forall (k: pure_post unit).
                            (forall (x: unit). {:pattern guard_free (k x)} p x ==> k x) ==>
                            (y = 0 == true ==> (forall (any_result: unit). k any_result)) /\
                            (~(y = 0 = true) ==>
                              (forall (b: bool).
                                  y = 0 == b ==>
                                  y - 1 >= 0 /\ y - 1 << y /\
                                  (forall (return_val: y: nat{y << y}).
                                      return_val == y - 1 ==>
                                      (forall (pure_result: unit).
                                          factorial (y - 1) > 0 ==> k pure_result)))))) /\
                  (forall (b: (y: nat -> FStar.Pervasives.Lemma (ensures factorial y > 0)))
                      (any_result: (y: nat -> FStar.Pervasives.Lemma (ensures factorial y > 0))).
                      y - 1 >= 0 /\
                      (forall (return_val: nat).
                          return_val == y - 1 ==>
                          (forall (pure_result: unit). factorial (y - 1) > 0 ==> k pure_result))))))
  )
(*?u145*) _
```

but the proof succeeds.

### Looping in the tactic

Let's take a detour and solve a simpler case: what if we only wanted to show our inequality
for a specific value?  If we have the inductive step as a lemma:

```FStar
let factorial_step (x:nat{x>0}) 
 : Lemma (requires (factorial (x-1) > 0))
         (ensures (factorial x > 0))
     = ()
```

then we can apply it a constant number of times:

```FStar
let rec constant_depth (depth:nat) : Tac unit =
  if depth = 0 then 
     dump "depth 0"
  else (
     apply_lemma (`factorial_step);
     dump "after lemma";
     constant_depth (depth - 1)
  )

let factorial_is_positive4 = 
  assert (factorial 5 > 0) by (constant_depth 5)

```  

This gives a sequence of goals:

```
squash (factorial (5 - 1) > 0)
squash (factorial (5 - 1 - 1) > 0)
...
squash (factorial (5 - 1 - 1 - 1 - 1 - 1) > 0)
```

But this is sort of silly.  Trying it for general depth will cause an error:

```
(Error 228) user tactic failed: `Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.
(if n = 0
  then reify (FStar.Tactics.Builtins.dump "depth 0")
  else
    reify (FStar.Tactics.Derived.apply_lemma (`Example.factorial_step);
        let _ = FStar.Tactics.Builtins.dump "after lemma" in
        Example.constant_depth (n - 1))) "(((proofstate)))"`
```

### Building the lemma as a term

This still isn't generalized to other cases, but we can build the lemma as a term using quoting:

```FStar
let appeal_to_new_lemma2 () : Tac unit =
  dump "before";
  let new_lemma=`(let rec nl (y:nat) : Lemma(factorial y > 0 == true) = if y = 0 then () else nl (y-1) in nl) in 
      apply_lemma new_lemma;
      dump "after"

let factorial_is_positive5 (n:nat) = 
  assert (factorial n > 0) by appeal_to_new_lemma2()
```

This time we have to give F* a little help by converting the Lemma contents from a `bool` (the result of the comparison) to a
`Type`, specifically an equality type.

Our familiar-looking monster goal is back, but SMT can handle it.

```
after @ …k/aoc-fstar/doc/Example.fst(66,6-66,18)  Wed Nov 17 02:02:28 2021
SMT goal 1/1
n: nat
--------------------------------------------------------------------------------
squash (forall (y: nat)
      (nl: (y: nat{y << y} -> FStar.Pervasives.Lemma (ensures factorial y > 0 == true))).
      (*could not prove post-condition*)
      forall (p: pure_post unit).
        (forall (pure_result: unit). factorial y > 0 == true ==> p pure_result) ==>
        (forall (any_result: nat).
            y == any_result ==>
            (forall (any_result: int).
                0 == any_result ==>
                (forall (any_result: bool).
                    y = 0 == any_result ==>
                    (forall (k: pure_post unit).
                        (forall (x: unit). {:pattern guard_free (k x)} p x ==> k x) ==>
                        (y = 0 == true ==> (forall (any_result: unit). k any_result)) /\
                        (~(y = 0 = true) ==>
                          (forall (b: bool).
                              y = 0 == b ==>
                              y - 1 >= 0 /\ y - 1 << y /\
                              (forall (return_val: y: nat{y << y}).
                                  return_val == y - 1 ==>
                                  (forall (pure_result: unit).
                                      factorial (y - 1) > 0 == true ==> k pure_result)))))))))
(*?u140*) _
```


But how worried should we be about "could not prove post-condition"?

Well, if we try a false lemma, the type-checker does catch it!

```FSTar
let appeal_to_false_lemma () : Tac unit =
  dump "before";
  let new_lemma=`(let rec nl (y:nat) : Lemma(factorial y > 120 == true) = if y = 0 then () else nl (y-1) in nl) in 
      apply_lemma new_lemma;
      dump "after"

let factorial_is_positive6 (n:nat) = 
  assert (factorial n > 120) by appeal_to_false_lemma()
```

```
(Error 19) could not prove post-condition; The SMT solver could not prove the query, try to spell your proof in more detail or increase fuel/ifuel
```

### Can we send the induction to the SMT solver?
 
Instead of writing a lemma, can we just transform the goal into something simliar to what the lemma produces?

The answer appears to be *no*.  For the clearest example of what's going wrong, consider the following Lemma, which doesn't type-check.

```FStar
let half_induction (n:nat) : Lemma
  (requires (n == 0) ==> (factorial 0 > 0 == true ) /\
            (n > 0 ) ==> (factorial (n-1) > 0 == true ==> factorial n > 0 == true))
  (ensures (factorial n > 0))
  = ()
```

It seems like F* knows how to type-check a recursive function, but it does not recognize induction over the natural numbers when it appears.
So, it can translate a recursively-defined Lemma in a sound way, but that capability doesn't appear to be available to tactics.

Perhaps I am mistaken.  But https://github.com/FStarLang/FStar/issues/1419 has a one-word checklist item for "induction".

### Can we create a lemma from scratch?

Can we recognize the goal, construct a Lemma using reflection as in the previous working example, and apply it?

This seems difficult for a couple reasons:
  * Unquoting only works in certain places; it looks like a restriction on the desugaring process. Whatever the cause, something
  like the following does not seem to work: 

```FStar
let lemma = (`let rec foo (n:nat) : Lemma(`#mygoal) ...)
```

  * The `Tv_Let` term view constructor e has fields for whether it is recursive or not, a set of attributes, the binding variable, the definition,
  and the body of the statement.  But `attrs` seems to be always empty.
  
``` Fstar
type term_view =
...
| Tv_Let    : recf:bool -> attrs:(list term) -> bv:bv -> def:term -> body:term -> term_view
```

Something like

```FStar
`(let f (x:nat) : Lemma( x + 1 = 1 + x ) = () in f)
```

gets printed as

```
TAC>> Tv_Let (false, (f:_), Tv_Abs ((x:Prims.nat), C_Unit), Tv_Var (f:_))
```

All the type annotation has disappeared, somewhere.  Perhaps a better understanding of how the type annotation is implemented would help,
but I don't have that.


### A new hope

The following Lemma _does_ type-check in F*:

```FStar
let rec nat_induction (p : nat -> Type) (n:nat)
  : Lemma (requires p 0 /\ (forall (x:nat) . ( x > 0 /\ p (x-1) ) ==> p x ))
    (ensures p n)
  = if n = 0 then () else nat_induction p (n-1)
```

So, if we can recognize the goal and write it as an abstraction, then we can apply this theorem to many different goals.  Let's build
the pieces one by one.

### Examining the current goal

The `cur_goal` function lets us example what we're trying to prove:

```FStar
(** [cur_goal] returns the current goal's type *)
let cur_goal () : Tac typ = goal_type (_cur_goal ())
```

We can take that type and unwrap it from its 'squash', like this, using pattern-matching on the application.  The `squash_qn` is a constant
that is equal to `["Prims", "squash"]`, the fully qualified name of the `squash` function.

```FStar
let access_type_in_squash (t:typ) : Tac term =
  match inspect t with 
  | Tv_App hd a -> 
    begin
    match inspect hd with
    | Tv_FVar f ->
       if inspect_fv f = squash_qn then
          fst a
       else
          fail "Not a squash type"
    | _ -> fail "Not a squash type"
    end
  | _ -> fail "Not a squash type"

let nat_induction_tac () : Tac unit =
     let term_to_prove = access_type_in_squash (cur_goal()) in (
       print ("goal type = " ^ term_to_string( term_to_prove ) );
          ...
```

### Examining the current environment

The `curr_binder` function lets us look at the binders (the type context) of the environment:

```FStar
(** [cur_binders] returns the list of binders in the current goal. *)
let cur_binders () : Tac binders =
    binders_of_env (cur_env ())
```

From this we can learn the name and type of any arguments to our type.  Recall, when we're starting out, our goal looks like this:

```
proof-state: State dump @ depth 1 (before):
Location: ExampleInduction.fst(49,19-49,32)
Goal 1/1:
(n: Prims.nat) |- _ : Prims.squash (ExampleInduction.factorial n > 0)
```

So, we can check that there's exactly one (and could check that its type is `nat`) like this:

```FStar
let induction_binder () : Tac binder =
  match cur_binders() with
  | [] -> fail "No variable in environment"
  | hd :: [] -> hd
  | hd :: tl -> fail "More than one variable in environment"

let nat_induction_tac () : Tac unit =
     let term_to_prove = access_type_in_squash (cur_goal()) in (
       print ("goal type = " ^ term_to_string( term_to_prove ) );
       let binder = induction_binder() in
         print ("binder = " ^ binder_to_string( binder) )
            ...
```

### Applying our super-lemma

With these in hand, we can create an abstraction of the correct type, and apply it to
`nat_induction` to get the lemma that we need.  Here's the whole tactic:

```FStar
let rec nat_induction (p : nat -> Type) (n:nat)
  : Lemma (requires p 0 /\ (forall (x:nat) . ( x > 0 /\ p (x-1) ) ==> p x ))
    (ensures p n)
  = if n = 0 then () else nat_induction p (n-1)

let access_type_in_squash (t:typ) : Tac term =
  match inspect t with 
  | Tv_App hd a -> 
    begin
    match inspect hd with
    | Tv_FVar f ->
       if inspect_fv f = squash_qn then
          fst a
       else
          fail "Not a squash type"
    | _ -> fail "Not a squash type"
    end
  | _ -> fail "Not a squash type"

let induction_binder () : Tac binder =
  match cur_binders() with
  | [] -> fail "No variable in environment"
  | hd :: [] -> hd
  | hd :: tl -> fail "More than one variable in environment"

let nat_induction_tac () : Tac unit =
     let term_to_prove = access_type_in_squash (cur_goal()) in (
       print ("goal type = " ^ term_to_string( term_to_prove ) );
       let binder = induction_binder() in
         print ("binder = " ^ binder_to_string( binder) );
           let myProp = mk_abs [binder] term_to_prove in
             let l = mk_e_app (`nat_induction) [myProp] in
               print( "my_lemma = " ^ term_to_string( l ) );
               dump "before";
               apply_lemma l;
               dump "after lemma";
               split();
               dump "after split"
```

We used a new function from the `Tactics` namespace, called `split` which converts goals that have an `/\` into two separate goals.
This would allow us to work on the two sides of the inductive hypothesis separately, if we needed to.  (We could call `nat_induction_tac`
from other tactics.)

Here's what it looks like on our sample theorem:

```FStar
let factorial_is_positive (n:nat) = 
  assert (factorial n > 0) by nat_induction_tac()
```

```
TAC>> goal type = ExampleInduction.factorial n > 0
TAC>> binder = (n:Prims.nat)
TAC>> my_lemma = ExampleInduction.nat_induction (fun n -> ExampleInduction.factorial n > 0)
proof-state: State dump @ depth 1 (before):
Location: ExampleInduction.fst(49,19-49,32)
Goal 1/1:
(n: Prims.nat) |- _ : Prims.squash (ExampleInduction.factorial binder > 0)

proof-state: State dump @ depth 1 (after lemma):
Location: ExampleInduction.fst(51,19-51,37)
Goal 1/1:
(n: Prims.nat) |- _ : Prims.squash ((fun n -> ExampleInduction.factorial n > 0) 0 /\
    (forall (x: Prims.nat).
        x > 0 /\ (fun n -> ExampleInduction.factorial n > 0) (x - 1) ==>
        (fun n -> ExampleInduction.factorial n > 0) x))

proof-state: State dump @ depth 0 (after split):
Location: ExampleInduction.fst(53,19-53,37)
Goal 1/2:
(n: Prims.nat) |- _ : Prims.squash (ExampleInduction.factorial 0 > 0)

Goal 2/2:
(n: Prims.nat) |- _ : Prims.squash (forall (x: Prims.nat).
      x > 0 /\ ExampleInduction.factorial (x - 1) > 0 ==> ExampleInduction.factorial x > 0)

Verified module: ExampleInduction
All verification conditions discharged successfully
```

Is there a simpler way?


## What's in the standard library?


