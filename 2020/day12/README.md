## Day 12 solution notes

I wanted to learn F*'s STATE/ST effect, so even though this could have been
done in a purely functional fashion, I did it in imperative style.

### F* successes

This was a toy example of "embedding a domain-specific language within F*".
I translated the input to a program, and then built the program primitives.

F* caught my copy-and-paste error, but only after I did. Ensuring that each
of north/south/east/west only modified the correct coordinate would have
prevented the failed submission on part 1.

### Problems encountered with F*

I'm really not sure, even after having read the tutorial a couple times,
whether it is possible to prove lemmas about imperative functions after
they are written?  Or is it necessary to include all the information about
what the function does in its postconditions in order to do so?

I'm also not sure whether changing a value X -> Y -> X counts as "modifies"
or not for the purpose of the postcondition. I expect it does not.

Verifying the real input function takes a long time, had to bump the SMT
rlimit, even though there is (I think?) not any complicated type here.
The SMT queries that timed out all said "reason-unknown=unknwon because unknown".
The error message could be a lot better here and say "timed out" if that's
the problem

### Questions

Is there a more idiomatic way to get the x, y, etc. variables into
the imperative functions?

Is there a better "spec" for what the functions are supposed to do, that could
be used to prove correctness?

### The BOAT effect

I created a custom effect based on STATE_h so that the state is just the
tuple we care about.  You can find this code in BoatEffect.fsti, and a
solution using it in Part3.

It didn't seem like I could define the getters and setters within F*, but
I may be missing something obvious.  The heap getters and setters, for example,
are not defined but merely assumed.  I followed this pattern, and so
the minimal interface defined in Boat.fsti is implemented in Boat.ml.

More questions arose in the course of doing this;

* Is there a way to define get_coords/set_coords so that F* extracts their
definitions as well?

* What is the best way to lift the BOAT effect to ALL, so that we can call
it from an ML function?  How do we convert BOAT wp's to ALL wp's?

I implemented the trivial lift function which simply ignores the state of
the heap, and always returns True.  That might be fine.

I implemented and used a slightly more complicted version below, but I'm
not sure it's any more "correct":

```FStar
let boat_pre_to_all_pre (p1:boat_pre) : all_pre =
  fun (h:heap) -> (p1 initial_state )

unfold let lift_boat_all (rt:Type) (wp:boat_wp rt) (pc: all_post rt) : all_pre =
  boat_pre_to_all_pre (wp (fun a bc -> pc (V a) emp))
```

This says to convert a BOAT predicate transformer "wp" into an "ALL" predicate
transformer:
  1. Access the postcondition for return value `a` (of type `rt`?) on the empty heap: `pc (V a) emp`.  `V` is a constructor for the `result` type used to signal errors.  BOAT cannot error.
  2. Run the WP predicate transformer, ignoring the contents of the boat state.
  3. That gives a precondition for BOAT on the boat state.  But we need a precondition on the ALL heap.  Once again, ignore the heap and return the type that we'd get on the boat initial state.

All of these seem extremely sketchy, but work in practice--- and I'm not trying to reason about the whole ML effect, so it's probably
OK? But, then we might as well do the easy thing.





