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

I thought about creating a custom effect that only had the state that
was relevant to the problem. But it looked hairy so I didn't attempt it
on-screen.  What would that look like?

Is there a better "spec" for what the functions are supposed to do, that could
be used to prove correctness?






