# Day 4 solution notes

I had a bug, which caused me to be one move late in reporting the winner.  This was very
puzzling and I spent some time going back and doing printf-debugging.  It turned out that
I was checking for a winner in the input `board` rather than the marked boards
`marked_boards` so the winner was determined one iteration later.

It would be nice if I had written a type that would have caught this for me; something along
the lines of "this card is the first to winner" but "first" seems very difficult to reason about.
Maybe "it has the minimum among all winning times?"  We could play out all cards simulatneously
instead of one step at a time.

## F* wins

## F* problems

Is there a boolean not operator?  Or do we have to use op_Negation?  I had a hard time
finding `op_Negation` (and then I didn't recognize it when I found it, I kept looking for
a symbol.)  Is there a reference anywhere?  I noticed that || and && are not
on the symbols list, adding them to the wiki.

I keep running into the problem where I want types in F* to be covaraint, but they are not.
`list nat`  is not a `list int`.  An `option` on a refined type is not an `option` on the base type.
There are some simple examples in Covariance.fst in this directory.

Fortunately I got my "how to I make a list of length 5" problems out of my system, but I ended
up copy-and-pasting anyway because things that are one-liners in Python with list comprehensions
are much harder to express.

I spent a long time on parsing; maybe I need to write some better primitives.  Maybe I can copy
some of these on later days.

I could not figure out whether the `UInt32` parsing function would accept an initial `' '`
in the number, and my attempts to run Ocaml interactively to test it failed miserably.