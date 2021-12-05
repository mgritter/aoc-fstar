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
There are some simple examples in [Covariance.fst](Covariance.fst) in this directory.

Fortunately I got my "how to I make a list of length 5" problems out of my system, but I ended
up copy-and-pasting anyway because things that are one-liners in Python with list comprehensions
are much harder to express.

I spent a long time on parsing; maybe I need to write some better primitives.  Maybe I can copy
some of these on later days.

I could not figure out whether the `UInt32` parsing function would accept an initial `' '`
in the number, and my attempts to run Ocaml interactively to test it failed miserably.

### follow-up "Part 3"

I decided it would be easier to prove the properties of the solution if we computed the first-win times
for all boards, and then took the minimum and the maximum.  Here's the key predicate, which is
itself recusively defined:

```
// Predicate: is x the first index within "nums" such that
// marking the first x numbers makes the card a win?
let rec is_first_win (nums:list int) (c:card) (x:nat) : Tot bool =
  ( x = 0 && is_winner c ) ||
  ( x > 0 && x <= length nums &&
    length nums > 0 &&
    op_Negation (is_winner c)  &&
    is_first_win (tl nums) (mark_single_card (hd nums) c) (x-1) )
```

We can show that this definition ensures that no previous round is a win:

```
let rec first_really_is_first (nums:list int) (c:card) (x:nat) (y:nat)
 : Lemma (requires (is_first_win nums c x) /\ (y < x))
         (ensures (is_first_win nums c y = false )) =
	 // proof omitted
```

And that the search procedure that is actually executed will find it.

```
let rec time_to_win_returns_first (nums:list int) (c:card) (time:nat) (final_card:card):
  Lemma (requires (time_to_win nums c == Some (time,final_card)))
        (ensures (is_first_win nums c time)) =
	// proof omitted
```

This latter proof required me to bump up the SMT solver timeout; sometimes it worked
without it, but not reliably.

I was pleased that the SMT solver could handle the details of this proof by itself:

```
let rec first_by_time (nums:list int) (l:(list (win_rec nums)){Cons? l}) :
  (m:(win_rec nums){forall y . (mem y l) ==> Winner?.time m <= Winner?.time y}) =
  match l with 
  | hd :: [] -> hd
  | hd :: tl -> let prev_min = first_by_time nums tl in
    if Winner?.time hd <= Winner?.time prev_min then
       hd
    else
       prev_min
```

I was less pleased that I had to convert the "time" back into an "index", in a way not
proven to be correct.  So there was still room for a bug to be introduced in the score
calculation, but writing a type for that seemed still another bump in complexity.
