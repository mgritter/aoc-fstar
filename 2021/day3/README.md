# Day 3 solution notes

I foolishly assumed that the input would *not* be of even length, so I wrote my initial types for
majority and minority based on that assumption, and then -- whoops! -- my check failed on the real input.
For Part 1, I could just add an all-zero vector at the end (which should not change the result, because
no tiebreaker was given.)  For Part 2, I was able to loosen these conditions and incorporate the tiebreaker
rule given into the "majority" and "minority" functions.

In Part 2, I also got tripped up by initially having my check for "last bit" and "length 1" in the wrong
order.  I don't know what sort of assertion would have caught that.  It seems very hard to prove that a
search of this sort terminates successfully with just one list element; for some inputs, it won't!

### F* successes

The bitvector (FStar.BV) type was painless to use and handled the bit-to-integer conversion!

Proving properties about majority/minority was generally painless, I was able to write a lemma that let
F* figure things out from there.

Being able to write the type precisely helped get the last line correct, I think I initially had `>`
instead of `>=`, and it gave me confidence the tiebreaker was the correct direction:

```FStar
let majority (input:(list bool)) : 
   Tot (b:bool{number_of b input > (List.Tot.length input / 2) \/
               (b = true /\ number_of true input = (List.Tot.length input / 2))}) =
   let true_count = number_of true input in
     let false_count = number_of false input in
       true_and_false_partition_the_list input;
       (true_count >= false_count)
```

### F* problems

In part 1 I wanted to map over the list `[0; 1; 2; 3; ...; 10; 11]`.  I could not convince F* that it had length 12, which I needed
to match the bitvector length.

I eventually grabbed the code I had laboriously gotten correct for natural-number ranged while warming up with last year's problems, but
that *cannot* be the right way to construct the numbers 0 through N-1 and prove that they have length N.  For fixed N in this case!
It's a horribly complicated set of three lemmas.

Oops, I thought I could use a fancy match clause after looking it up in OCaml, but 'match blah with | hd :: tl with hd = v` gave this:
```
// (Error 236) When clauses are not yet supported in --verify mode; they will be some day
```

This error message was less than helpful:
```
// Failed to resolve implicit argument ?328 of type pos introduced for flex-flex quasi:	lhs=Instantiating implicit argument in application	rhs=Instantiating implicit argument in application
```
I interpreted it as "I can't determine the length of the bit vector" but I'm not sure why not, or what the message is actually talking about.

### List literal length

I was close to working in one of my on-screen attempts, what we need to do is put the list into a variable first
before using `assert_norm`.  After that, F* can tell that the return value is the same as the list that we've
proved something about, which it can't seem to do for the raw literal:

```FStar
val zero_to_eleven (_:unit) : (l:list (n:nat{n<12}){List.Tot.length l = 12})
let zero_to_eleven _ = 
  let x = [0;1;2;3;4;5;6;7;8;9;10;11] in
    assert_norm(List.Tot.length x = 12);
    x
```

### Questions

Can I give types to the Part 2 loops that would have caught the bug earlier?

What is the "right" way to define an integer range?  Why isn't this in the standard library?

