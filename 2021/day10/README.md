# Day 10 solution notes

Stack-based parsing was the right choice here, and the parser was surprisingly simple.

I messed up the requirements on part 1 which took some rewriting, but fortunately the
way I messed up was "return the stack" rather than "return the first erroneous character"
so I was well set up for part 2.

Fortunately I had median code all ready to go from day 7, so I didn't have to resolve the
"sorted list is the same length as the original one" problem.

## F* succeses

Had I written the type for part 2's "score" function correctly, it would have
caught my bug, which was

```FStar
match incomplete with
| Empty -> 0
```

but tbh I only wrote the type after parsing the error.  F* did point out that
the condition I wrote only applied to natural numbers, not integers, so I changed
the type at the last minute.

The stack-based parsing made it easy to prove termination, loads easier than
my recursive-descent parser.

## F* problems

I still can't believe sortWith doesn't automatically come with length equality.

I tried to write parse_stack so that `Error` was one of the constructors, but I wanted to express the fact that
`prev` could not be an error.  The first thing I tried was

```FStar
type parse_stack =
 | Error : parse_stack
 | Empty : parse_stack
 | Square : (prev:parse_stack{op_Negation (Error? prev)}) -> parse_stack
```

but the helper functions aren't yet in scope, I think.  I considered

```FStar
type parse_stack (is_error:bool) =
 | Error : parse_stack true
 | Empty : parse_stack false
 | Square : prev:(parse_stack false) -> parse_stack false
```

but then the return type of `parse_line` is not clear. Would it have to be a
dependent tuple?  I think it would.  But then might as well wrap an
error state around the stack-- which is what I did with `option`.

## Questions

Is there a way to express the idea above using only a single type?

Are F* type constructors arrow types?



