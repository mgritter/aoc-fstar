# Advent of Code day 14 solution notes

I was kicking myself for not doing part 1 in a forward-looking fashion, but it wasn't *too*
hard to adapt the code for part 2, switching from maintaining a list to maintaining pairs.

I wonder if the corner case of the first and last characters actually matters to the solution
correctness.  I could give it a try, I suppose.  They only participate in one pair each, so they
are the only characters that are not double-counted in the pair population count.

I missed the obvious solution for double-counting pairs: only count the rightmost element in each pair!  Oops.

## F* successes

Type-checking helped a lot when I was rewriting functions that had worked on single values
to work on pairs instead.

F* unexpectedly was able to prove that this function met its own preconditions. I'm not sure in what circumstances
F* is able to do that:

```
let rec single_step (polymer:(list char){Cons? polymer}) (rules:list rule) : (list char) =
  match polymer with
  | c0 :: c1 :: rest -> (
      match find_rule rules c0 c1 with
      | None -> c0 :: (single_step (c1::rest) rules)
      | Some r -> c0 :: (Rule?.result r) :: (single_step (c1::rest) rules)      
  )
  | c0 :: [] -> [c0]
```

It is certainly true that the output is a nonempty list (every case guarantees that) but even though
this was not in the return value type, the `multiple_steps` function was able to feed the return value
into a parameter that also required a nonempty list.

## F* problems

Not having an iteratable map domain produced some quite ugly hacks.  This is what I used instead, iterating
over the entire space of pairs instead of just the ones in the map:

```FStar
let all_elements : list char = ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L'; 'M'; 'N'; 'O'; 'P'; 'Q'; 'R'; 'S'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z']

let rec product (a:list char) (b:list char) : (list (char*char)) =
  match a with 
  | [] -> []
  | hd :: tl ->
      List.Tot.append 
        (List.Tot.map (fun x -> (hd,x)) b)
        (product tl b)
      
let all_pairs : list (char*char) = product all_elements all_elements
```

## Questions

I wrote one invariant in part 2 that we would like to be able to prove. Is it feasible to do so?

What other correctness checks can we made about the polymerization process? I wasn't really able to come up with a concise definition of
what it's supposed to look like other than the function itself.

Would updating the map imperatively rather than iteratively made it easier to make the code correct when updating two keys at once,
which might concievably be equal?  Maybe I should have written a helper function for that.

