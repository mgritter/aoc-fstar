module ExampleMatch

let sign = (z:int{z = 0 \/ z = (-1) \/ z = 1})

let example_1 (s:sign) : string =
 match s with
 | (-1) -> "negative"
 | 1 -> "positive"
 | 0 -> "zero"
