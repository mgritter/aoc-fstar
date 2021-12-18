module Part1

open FStar.String
open FStar.Printf
open FStar.All

// Our input:
// x=206..250, y=-105..-57

// x position =
//   x_v + 0
//   + (x_v-1)
//   + (x_v-2)
//   + ...
//   + (x_v-(x_v-1))     i.e., +1
//   + 0
//   + 0
// Sum after n steps =
// n * x_v - ( 0 + 1 + 2 + ... n-1 )
// n * x_v - (n-1)*n/2
// 
// after x_v steps, it's
//   x_v * x_v - (x_v-1)*x_v /2

let rec x_pos_n (n:nat) (curr_velocity:int) : int =
  if n = 0 then 0
  else if curr_velocity = 0 then 0
  else curr_velocity + (x_pos_n (n-1) (curr_velocity - 1))

let x_closed_form (n:nat) (init_velocity:int) : int =
  if n >= init_velocity then
     (op_Multiply init_velocity init_velocity) - (op_Multiply (init_velocity - 1) init_velocity ) / 2
  else
     (op_Multiply n init_velocity) - (op_Multiply (n-1) n) / 2

#push-options "--z3rlimit 30"
let rec x_pos_closed_form (n:nat) (init_velocity:int) 
  : Lemma (requires init_velocity >= 0)
    (ensures x_pos_n n init_velocity = x_closed_form n init_velocity )
   = if n = 0 then 
       ()
     else if init_velocity = 0 then
       ()
     else 
       x_pos_closed_form (n-1) (init_velocity - 1)
#pop-options

let rec y_pos_n (n:nat) (curr_velocity:int) : int =
  if n = 0 then 0
  else curr_velocity + (y_pos_n (n-1) (curr_velocity - 1))

let y_closed_form (n:nat) (init_velocity:int) : int =
  (op_Multiply n init_velocity) - (op_Multiply (n-1) n) / 2

let rec y_pos_closed_form (n:nat) (init_velocity:int) 
  : Lemma (y_pos_n n init_velocity =
           y_closed_form n init_velocity )
   = if n = 0 then 
       ()
     else 
       y_pos_closed_form (n-1) (init_velocity - 1)

// height = n * y_v - (n-1)*n/2 = n*y_v - (n^2-n)/2
// d/dn = y_v - n + 1/2
// d/dn = 0 when y_v - n + 1/2 = 0
//                  n = y_v + 1/2
// So, max height when n = y_v or y_v + 1 

// max height = iv * iv - (iv-1)*iv/2 = iv^2 - (iv^2)/2 + iv/2
// 

let y_maximum (iv:int) : int =
  (op_Multiply iv iv) - ( (op_Multiply iv iv) - iv) / 2

#push-options "--z3rlimit 60"
let rec y_maximum_exists_minus (init_velocity:int) (n:nat{n<=init_velocity})
 : Lemma (requires init_velocity >= 0)
         (ensures y_closed_form n init_velocity <= y_maximum init_velocity)
 = if n = 0 then
     ()
   else
     y_maximum_exists_minus init_velocity (n-1)

let rec y_maximum_exists_plus (init_velocity:int) (n:nat{n>=init_velocity})
 : Lemma (requires init_velocity >= 0)
         (ensures y_closed_form n init_velocity <= y_maximum init_velocity)
 = if n = init_velocity then
     ()
   else
     y_maximum_exists_plus init_velocity (n-1)
#pop-options

let y_maximum_exists (init_velocity:int) (n:nat)
 : Lemma (requires init_velocity >= 0)
         (ensures y_closed_form n init_velocity <= y_maximum init_velocity) =
   if n <= init_velocity then
     y_maximum_exists_minus init_velocity n
   else
     y_maximum_exists_plus init_velocity n

// y=-105..-57
// y(n) = n*y_v - (n^2-n)/2        
// -105 <= n*y_v - (n^2-n)/2 <= -57
//
// *waves hands furiously* ...
//            .........
//         .........
//      .....
//     ....
//    ....

let in_range (v:int) (min:int) (max:int) : Tot bool =
  min <= v && v <= max

type feasible : (x_min:int) -> (x_max:int) -> (y_min:int) -> (y_max:int) -> Type =
 | Feasible : (x_min:int) -> (x_max:int) -> (y_min:int) -> (y_max:int) 
              -> n:nat 
              -> (x_v:int{in_range (x_closed_form n x_v) x_min x_max})
              -> (y_v:int{in_range (y_closed_form n y_v) y_min y_max})
              -> feasible x_min x_max y_min y_max

// x_v <= x_max otherwise we overshoot on time 1
// 
// If a <= n*y_v - (n^2-n)/2 <= b, then
//  a + (n^2-n)/2 <= n * y_v <= b + (n^2-n)/2
//  a/n + (n-1)/2 <= y_v <= b/n + (n-1)/2
//  a  + n(n-1)/2 <= n * y_v <= b + n*(n-1)/2
//  a <= n ( y_v - (n-1)/2 )  <= b 
//
// Is the interval ever small enough not to contain an integer?
// Yes, (n-1)/2 is either an integer or half an integer, but 
// if a and b have the same sign, then 
// a/n and b/n form a bound that eventually does not include an integer,
// because they are within 0.5.

let maximum_x (x_min:int) (x_max:int) : int = x_max

let maximum_x_correct (x_min:int) (x_max:int) (n:nat{n>0}) (x_v:int)
 : Lemma( in_range (x_closed_form n x_v) x_min x_max ==> x_v <= maximum_x x_min x_max ) =
   ()
          
let maximum_n (y_min:int{y_min < 0}) (y_max:int{y_max < 0 && y_max >= y_min}) : nat =
   // Want (y_max - y_min) / n >= 0.5
   // 2(y_max - y_min) >= n
   op_Multiply 2 (y_max - y_min)

#push-options "--z3rlimit 120"
let maximum_n_correct (y_min:int{y_min < 0}) (y_max:int{y_max < 0 && y_max >= y_min}) (n:nat{n>0}) (y_v:int)
  : Lemma( in_range (y_closed_form n y_v) y_min y_max ==> n <= maximum_n y_min y_max )
  = // This might be hard because my proof did not use integers!
    // assert( in_range (y_closed_form n y_v) y_min y_max ==>
    //        y_min <= (op_Multiply n y_v) - (op_Multiply (n-1) n) / 2 );
    // assert( in_range (y_closed_form n y_v) y_min y_max ==>
    //        y_min + (op_Multiply (n-1) n) / 2  <= (op_Multiply n y_v) );
    //assert( in_range (y_closed_form n y_v) y_min y_max ==>
    //         (op_Multiply 2 y_min) + (op_Multiply (n-1) n)  <= (op_Multiply 2 (op_Multiply n y_v)));
    assert_spinoff( in_range (y_closed_form n y_v) y_min y_max ==>
            (op_Multiply 2 y_min) / n + (n-1)  <= (op_Multiply 2 y_v));
    assert_spinoff( in_range (y_closed_form n y_v) y_min y_max ==>
            (op_Multiply 2 y_v) <= (op_Multiply 2 y_max) / n + (n-1) );
    assert_spinoff( in_range (y_closed_form n y_v) y_min y_max ==>
            ( (op_Multiply 2 y_min) / n + (n-1)  <= (op_Multiply 2 y_v) /\
              (op_Multiply 2 y_v) <= (op_Multiply 2 y_max) / n + (n-1)) );
     ()
#pop-options            


let feasible_xy (x_min:int) (x_max:int) (y_min:int{y_min < 0}) (y_max:int)
 : Tot (list (feasible x_min x_max y_min y_max)) = 
    admit()
 
