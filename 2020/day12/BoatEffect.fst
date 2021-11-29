module BoatEffect

open FStar.ST
open FStar.Heap
open FStar.All

type bearing = (h:int{h = 0 \/ h = 90 \/ h = 180 \/ h = 270})
type boat_state = { heading: bearing; x: int; y: int }

let initial_state : boat_state = { heading=90; x=0; y=0 }

new_effect BOAT = STATE_h boat_state

// Boilerplate, for now, copied from FStar.ST.fst's definition of GST

// The type of a precondition on the state
// boat_state -> GTot Type0
let boat_pre           = st_pre_h boat_state

// The type of a postcondition on the state, parameterized by the return type
// of the function.
// a -> _: boat_state{pre} -> GTot Type0
// "pre" means preposition, not precondition.
let boat_post' (a:Type) (pre:Type) = st_post_h' boat_state a pre

// "Postconditions without refinemenst"
// a -> _: boat_state{True} -> GTot Type0
let boat_post  (a:Type) = st_post_h boat_state a

// The type of the "weakest precondition."  Takes postconditions to the 
// necessary preconditions.  In our case, it is
// (st_post_h boat_state a -> Tot (st_pre_h heap)
// (a -> boat_state -> GTot Type0) -> Tot (boat_state -> Gtot Type0)
let boat_wp (a:Type)   = st_wp_h boat_state a

// This says that a DIV computation leaves the boat state unchanged?
// I think this is required to let us call Tot functions.
unfold let lift_div_boat (a:Type) (wp:pure_wp a) (p:boat_post a) (t:boat_state) = wp (fun a -> p a t)
sub_effect DIV ~> BOAT = lift_div_boat

// BOAT  needs to be liftable to ML, I think, in order to produce output.
// ML is based on ALL, which is instantiated from ALL_h with a heap.
//
// Copying the example:
// unfold let lift_state_all (a : Type) (wp : st_wp a) (p : all_post a) = wp (fun a -> p (V a))
//
// This converts a boat WP to an ALL wp
// An ALL wp converts (all_post result) to (all_pre)
// all_pre is a predicate on heap: heap -> GTot Type0
// all_post is a predicate on the heap and response value: a -> (result a) -> heap{True} -> GTot Type

// This typechecks but for obvious reasons I don't feel good about it.
unfold let lift_boat_all_trivial (rt:Type) (wp:boat_wp rt) (pc: all_post rt) : all_pre =
  fun _ -> True

let boat_pre_to_all_pre (p1:boat_pre) : all_pre =
  // Ignore the heap, but the precondition must be based on the initial state of the boat?
  fun (h:heap) -> (p1 initial_state )

unfold let lift_boat_all (rt:Type) (wp:boat_wp rt) (pc: all_post rt) : all_pre =
  boat_pre_to_all_pre (wp (fun a bc -> pc (V a) emp))

sub_effect BOAT ~> ALL {lift_wp = lift_boat_all}

// More boilerplate, definining the pre/post and trivial versions.
effect BOAST (a:Type) (pre:boat_pre) (post: (h:boat_state -> Tot (boat_post' a (pre h)))) =
  BOAT a (fun (p:boat_post a) (h:boat_state) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))
effect Boat (a:Type) = BOAST a (fun h -> True) (fun h0 r h1 -> True)
