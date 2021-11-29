module Boat

open BoatEffect

(*
These are the operations we need Ocaml implementations of
*)

// get_coords: whatever it returns must be equal to the internal state.
val get_coords: unit -> BOAT boat_state (fun p t0 -> p t0 t0)

// set_coords: afterwards, whatever was passed it must be equal to the internal state
val set_coords: (t1:boat_state) -> BOAT unit (fun p t0 -> p () t1)

