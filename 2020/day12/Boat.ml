open BoatEffect

let global_coords = ref {
  x = Prims.of_int 0;
  y = Prims.of_int 0;
  heading = Prims.of_int 0;
}
 
let get_coords() =
  !global_coords

let set_coords (c:BoatEffect.boat_state) =
  global_coords := c
 
		 
