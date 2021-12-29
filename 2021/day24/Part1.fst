module Part1

open FStar.IO
open FStar.All
open FStar.Printf
open FStar.Option

type var_name =
 | W
 | X
 | Y
 | Z
 
type alu_inst = 
 | Inp : (v:var_name) -> alu_inst
 | Add : (v1:var_name) -> (v2:var_name) -> alu_inst
 | Addi : (v1:var_name) -> (imm:int) -> alu_inst
 | Mul : (v1:var_name) -> (v2:var_name) -> alu_inst
 | Muli : (v1:var_name) -> (imm:int) -> alu_inst
 | Div : (v1:var_name) -> (v2:var_name) -> alu_inst
 | Divi : (v1:var_name) -> (imm:int) -> alu_inst
 | Mod : (v1:var_name) -> (v2:var_name) -> alu_inst
 | Modi : (v1:var_name) -> (imm:int) -> alu_inst
 | Eql : (v1:var_name) -> (v2:var_name) -> alu_inst
 | Eqli : (v1:var_name) -> (imm:int) -> alu_inst

type expr =
 | InputValue : (index:nat{index<14}) -> expr
 | Literal : (z:int) -> expr
 | AddOp : (a:expr) -> (b:expr) -> expr
 | MulOp : (a:expr) -> (b:expr) -> expr
 | DivOp : (a:expr) -> (b:expr) -> expr
 | ModOp : (a:expr) -> (b:expr) -> expr
 | EqlOp : (a:expr) -> (b:expr) -> expr
 | IfEqElse: (cmpa:expr) -> (cmpb:expr) -> (ifeq:expr) -> (ifneq:expr) -> expr

let input_program : (list alu_inst) = [
Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 1
;Addi X 12
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 7
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 1
;Addi X 11
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 15
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 1
;Addi X 12
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 2
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 26
;Addi X (-3)
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 15
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26  // = z mod 26
;Divi Z 1   
;Addi X 10  // = (z+10) mod 26
;Eql X W    // 
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 14
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 26
;Addi X (-9)
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 2
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 1
;Addi X 10
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 15
;Mul Y X
;Add Z Y
;Inp W

;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 26
;Addi X (-7)
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 1
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 26
;Addi X (-11)
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 15
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 26
;Addi X (-4)
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 15
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 1
;Addi X 14
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 12
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 1
;Addi X 11
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 2
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 26
;Addi X (-8)
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 13
;Mul Y X
;Add Z Y

;Inp W
;Muli X 0
;Add X Z
;Modi X 26
;Divi Z 26
;Addi X (-10)
;Eql X W
;Eqli X 0
;Muli Y 0
;Addi Y 25
;Mul Y X
;Addi Y 1
;Mul Z Y
;Muli Y 0
;Add Y W
;Addi Y 13
;Mul Y X
;Add Z Y
]

type alu_registers = {  
  w: expr;
  x: expr;
  y: expr;
  z: expr;
  next_input: (n:nat{n<14});
}

let rec print_spaces (n:nat) : ML unit =
  if n = 0 then () else (
    print_string " ";
    print_spaces (n-1)
  )
  
let rec print_expr (e:expr) (depth:nat) : ML unit =
  match e with 
   | InputValue i -> print_string (sprintf "i_%d " i)
   | Literal z -> print_string (sprintf "%d " z)
   | AddOp a b -> print_string( "(+ ");
      print_expr a (depth+1);
      print_expr b (depth+1);
      print_string ") "
   | MulOp a b -> print_string( "(* ");
      print_expr a (depth+1);
      print_expr b (depth+1);
      print_string ") "
   | DivOp a b -> print_string( "(/ ");
      print_expr a (depth+1);
      print_expr b (depth+1);
      print_string ") "
   | ModOp a b -> print_string( "(% ");
      print_expr a (depth+1);
      print_expr b (depth+1);
      print_string ") "
   | EqlOp a b -> print_string( "(= ");
      print_expr a (depth+1);
      print_expr b (depth+1);
      print_string ") "
   | IfEqElse a b t f -> 
      print_string( "(if ");
      print_expr a (depth+1);
      print_string " = ";
      print_expr b (depth+1);
      print_string "\n";
      print_spaces depth;
      print_string "then\n";
      print_spaces depth;
      print_expr t (depth+1);      
      print_string "\n";
      print_spaces depth;
      print_string "else\n";
      print_spaces depth;
      print_expr f (depth+1);      
      print_string ") "

let mapTotPair #a #b (f:a -> a -> Tot b) (x:option a) (y:option a) : option b =
  match (x,y) with
  | Some x1, Some y1 -> Some (f x1 y1)
  | _ -> None

let mapNonzeroPair (f:int -> nonzero -> Tot int) (x:option int) (y:option int) : option int =
  match (x,y) with
  | Some x1, Some 0 -> None
  | Some x1, Some y1 -> Some (f x1 y1)
  | _ -> None

type input_vals = list (z:int{z >= 1 /\ z <= 9})

let rec eval_expr (e:expr) (inputs:input_vals) : Tot (option int) =
  match e with 
   | InputValue i -> if i < List.Tot.length inputs 
      then Some (List.Tot.index inputs i) else Some 1 
   | Literal z -> Some z
   | AddOp a b -> mapTotPair (+) (eval_expr a inputs) (eval_expr b inputs)
   | MulOp a b -> mapTotPair op_Multiply (eval_expr a inputs) (eval_expr b inputs)
   | DivOp a b -> mapNonzeroPair (/) (eval_expr a inputs) (eval_expr b inputs)
   | ModOp a b -> mapNonzeroPair (%) (eval_expr a inputs) (eval_expr b inputs)
   | EqlOp a b -> ( match (eval_expr a inputs,eval_expr b inputs) with
                  | Some av, Some bv -> if av = bv then Some 1 else Some 0
                  | _ -> None )
   | IfEqElse a b t f -> ( match (eval_expr a inputs,eval_expr b inputs) with
                  | Some av, Some bv -> if av = bv then (eval_expr t inputs) else (eval_expr f inputs)
                  | _ -> None)

let print_registers (regs:alu_registers) : ML unit =
  print_string "W: ";
  print_expr regs.w 0;
  print_string "\nX: ";
  print_expr regs.x 0;
  print_string "\nY: ";
  print_expr regs.y 0;
  print_string "\nZ: ";
  print_expr regs.z 0;
  print_string "\n\n"

let get_value (regs:alu_registers) (v:var_name) : expr =
  match v with 
  | W -> regs.w
  | X -> regs.x
  | Y -> regs.y
  | Z -> regs.z

// Apply the following transformations:
// 0 + x = x
// x + 0 = x
// 0 * x = 0
// x * 0 = 0
// 0 / x = 0
// 0 % x = 0
// 0 eql 0 = 1
// 1 * x = x
// x * 1 = x
// x / 1 = x
// literal mathematics
let identity_removal (e:expr) : expr =
  match e with
   | AddOp a (Literal 0) -> a
   | AddOp (Literal 0) b -> b   
   | AddOp (Literal a) (Literal b) -> (Literal (a+b))   
   | MulOp a (Literal 0) -> (Literal 0)
   | MulOp (Literal 0) b -> (Literal 0)
   | MulOp a (Literal 1) -> a
   | MulOp (Literal 1) b -> b
   | MulOp (Literal a) (Literal b) -> (Literal (op_Multiply a b))   
   | DivOp a (Literal 1) -> a   
   | DivOp (Literal 0) b -> (Literal 0)
   | ModOp (Literal 0) b -> (Literal 0)
   | ModOp (Literal a) (Literal b) -> 
      if b <> 0 then (Literal (a % b)) else e
   | EqlOp (Literal a) (Literal b) -> 
      if a = b then (Literal 1) else (Literal 0)
   // Inputs can only be 1 through 9, inclusive
   | EqlOp (InputValue a) (Literal b) -> 
      if b < 1 || b > 9 then (Literal 0) else e
   | EqlOp (Literal b) (InputValue a) -> 
      if b < 1 || b > 9 then (Literal 0) else e
   | _ -> e

let identity_correctness (e:expr) (iv:input_vals) 
 : Lemma (requires Some? (eval_expr e iv))
         // Some transformations only valid if the program is
         // valid and does not divide by zero.
         (ensures ( eval_expr e iv = eval_expr (identity_removal e) iv))
 = ()

let rec simplify_identity (e:expr) : expr =
  match e with
   | AddOp a b -> (identity_removal (AddOp (simplify_identity a) (simplify_identity b)))
   | MulOp a b -> (identity_removal (MulOp (simplify_identity a) (simplify_identity b)))
   | DivOp a b -> (identity_removal (DivOp (simplify_identity a) (simplify_identity b)))
   | ModOp a b -> (identity_removal (ModOp (simplify_identity a) (simplify_identity b)))
   | EqlOp a b -> (identity_removal (EqlOp (simplify_identity a) (simplify_identity b)))
   | IfEqElse a b t f -> 
      let t' = (identity_removal t) in
      let f' = (identity_removal f) in
        if t' = f' then t'
        else IfEqElse (identity_removal a) (identity_removal b) t' f'
   | Literal i -> Literal i
   | InputValue  i -> InputValue i

let rec simplify_identity_correctness (e:expr) (iv:input_vals) 
 : Lemma (requires Some? (eval_expr e iv))
         // Some transformations only valid if the program is
         // valid and does not divide by zero.
         (ensures ( eval_expr e iv = eval_expr (simplify_identity e) iv))
 = match e with
   | AddOp a b -> simplify_identity_correctness a iv;
                 simplify_identity_correctness b iv;
                 identity_correctness (AddOp (simplify_identity a) (simplify_identity b)) iv
   | MulOp a b -> simplify_identity_correctness a iv;
                 simplify_identity_correctness b iv;
                 identity_correctness (MulOp (simplify_identity a) (simplify_identity b)) iv
   | DivOp a b -> simplify_identity_correctness a iv;
                 simplify_identity_correctness b iv;
                 identity_correctness (DivOp (simplify_identity a) (simplify_identity b)) iv
   | ModOp a b -> simplify_identity_correctness a iv;
                 simplify_identity_correctness b iv;
                 identity_correctness (ModOp (simplify_identity a) (simplify_identity b)) iv
   | EqlOp a b -> simplify_identity_correctness a iv;
                 simplify_identity_correctness b iv;
                 identity_correctness (EqlOp (simplify_identity a) (simplify_identity b)) iv
   | IfEqElse a b t f -> (
                 // Need to match the structure of the evaluation because 
                 // the precondition to "identity_correctness t" is not met if the expression
                 // is always false, and vice versa.
                 identity_correctness a iv;
                 identity_correctness b iv;
                 match ( eval_expr a iv, eval_expr b iv) with
                  | Some av, Some bv -> if av = bv then 
                     identity_correctness t iv
                    else
                     identity_correctness f iv
                  | _ -> ()
                 )
   | _ -> ()


let _ = assert_norm 
  (simplify_identity  
    (EqlOp (AddOp (ModOp (AddOp (MulOp (Literal 0) (Literal 0))
                                (Literal 0))
                         (Literal 26))
                   (Literal 12))
           (InputValue 0))
    = (Literal 0))

let store_value (regs:alu_registers) (v:var_name) (e:expr) : alu_registers =
  match v with
    | W -> {regs with w = e}
    | X -> {regs with x = e}
    | Y -> {regs with y = e}
    | Z -> {regs with z = e}

// (+ (% (+ i_0 7 ) 26 ) 11 )
//
// (% (+ i_0 18) 26)
let rec constant_fold (e:expr{AddOp? e}) (l:int) : option expr =
  match e with
  | AddOp a (Literal b) -> Some (AddOp a (Literal (b+l)))
  | AddOp (Literal a) b -> Some (AddOp (Literal (a+l)) b)
  | AddOp (AddOp a1 b1) (AddOp a2 b2) -> (
     match constant_fold (AddOp a2 b2) l with
     | Some b' -> Some (AddOp (AddOp a1 b1) b')
     | None -> ( match constant_fold (AddOp a1 b1) l with 
         | Some a' -> Some (AddOp a' (AddOp a2 b2))
         | None -> None )
    )
  | AddOp x (AddOp a b) -> (
     match constant_fold (AddOp a b) l with
     | Some b' -> Some (AddOp x b')
     | None -> None    
  )
  | AddOp (AddOp a b) x -> (  
     match constant_fold (AddOp a b) l with
     | Some a' -> Some (AddOp a' x)
     | None -> None    
  )
  | AddOp x y ->
    None

let rec constant_fold_correct (e:expr{AddOp? e}) (iv:input_vals) (l:int) :
  Lemma (requires Some? (eval_expr e iv) /\ Some? (constant_fold e l))
        (ensures Some? (eval_expr (Some?.v (constant_fold e l)) iv) /\
                 l + (Some?.v (eval_expr e iv)) = 
                 Some?.v (eval_expr (Some?.v (constant_fold e l)) iv))                 
  = match e with
  // handle all the recursive cases
  | AddOp (AddOp a1 b1) (AddOp a2 b2) -> (
     match constant_fold (AddOp a2 b2) l with
     | Some _ -> constant_fold_correct (AddOp a2 b2) iv l
     | None -> assert (Some? (constant_fold (AddOp a1 b1) l));
              constant_fold_correct (AddOp a1 b1) iv l
     )
  // need to specifically exclude these from the next case
  | AddOp a (Literal b) -> ()
  | AddOp (Literal a) b -> ()
  | AddOp x (AddOp a b) ->
     constant_fold_correct (AddOp a b) iv l
  | AddOp (AddOp a b) y -> 
     constant_fold_correct (AddOp a b) iv l
        
let simplify_addition (e:expr) : expr =
  match e with
  | AddOp (Literal x) (AddOp a b) 
  | AddOp (AddOp a b) (Literal x) -> (
     match constant_fold (AddOp a b) x with
     | None -> (AddOp (AddOp a b) (Literal x)) // TODO: maybe this doesn't handle + 0 ?
     | Some f -> simplify_identity f       
  )
  | _ -> simplify_identity e

let simplify_addition_correctness (e:expr) (iv:input_vals) 
 : Lemma (requires Some? (eval_expr e iv))
         (ensures ( eval_expr e iv = eval_expr (simplify_addition e) iv)) =
  match e with
  | AddOp (Literal x) (AddOp a b) 
  | AddOp (AddOp a b) (Literal x) -> (
     match constant_fold (AddOp a b) x with
     | None -> ()
     | Some f -> constant_fold_correct (AddOp a b) iv x;
                simplify_identity_correctness f iv
    )
  | other -> simplify_identity_correctness other iv

let rec bound_value (e:expr) : option (int*int) =
  match e with
  | InputValue _ -> Some (1,9)
  | Literal z -> Some (z,z)
  | AddOp x y -> (match (bound_value x),(bound_value y)  with
      | (Some (lo_x,up_x), Some (lo_y,up_y)) -> Some ((lo_x + lo_y),( up_x + up_y))
      | _ -> None
    )
  | _ -> None

let rec bound_correctness (e:expr) (iv:input_vals): Lemma
  (requires Some? (bound_value e) /\ Some? (eval_expr e iv))
  (ensures Some?.v (eval_expr e iv) >= (fst (Some?.v (bound_value e))) /\
           Some?.v (eval_expr e iv) <= (snd (Some?.v (bound_value e))))
   = match e with
     | AddOp x y ->
        assert( Some? (bound_value x));
        assert( Some? (bound_value y));
        bound_correctness x iv;
        bound_correctness y iv
     | _ -> ()

let simplify_div (e:expr) : expr = 
  match e with
  | DivOp (AddOp (MulOp x (Literal m1)) z) (Literal m2) ->
     // ( (x * m1) + z) / m1 = x if z < m1
     if m1 = m2 then
        (match bound_value z with
          | Some (lo_z, up_z) ->
             if lo_z >= 0 && up_z < m1 then x else simplify_addition e
          | None -> simplify_addition e)             
     else
        simplify_addition e
  | ModOp (AddOp (MulOp x (Literal m1)) z) (Literal m2) ->
     // ( (x * m1) + z) / m1 = x if z < m1
     if m1 = m2 then
        (match bound_value z with
          | Some (lo_z, up_z) ->
             if lo_z >= 0 && up_z < m1 then z else simplify_addition e
          | None -> simplify_addition e)             
     else
        simplify_addition e
  | DivOp a (Literal b) ->
     (match bound_value a with
      | Some (lo_a, up_a) ->
          if lo_a >= 0 && up_a < b then (Literal 0) else simplify_addition e
      | None -> simplify_addition e
     )
  | _ -> simplify_addition e

#push-options "--z3rlimit 60"
let simplify_div_correctness (e:expr) (iv:input_vals) 
 : Lemma (requires Some? (eval_expr e iv))
         (ensures ( eval_expr e iv = eval_expr (simplify_div e) iv)) =
  match e with 
  | DivOp (AddOp (MulOp x (Literal m1)) z) (Literal m2) ->
    if m1 = m2 then
        (match bound_value z with
          | Some (lo_z, up_z) ->
             bound_correctness z iv;
             if lo_z >= 0 && up_z < m1 then (
                //assert (Some? (eval_expr e iv));
                //assert (Some? (eval_expr (AddOp (MulOp x (Literal m1)) z) iv));
                //assert (Some? (eval_expr (MulOp x (Literal m1)) iv));
                //assert (Some? (eval_expr x iv));
                let x_val = Some?.v (eval_expr x iv) in
                let z_val = Some?.v (eval_expr z iv) in
                // let prodplus = Some?.v (eval_expr (AddOp (MulOp x (Literal m1)) z) iv) in
                // assert( z_val >= 0 );
                // assert( z_val < m1 );
                Math.Lemmas.lemma_div_plus z_val x_val m1;
                Math.Lemmas.small_div z_val m1;              
                // assert( prodplus = z_val + op_Multiply x_val m1);
                // assert( prodplus / m1 = x_val );
                // assert( eval_expr e iv = eval_expr x iv );
                ()
             ) else 
                simplify_addition_correctness e iv
          | None -> simplify_addition_correctness e iv)               
    else
      simplify_addition_correctness e iv
  | DivOp a (Literal b) ->
    (match bound_value a with
      | Some (lo_a, up_a) -> 
         bound_correctness a iv;
         if lo_a >= 0 && up_a < b then
            Math.Lemmas.small_div (Some?.v (eval_expr a iv)) b
         else
            simplify_addition_correctness e iv
      | None -> simplify_addition_correctness e iv
    )
  | ModOp (AddOp (MulOp x (Literal m1)) z) (Literal m2) ->
    if m1 = m2 then
        (match bound_value z with
          | Some (lo_z, up_z) ->
              bound_correctness z iv;
              if lo_z >= 0 && up_z < m1 then (
                let x_val = Some?.v (eval_expr x iv) in
                let z_val = Some?.v (eval_expr z iv) in
                Math.Lemmas.lemma_mod_plus z_val x_val m1;
                Math.Lemmas.small_mod z_val m1
              ) else
                simplify_addition_correctness e iv
          | None -> simplify_addition_correctness e iv
        )
    else
      simplify_addition_correctness e iv
  | _ -> simplify_addition_correctness e iv
#pop-options

let is_equality_known (a:expr) (b:expr) : option bool =
  match (a,b) with
  | (InputValue _),(Literal y) -> if y < 1 || y > 9 then Some false else None
  | (Literal y),(InputValue _) -> if y < 1 || y > 9 then Some false else None
  | (Literal x),(Literal y) -> if x = y then Some true else Some false
  | (AddOp (InputValue _) (Literal y)),(InputValue _) ->
       // Maximum is first input value is 1 and second is 9
       if y > 8 then Some false 
       else if y < (-8) then Some false
       else None
  | (AddOp (ModOp (AddOp (InputValue _) (Literal k)) (Literal 26)) (Literal y)),(InputValue _) ->
       // Maximum is first input value is 1 and second is 9
       let lb = 1 + k in
       let ub = 9 + k in
       if lb < 0 then
          None
       else if ub >= 26 then
          None
       else
          // Cannot happen if lb+y > 9 or
          // ub+y < 1
          if (lb+y) > 9 || (ub+y) < 1 then
             Some false // cannot happen
          else 
             None // might happen
  | _ -> None

let is_equality_known_correct (a:expr) (b:expr) (iv:input_vals) 
 : Lemma (requires (Some? (is_equality_known a b)) /\
                   (Some? (eval_expr a iv)) /\
                   (Some? (eval_expr b iv)))                 
         (ensures (Some?.v (is_equality_known a b ) ==> (Some?.v (eval_expr (EqlOp a b) iv) = 1)) /\
                  (~ (Some?.v (is_equality_known a b )) ==> (Some?.v (eval_expr (EqlOp a b) iv) = 0))) =
  match (a,b) with
  | (AddOp (ModOp (AddOp (InputValue _) (Literal k)) (Literal 26)) (Literal y)),(InputValue _) ->
    let lb = 1 + k in
    let ub = 9 + k in
    Math.Lemmas.small_mod lb 26; 
    Math.Lemmas.small_mod ub 26      
  | _ -> ()

// If both branches are the same, then elide the comparison
let check_case_equality (x1:expr) (y1:expr) (t1:expr) (f1:expr) : expr =
  if t1 = f1 then
     t1
  else match (t1,f1) with
  (* We don't have the vocabulary to express this
     // if 1=2 then
     //    if 3=4 then A else B
     // else
     //    if 5=6 then A else B
     // ==> ????
     | (IfEqElse x2 y2 t2 f2,IfEqElse x3 y3 t3 f3) ->
        if t2 = t3 && f2 = f3 then
  *)
     | _ -> IfEqElse x1 y1 t1 f1

// Push the operation down into the first non-conditional expression in the AST.
// Preserve existing branches if we can.
let rec push_op_into_tree (op:expr->expr->expr) (arg1:expr) (arg2:expr) : expr =
  match (arg1,arg2) with
  | (IfEqElse x1 y1 t1 f1, IfEqElse x2 y2 t2 f2) ->
    if x1 = x2 && y1 = y2 then    
      check_case_equality x1 y1 (push_op_into_tree op t1 t2) (push_op_into_tree op f1 f2)
    else 
      // (if x1 = y1 then t1 else f1) * (if x2 = y2 then t2 else f2)
      // = (if x1 = y1 then (if x2 = y2 then t1 op t2 else
      //                                     t1 op f2 else)
      //               else (if x2 = y2 then f1 op t2 else
      //                                     f1 op f2)
      check_case_equality x1 y1 (push_op_into_tree op t1 (IfEqElse x2 y2 t2 f2))
                     (push_op_into_tree op f1 (IfEqElse x2 y2 t2 f2))
  | (IfEqElse x1 y1 t1 f1, b) ->    
    check_case_equality x1 y1 (push_op_into_tree op t1 b) (push_op_into_tree op f1 b)
  | (a, IfEqElse x2 y2 t2 f2) ->
    check_case_equality x2 y2 (push_op_into_tree op a t2) (push_op_into_tree op a f2)
  | (IfEqElse x1 y1 t1 f1, b) ->    
    check_case_equality x1 y1 (push_op_into_tree op t1 b) (push_op_into_tree op f1 b)
  | (a, IfEqElse x2 y2 t2 f2) ->
    check_case_equality x2 y2 (push_op_into_tree op a t2) (push_op_into_tree op a f2)
  | (a, b) ->
    match (simplify_identity (op a b)) with
    | EqlOp z1 z2 ->
      (match is_equality_known z1 z2 with
       | None -> IfEqElse z1 z2 (Literal 1) (Literal 0)
       | Some false -> Literal 0
       | Some true -> Literal 1
      )
    | e -> (simplify_div e)

let rec push_op_correctness (arg1:expr) (arg2:expr) (iv:input_vals)
 : Lemma (requires (Some? (eval_expr (AddOp arg1 arg2) iv)))
         (ensures (eval_expr (AddOp arg1 arg2) iv) =
                  (eval_expr (push_op_into_tree AddOp arg1 arg2) iv))
  = match (arg1, arg2) with
  | (IfEqElse x1 y1 t1 f1, IfEqElse x2 y2 t2 f2) ->
    if x1 = x2 && y1 = y2 then (   
      if (eval_expr x1 iv) = (eval_expr y1 iv) then (
         assert( eval_expr (AddOp arg1 arg2) iv =
                 eval_expr (AddOp t1 t2) iv);
         push_op_correctness t1 t2 iv
      ) else        
         push_op_correctness f1 f2 iv
    ) else ( 
      if (eval_expr x1 iv) = (eval_expr y1 iv) then (
         push_op_correctness t1 (IfEqElse x2 y2 t2 f2) iv
      ) else (
         push_op_correctness f1 (IfEqElse x2 y2 t2 f2) iv
      )
    )
  | (IfEqElse x1 y1 t1 f1, b) ->    
    if (eval_expr x1 iv) = (eval_expr y1 iv) then (
      push_op_correctness t1 b iv
    ) else 
      push_op_correctness f1 b iv      
  | (a, IfEqElse x2 y2 t2 f2) ->
    if (eval_expr x2 iv) = (eval_expr y2 iv) then
      push_op_correctness a t2 iv
    else 
      push_op_correctness a f2 iv     
  | (a, b) -> 
     simplify_identity_correctness (AddOp a b) iv;
     match simplify_identity (AddOp a b) with
     | EqlOp z1 z2 -> ( match is_equality_known z1 z2 with
         | None -> ()
         | Some _ -> is_equality_known_correct z1 z2 iv
       )
     | _ -> simplify_div_correctness (simplify_identity (AddOp a b)) iv


// What properties do we need from the operator to make the proof above generalize?
type op_constructor = (f:(expr->expr->expr){
  forall a b iv . 
  Some? (eval_expr a iv) /\
  Some? (eval_expr b iv) 
  ==>
  (eval_expr (f a b) iv) =
             (eval_expr (f (Literal (Some?.v (eval_expr a iv)))
                           (Literal (Some?.v (eval_expr b iv)))) iv)
})

[@@expect_failure]
let rec push_op_correctness_2 (op:op_constructor) (arg1:expr) (arg2:expr) (iv:input_vals)
 : Lemma (requires (Some? (eval_expr (op arg1 arg2) iv)))
         (ensures (eval_expr (op arg1 arg2) iv) =
                  (eval_expr (push_op_into_tree op arg1 arg2) iv))
  = match (arg1, arg2) with
  | (IfEqElse x1 y1 t1 f1, IfEqElse x2 y2 t2 f2) ->
    if x1 = x2 && y1 = y2 then (   
      if (eval_expr x1 iv) = (eval_expr y1 iv) then (
         assert( eval_expr (op arg1 arg2) iv =
                 eval_expr (op (IfEqElse x1 y1 t1 f1) (IfEqElse x2 y2 t2 f2)) iv);
         assert( eval_expr (op arg1 arg2) iv =
                 eval_expr (op t1 t2) iv);
         push_op_correctness t1 t2 iv
      ) else        
         push_op_correctness f1 f2 iv
    ) else ( 
      if (eval_expr x1 iv) = (eval_expr y1 iv) then (
         push_op_correctness t1 (IfEqElse x2 y2 t2 f2) iv
      ) else (
         push_op_correctness f1 (IfEqElse x2 y2 t2 f2) iv
      )
    )
  | (IfEqElse x1 y1 t1 f1, b) ->    
    if (eval_expr x1 iv) = (eval_expr y1 iv) then (
      push_op_correctness t1 b iv
    ) else 
      push_op_correctness f1 b iv      
  | (a, IfEqElse x2 y2 t2 f2) ->
    if (eval_expr x2 iv) = (eval_expr y2 iv) then
      push_op_correctness a t2 iv
    else 
      push_op_correctness a f2 iv     
  | (a, b) -> 
     simplify_identity_correctness (op a b) iv;
     match simplify_identity (op a b) with
     | EqlOp z1 z2 -> ( match is_equality_known z1 z2 with
         | None -> ()
         | Some _ -> is_equality_known_correct z1 z2 iv
       )
     | _ -> simplify_div_correctness (simplify_identity (op a b)) iv

let set_value (regs:alu_registers) (v:var_name) (op:expr->expr->expr) (arg1:expr) (arg2:expr)
  : alu_registers =
 store_value regs v (push_op_into_tree op arg1 arg2)

let rec symbolic_execution 
  (prog:list alu_inst) (regs:alu_registers)
 : ML alu_registers = 
  match prog with
  | [] -> regs
  | curr :: rest ->
    // print_registers regs;
    symbolic_execution rest
    ( let gv = get_value regs in
      match curr with 
     | Inp v -> 
        let iv = regs.next_input in
           { (store_value regs v (InputValue iv))
             with next_input = 
               if iv = 13 then 13 else iv+1}
     | Add v1 v2 ->
        set_value regs v1 AddOp (gv v1) (gv v2)
     | Addi v1 v2 ->
        set_value regs v1 AddOp (gv v1) (Literal v2)
     | Mul v1 v2 ->
        set_value regs v1 MulOp (gv v1) (gv v2)
     | Muli v1 v2 ->
        set_value regs v1 MulOp (gv v1) (Literal v2)
     | Div v1 v2 ->
        set_value regs v1 DivOp (gv v1) (gv v2)
     | Divi v1 v2 ->
        set_value regs v1 DivOp (gv v1) (Literal v2)
     | Mod v1 v2 ->
        set_value regs v1 ModOp (gv v1) (gv v2)
     | Modi v1 v2 ->
        set_value regs v1 ModOp (gv v1) (Literal v2)
     | Eql v1 v2 ->
        set_value regs v1 EqlOp (gv v1) (gv v2)
     | Eqli v1 v2 ->
        set_value regs v1 EqlOp (gv v1) (Literal v2)
     )

type init_registers = {
  w=(Literal 0);
  x=(Literal 0);
  y=(Literal 0);
  z=(Literal 0);
  next_input=0;
}

// We can't use an integer type here because
// there's no way to pattern match on Some (-1)!
type sign =
  | Unknown
  | Positive
  | Negative
  | Zero

let rec sign_of (e:expr) : sign =
  match e with 
  | InputValue _ -> Positive
  | Literal z -> if z = 0 then Zero else
    if z < 0 then Negative else Positive
  | AddOp a b -> (
    match (sign_of a, sign_of b) with
    | (Negative,Negative) -> Negative
    | (Positive,Positive) -> Positive
    | (Zero,s) -> s
    | (s,Zero) -> s
    | _ -> Unknown
  )
  | MulOp a b -> (
    match (sign_of a, sign_of b) with
    | (Positive,Positive) -> Positive
    | (Zero,_) -> Zero
    | (_,Zero) -> Zero
    | (Negative,Negative) -> Positive
    | (Positive,Negative) -> Negative
    | (Negative,Positive) -> Negative
    | _ -> Unknown
  )
  | DivOp _ _ -> Unknown
  | ModOp _ _ -> Unknown
  | EqlOp _ _ -> Unknown
  | IfEqElse _ _ _ _  -> Unknown
  
let rec print_equalities (conditions:list (bool*expr*expr)) : ML unit =
  match conditions with
  | [] -> ()
  | (eq,x,y) :: tl -> 
    print_expr x 0;
    (if eq then print_string " == " else print_string " <> ");
    print_expr y 0;
    (if List.Tot.length tl > 0 then print_string " /\\\n" else print_string "\n");
    print_equalities tl

// True if expression only uses input <= input_num
let rec expr_uses_inputs_up_to (input_num:int) (e:expr) : Tot bool =
 match e with
 | InputValue i -> i <= input_num
 | Literal _ -> true
 | AddOp a b 
 | MulOp a b 
 | DivOp a b 
 | ModOp a b 
 | EqlOp a b -> expr_uses_inputs_up_to input_num a &&
               expr_uses_inputs_up_to input_num b
 | IfEqElse x y t f ->
      expr_uses_inputs_up_to input_num x &&
      expr_uses_inputs_up_to input_num y &&
      expr_uses_inputs_up_to input_num t &&
      expr_uses_inputs_up_to input_num f

let rec print_list_aux (l:list int) : ML unit =
  match l with
  | [] -> ()
  | hd :: [] -> print_string (sprintf "%d" hd)
  | hd :: tl -> print_string (sprintf "%d; " hd);
               print_list_aux tl
  
let print_list (l:list int) : ML unit =
  print_string "[";
  print_list_aux l;
  print_string "]"

let rec largest_input (vals:input_vals) (n:int{1 <= n /\ n <= 9}) 
  (conditions:list (bool*expr*expr)) : ML (option input_vals) =
  //print_string "Trying ";
  //print_list (List.Tot.list_unref vals);
  //print_string (sprintf " @ [%d]\n" n ); 
  if List.Tot.length vals = 14 then
    Some vals
  else let attempt = List.Tot.snoc (vals,n) in
       let var_index = List.Tot.length vals in
       let applicable = List.Tot.filter 
          (fun (e,x,y) -> expr_uses_inputs_up_to var_index x &&
          expr_uses_inputs_up_to var_index y )
          conditions in
       //print_string (sprintf "%d applicable constraints\n" (List.Tot.length applicable));
       if List.Tot.for_all 
          (fun (e,x,y) -> 
            if e then 
               eval_expr x attempt = eval_expr y attempt
            else
               eval_expr x attempt <> eval_expr y attempt
          )
          applicable then
          // it worked, try next variable
          match (largest_input attempt 9 conditions) with
          | Some l -> Some l  // sub-problem succeeded
          | None ->           // sub-problem failed, try the next value
             if n = 1 then None else
             (largest_input vals (n-1) conditions)             
       else   
          // Value is wrong, try next-smallest
          if n = 1 then None else
          (largest_input vals (n-1) conditions)             

let rec smallest_input (vals:input_vals) (n:int{1 <= n /\ n <= 9}) 
  (conditions:list (bool*expr*expr)) : ML (option input_vals) =
  //print_string "Trying ";
  //print_list (List.Tot.list_unref vals);
  //print_string (sprintf " @ [%d]\n" n ); 
  if List.Tot.length vals = 14 then
    Some vals
  else let attempt = List.Tot.snoc (vals,n) in
       let var_index = List.Tot.length vals in
       let applicable = List.Tot.filter 
          (fun (e,x,y) -> expr_uses_inputs_up_to var_index x &&
          expr_uses_inputs_up_to var_index y )
          conditions in
       //print_string (sprintf "%d applicable constraints\n" (List.Tot.length applicable));
       if List.Tot.for_all 
          (fun (e,x,y) -> 
            if e then 
               eval_expr x attempt = eval_expr y attempt
            else
               eval_expr x attempt <> eval_expr y attempt
          )
          applicable then
          // it worked, try next variable
          match (smallest_input attempt 1 conditions) with
          | Some l -> Some l  // sub-problem succeeded
          | None ->           // sub-problem failed, try the next value
             if n = 9 then None else
             (smallest_input vals (n+1) conditions)             
       else   
          // Value is wrong, try next-smallest
          if n = 9 then None else
          (smallest_input vals (n+1) conditions)             

let rec print_possible_zeros (e:expr) (conditions:list (bool*expr*expr)) : ML unit =
  match e with
  | IfEqElse x y t f -> 
       print_possible_zeros t (List.Tot.snoc (conditions,(true,x,y)));
       print_possible_zeros f (List.Tot.snoc (conditions,(false,x,y)))
  | _ -> match sign_of e with
     | Zero -> (
        print_equalities conditions;
        print_string "  ==> ";
        print_expr e 0;
        print_string "\n";
        match largest_input [] 9 conditions with
        | None -> print_string "unsatisfiable\n"
        | Some l -> print_string "largest:\n"; print_list (List.Tot.list_unref l); print_string "\n"
        ;
        match smallest_input [] 1 conditions with
        | None -> print_string "unsatisfiable\n"
        | Some l -> print_string "smallest:\n"; print_list (List.Tot.list_unref l); print_string "\n"        
     )
     | Unknown ->
        print_equalities conditions;
        print_string "  ?? ==> ";
        print_expr e 0;
        print_string "\n"       
     | _ -> ()
     
let print_program () : ML unit =
  let regs = symbolic_execution input_program init_registers in
    //print_expr regs.z 0
    print_possible_zeros regs.z []

let _ = print_program()

