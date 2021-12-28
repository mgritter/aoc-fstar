module Part1

open FStar.IO
open FStar.All
open FStar.Printf

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
           
let simplify_addition (e:expr) : expr =
  match e with
  | AddOp (Literal x) (AddOp a b) 
  | AddOp (AddOp a b) (Literal x) -> (
     match constant_fold (AddOp a b) x with
     | None -> (AddOp (AddOp a b) (Literal x))
     | Some f -> simplify_identity f       
  )
  | _ -> simplify_identity e

let simplify_add_mod (e:expr) : expr = 
  match e with
  | AddOp a (ModOp b m) -> (ModOp (simplify_addition (AddOp a b)) m)
  | AddOp (ModOp a m) b -> (ModOp (simplify_addition (AddOp a b)) m)
  | _ -> simplify_addition e

let rec bound_value (e:expr) : option (int*int) =
  match e with
  | InputValue _ -> Some (1,9)
  | Literal z -> Some (z,z)
  | AddOp x y -> (match (bound_value x),(bound_value y)  with
      | (Some (lo_x,up_x), Some (lo_y,up_y)) -> Some ((lo_x + lo_y),( up_x + up_y))
      | _ -> None
    )
  | _ -> None

let simplify_div (e:expr) : expr = 
  match e with
  | DivOp (AddOp (MulOp x (Literal m1)) z) (Literal m2) ->
     // ( (x * m1) + z) / m1 = x if z < m1
     if m1 = m2 then
        (match bound_value z with
          | Some (lo_z, up_z) ->
             if lo_z >= 0 && up_z < m1 then x else simplify_add_mod e
          | None -> simplify_add_mod e)             
     else
        simplify_add_mod e
  | ModOp (AddOp (MulOp x (Literal m1)) z) (Literal m2) ->
     // ( (x * m1) + z) / m1 = x if z < m1
     if m1 = m2 then
        (match bound_value z with
          | Some (lo_z, up_z) ->
             if lo_z >= 0 && up_z < m1 then z else simplify_add_mod e
          | None -> simplify_add_mod e)             
     else
        simplify_add_mod e
  | DivOp a (Literal b) ->
     (match bound_value a with
      | Some (lo_a, up_a) ->
          if lo_a >= 0 && up_a < b then (Literal 0) else simplify_add_mod e
      | None -> simplify_add_mod e
     )
  | _ -> simplify_add_mod e
  
let set_value_add (regs:alu_registers) (v:var_name) (e:expr) 
 : Tot alu_registers = 
 match v with
  | W -> {regs with w = simplify_add_mod e}
  | X -> {regs with x = simplify_add_mod e}
  | Y -> {regs with y = simplify_add_mod e}
  | Z -> {regs with z = simplify_add_mod e}

let is_equality_known (a:expr) (b:expr) : option bool =
  match (a,b) with
  | (InputValue _),(Literal y) -> if y < 1 || y > 9 then Some false else None
  | (Literal y),(InputValue _) -> if y < 1 || y > 9 then Some false else None
  | (Literal x),(Literal y) -> if x = y then Some true else Some false
  | _ -> None

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
  | (a, b) ->
    match (simplify_identity (op a b)) with
    | EqlOp z1 z2 ->
      (match is_equality_known z1 z2 with
       | None -> IfEqElse z1 z2 (Literal 1) (Literal 0)
       | Some false -> Literal 0
       | Some true -> Literal 1
      )
    | e -> (simplify_div e)

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

let rec sign (e:expr) : some (z:int{z = 0 /\ z = (-1) /\ z = 1})  =
  match e with 
  | InputValue _ -> Some 1
  | Literal z -> if z = 0 then Some 0 else
    if z < 0 then Some (-1) else Some 1
  | AddOp a b -> (
    match (sign a, sign b) with
    | None -> None
    | (Some (-1),Some (-1)) -> Some (-1)
    | (Some 1,Some 1) -> Some 1
    | (Some 0,Some s) -> Some s
    | (Some s,Some 0) -> Some s
    | _ -> None
  | MulOp a b -> (
    match (sign a, sign b) with
    | None -> None
    | (Some 1,Some 1) -> Some 1
    | (Some 0,Some s) -> Some 0
    | (Some s,Some 0) -> Some 0
    | (Some (-1),Some (-1)) -> Some 1
    | (Some 1, Some (-1)) -> Some (-1)
    | (Some (-1), Some 1) -> Some (-1)
  )
  | DivOp _ _ -> None
  | ModOp _ _ -> None
  | EqlOp _ _ -> None
  | IfThenElse _ _ _ _  -> None

let find_zeros (e:expr) (conditions:list (bool*expr)) : ML unit =
  


let print_program () : ML unit =
  let regs = symbolic_execution input_program init_registers in
    print_expr regs.z 0

let _ = print_program()

