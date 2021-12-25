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
 | TempVar : (index:nat) -> expr
 | Literal : (z:int) -> expr
 | AddOp : (a:expr) -> (b:expr) -> expr
 | MulOp : (a:expr) -> (b:expr) -> expr
 | DivOp : (a:expr) -> (b:expr) -> expr
 | ModOp : (a:expr) -> (b:expr) -> expr
 | EqlOp : (a:expr) -> (b:expr) -> expr

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

  sso: list expr;
}

let rec print_spaces (n:nat) : ML unit =
  if n = 0 then () else (
    print_string " ";
    print_spaces (n-1)
  )
  
let rec print_expr (e:expr) (depth:nat) : ML unit =
  match e with 
   | InputValue i -> print_string (sprintf "i_%d " i)
   | TempVar i -> print_string (sprintf "t_%d " i)
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

let print_registers (regs:alu_registers) : ML unit =
  print_string "W: ";
  print_expr regs.w 0;
  print_string "X: ";
  print_expr regs.x 0;
  print_string "Y: ";
  print_expr regs.y 0;
  print_string "Z: ";
  print_expr regs.z 0;
  print_string "\n"

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
   | Literal i -> Literal i
   | InputValue  i -> InputValue i
   | TempVar i -> TempVar i

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

let set_value (regs:alu_registers) (v:var_name) (e:expr) 
 : ML alu_registers = 
 let e2 = simplify_identity e in
 if e <> e2 || InputValue? e2 then
   store_value regs v e2
 else
   let new_sso = List.Tot.snoc (regs.sso,e) in
     let tmp_var = TempVar (List.Tot.length new_sso - 1) in
       print_expr tmp_var 0;
       print_string " := ";
       print_expr e 0;
       print_string "\n";
       {(store_value regs v tmp_var) 
         with sso = new_sso }

// (+ (% (+ i_0 7 ) 26 ) 11 )
//
// (% (+ i_0 18) 26)
let simplify_addition (e:expr) : expr =
  match e with
  | AddOp (Literal x) (AddOp a (Literal b)) -> AddOp a (Literal (x+b))
  | AddOp (Literal x) (AddOp (Literal a) b) -> AddOp (Literal (x+a)) b
  | AddOp (AddOp a (Literal b)) (Literal x) -> (AddOp a (Literal (b+x)))
  | AddOp (AddOp (Literal a) b) (Literal x) -> (AddOp (Literal (a+x)) b)
  | _ -> simplify_identity e

let simplify_add_mod (e:expr) : expr = 
  match e with
  | AddOp a (ModOp b m) -> (ModOp (simplify_addition (AddOp a b)) m)
  | AddOp (ModOp a m) b -> (ModOp (simplify_addition (AddOp a b)) m)
  | _ -> simplify_addition e

let set_value_add (regs:alu_registers) (v:var_name) (e:expr) 
 : Tot alu_registers = 
 match v with
  | W -> {regs with w = simplify_add_mod e}
  | X -> {regs with x = simplify_add_mod e}
  | Y -> {regs with y = simplify_add_mod e}
  | Z -> {regs with z = simplify_add_mod e}

(*
let simplify_equality (e:expr) : expr = 
  match e with
  | EqlOp (Cond n) (Literal 0) -> NotCond n
  | _ -> simplify_identity e
*)

let rec symbolic_execution 
  (prog:list alu_inst) (regs:alu_registers)
 : ML alu_registers = 
  match prog with
  | [] -> regs
  | curr :: rest ->
    symbolic_execution rest
    ( let gv = get_value regs in
      match curr with 
     | Inp v -> 
        let iv = regs.next_input in
           { (set_value regs v (InputValue iv))
             with next_input = 
               if iv = 13 then 13 else iv+1}
     | Add v1 v2 ->
        (set_value regs v1 (AddOp (gv v1) (gv v2)))
     | Addi v1 v2 ->
        (set_value regs v1 (AddOp (gv v1) (Literal v2)))
     | Mul v1 v2 ->
        (set_value regs v1 (MulOp (gv v1) (gv v2)))
     | Muli v1 v2 ->
        (set_value regs v1 (MulOp (gv v1) (Literal v2)))
     | Div v1 v2 ->
        (set_value regs v1 (DivOp (gv v1) (gv v2)))
     | Divi v1 v2 ->
        (set_value regs v1 (DivOp (gv v1) (Literal v2)))
     | Mod v1 v2 ->
        (set_value regs v1 (ModOp (gv v1) (gv v2)))
     | Modi v1 v2 ->
        (set_value regs v1 (ModOp (gv v1) (Literal v2)))
     | Eql v1 v2 ->
        (set_value regs v1 (EqlOp (gv v1) (gv v2)))
     | Eqli v1 v2 ->
        (set_value regs v1 (EqlOp (gv v1) (Literal v2)))
     )

type init_registers = {
  w=(Literal 0);
  x=(Literal 0);
  y=(Literal 0);
  z=(Literal 0);
  next_input=0;
  sso=[];
}

let print_program () : ML unit =
  let regs = symbolic_execution input_program init_registers in
    print_expr regs.z 0

let _ = print_program()

