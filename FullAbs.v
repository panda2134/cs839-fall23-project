Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Program.Wf.
Require Import Recdef.

Inductive Expr: Type :=
    Num: Z -> Expr
  | Plus: Expr -> Expr -> Expr
  | Minus: Expr -> Expr -> Expr
  | VarX: Expr
  | VarY: Expr
  | LetX: Expr -> Expr -> Expr
  | LetY: Expr -> Expr -> Expr
  | IteZero: Expr -> Expr -> Expr -> Expr
  .


(* cannot handle func call: recursiveness? *)
(* I even don't know how to handle it when recursing is not allowed! *)

Fixpoint evalExpr (e: Expr) (varX: Z) (varY: Z): Z :=
  match e with
  | Num n => n
  | Plus e1 e2 => (evalExpr e1 varX varY) + (evalExpr e2 varX varY)
  | Minus e1 e2 => (evalExpr e1 varX varY) - (evalExpr e2 varX varY)
  | VarX => varX
  | VarY => varY
  | LetX e1 e2 => let varX' := (evalExpr e1 varX varY) in (evalExpr e2 varX' varY)
  | LetY e1 e2 => let varY' := (evalExpr e1 varX varY) in (evalExpr e2 varX varY')
  | IteZero ec el er =>
       let cond := (evalExpr ec varX varY) in
       let l := (evalExpr el varX varY) in
       let r := (evalExpr er varX varY) in
       match cond with
       | Z0 => l
       | _ => r
       end
  end.

Example E1: (Z.to_nat (evalExpr (Plus (Num 3) VarX) 2 3)) = 5.
Proof.
  auto.
Qed.

Example E2: (Z.to_nat (evalExpr (IteZero (Minus (Num 1) (Num 1)) VarX VarY) 3 5)) = 3.
Proof. unfold evalExpr. auto.
Qed.

Inductive Instr: Type := 
    IPlus: Instr
  | IMinus: Instr
  | ICondPick: Instr (* Remove all 3 elements. If StackTop is Zero then Pick StackTop-1 else Pick StackTop-2 *)
  | ILoadX: Instr    (* Pop *)
  | ILoadY: Instr
  | IPop: Instr
  | IStoreX: Instr   (* Push *)
  | IStoreY: Instr
  | IStoreImm: Z -> Instr
  | IDup: Instr
  | ISwap: Instr.

Fixpoint evalInstr (prog: (list Instr)) (stack: list Z) (regX: Z) (regY: Z): option (list Z) :=
  match (prog, stack) with
  | (nil, result) => Some(result)
  | (IPlus :: prog', n1 :: n2 :: rest) => (evalInstr prog' ((n2 + n1)%Z :: rest) regX regY)
  | (IMinus :: prog', n1 :: n2 :: rest) => (evalInstr prog' ((n2 - n1)%Z :: rest) regX regY)
  | (ICondPick :: prog', cond :: l :: r :: rest) =>
    match cond with
    | Z0 => (evalInstr prog' (l :: rest) regX regY)
    | _ => (evalInstr prog' (r :: rest) regX regY)
    end
  | (ILoadX :: prog', n :: rest) => (evalInstr prog' rest n regY)
  | (ILoadY :: prog', n :: rest) => (evalInstr prog' rest regX n)
  | (IStoreX :: prog', _) => (evalInstr prog' (regX :: stack) regX regY)
  | (IStoreY :: prog', _) => (evalInstr prog' (regY :: stack) regX regY)
  | ((IStoreImm imm) :: prog', _) => (evalInstr prog' (imm :: stack) regX regY)
  | (IPop :: prog', n :: rest) => (evalInstr prog' rest regX regY)
  | (IDup :: prog', n :: rest) => (evalInstr prog' (n :: n :: rest) regX regY)
  | (ISwap :: prog', n1 :: n2 :: rest) => (evalInstr prog' (n2 :: n1 :: rest) regX regY)
  | (_, _) => None
  end.

Example IE1: (evalInstr (IDup :: IPlus :: nil) (1%Z :: nil) 0 0) = Some(2%Z :: nil).
Proof.
  unfold evalInstr.
  auto.
Qed.

Search Expr.

Fixpoint compile (e: Expr): list Instr :=
  match e with
  | VarX => [IStoreX]
  | VarY => [IStoreY]
  | LetX e1 e2 =>
    let e1Prog := (compile e1) in
    let e2Prog := (compile e2) in
    e1Prog ++ [IStoreX ; ISwap ; ILoadX] ++ e2Prog ++ [ISwap; ILoadX]
  | LetY e1 e2 =>
    let e1Prog := (compile e1) in
    let e2Prog := (compile e2) in
    e1Prog ++ [IStoreY ; ISwap ; ILoadY] ++ e2Prog ++ [ISwap; ILoadY]
  | Num n => [(IStoreImm n)]
  | Plus e1 e2 => 
    let e1Prog := (compile e1) in
    let e2Prog := (compile e2) in
    e1Prog ++ e2Prog ++ [IPlus]
  | Minus e1 e2 => 
    let e1Prog := (compile e1) in
    let e2Prog := (compile e2) in
    e1Prog ++ e2Prog ++ [IMinus]
  | IteZero ec el er =>
    let elProg := (compile el) in
    let erProg := (compile er) in
    let ecProg := (compile ec) in
    erProg ++ elProg ++ ecProg ++ [ICondPick]
  end.

Compute evalInstr (compile (LetX (Num 1) (LetX (Num 2) VarX))) [] 0 0.

Function stackTop (xs: option (list Z)): option Z :=
  match xs with
  | None => None
  | Some(nil) => None
  | Some(x :: rest) => Some(x)
  end.

Lemma step_correct: forall e: Expr, forall x0 y0: Z, forall progs: list Instr, forall st: list Z,
  (evalInstr ((compile e) ++ progs) st x0 y0) = (evalInstr progs ((evalExpr e x0 y0) :: st) x0 y0).
Proof.
  induction e.
  - (*Num*) auto.
  - (*Plus*) simpl.
    intros x0 y0 progs st. repeat rewrite <- app_assoc.
    rewrite IHe1. rewrite IHe2. simpl. reflexivity.
  - (*Minus*) simpl.
    intros x0 y0 progs st. repeat rewrite <- app_assoc.
    rewrite IHe1. rewrite IHe2. simpl. reflexivity.
  - (*VarX*) auto.
  - (*VarY*) auto.
  - (*LetX*) simpl.
    intros x0 y0 progs st.
    repeat rewrite <- app_assoc.
    rewrite IHe1. simpl.
    repeat rewrite <- app_assoc.
    rewrite IHe2. reflexivity.
  - (*LetY*) simpl.
    intros x0 y0 progs st.
    repeat rewrite <- app_assoc.
    rewrite IHe1. simpl.
    repeat rewrite <- app_assoc.
    rewrite IHe2. reflexivity.
  - (*IteZero*) intros x0 y0 progs st.
    simpl (compile (IteZero e1 e2 e3) ++ progs). repeat rewrite <- app_assoc. rewrite IHe3. rewrite IHe2. rewrite IHe1.
    simpl (evalInstr ([ICondPick] ++ progs) (evalExpr e1 x0 y0 :: evalExpr e2 x0 y0 :: evalExpr e3 x0 y0 :: st) x0 y0).
    destruct (evalExpr e1 x0 y0) eqn:condLeft.
    all: try simpl (evalInstr progs (evalExpr (IteZero e1 e2 e3) x0 y0 :: st) x0 y0).
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (evalExpr e2 x0 y0). all:repeat auto.
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (evalExpr e3 x0 y0). all:reflexivity.
    * simpl. destruct (evalExpr e1 x0 y0).
      + discriminate. + reflexivity. + reflexivity.
Qed.

Theorem compiler_correct: forall e: Expr, forall x0 y0: Z,
  Some(evalExpr e x0 y0) = stackTop (evalInstr (compile e) [] x0 y0).
Proof.
  assert (forall e: Expr, forall x0 y0: Z,
      evalInstr (compile e ++ []) [] x0 y0 = evalInstr (compile e) [] x0 y0).
  - intros. rewrite app_nil_r. reflexivity.
  - intros. rewrite <- H. rewrite step_correct. reflexivity.
Qed.
