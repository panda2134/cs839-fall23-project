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
  | IteZero: Expr -> Expr -> Expr -> Expr
  .

Inductive Stmt: Type :=
    LetX: Expr -> Stmt -> Stmt
  | LetY: Expr -> Stmt -> Stmt
  | Write: Expr -> Stmt
  | Seq: Stmt -> Stmt -> Stmt
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
  | IteZero ec el er =>
       let cond := (evalExpr ec varX varY) in
       let l := (evalExpr el varX varY) in
       let r := (evalExpr er varX varY) in
       match cond with
       | Z0 => l
       | _ => r
       end
  end.

Fixpoint evalStmt (s: Stmt) (varX: Z) (varY: Z) : list Z :=
  match s with
  | LetX e1 e2 => let varX' := (evalExpr e1 varX varY) in 
                    (evalStmt e2 varX' varY)
  | LetY e1 e2 => let varY' := (evalExpr e1 varX varY) in
                    (evalStmt e2 varX varY')
  | Write e => [(evalExpr e varX varY)]
  | Seq p q => (evalStmt p varX varY) ++ (evalStmt q varX varY)
  end.

Example E1: (Z.to_nat (evalExpr (Plus (Num 3) VarX) 2 3)) = 5.
Proof.
  auto.
Qed.

Example E2: (Z.to_nat (evalExpr (IteZero (Minus (Num 1) (Num 1)) VarX VarY) 3 5)) = 3.
Proof. unfold evalExpr. auto.
Qed.

Example E3: ((evalStmt (Seq (LetX (Num 1) (LetY (Num 2) (Write VarX))) (Write VarY)) 3 4) = [1%Z; 4%Z]).
Proof. unfold evalStmt. simpl. reflexivity.
Qed.

Inductive Instr: Type := 
    IPlus: Instr
  | IMinus: Instr
  | ICondPick: Instr (* Remove all 3 elements. If StackTop is Zero then Pick StackTop-1 else Pick StackTop-2 *)
  | IWrite: Instr    (* Write Stack Top to Output*)
  | ILoadX: Instr    (* Pop *)
  | ILoadY: Instr
  | IPop: Instr
  | IStoreX: Instr   (* Push *)
  | IStoreY: Instr
  | IStoreImm: Z -> Instr
  | IDup: Instr
  | ISwap: Instr.

(* return: stack & write events *)
Fixpoint evalInstr (prog: (list Instr)) (stack: list Z) (regX: Z) (regY: Z): option (list Z * list Z) :=
  match (prog, stack) with
  | (nil, result) => Some(result, [])
  | (IPlus :: prog', n1 :: n2 :: rest) => (evalInstr prog' ((n2 + n1)%Z :: rest) regX regY)
  | (IMinus :: prog', n1 :: n2 :: rest) => (evalInstr prog' ((n2 - n1)%Z :: rest) regX regY)
  | (IWrite :: prog', n :: rest) => match (evalInstr prog' stack regX regY) with
                                    | Some(stack', evt') => Some(stack', n :: evt')
                                    | None => None
                                    end
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

Example InstrE1: (evalInstr (IDup :: IPlus :: nil) (1%Z :: nil) 0 0) = Some([2%Z], []).
Proof.
  unfold evalInstr.
  auto.
Qed.

Example InstrE2: (evalInstr (IStoreX :: IWrite :: IPop :: nil) [] 3%Z 4%Z) = Some([], [3%Z]).
Proof.
  auto.
Qed.

Fixpoint compileExpr (e: Expr): list Instr :=
  match e with
  | VarX => [IStoreX]
  | VarY => [IStoreY]
  | Num n => [(IStoreImm n)]
  | Plus e1 e2 => 
    let e1Prog := (compileExpr e1) in
    let e2Prog := (compileExpr e2) in
    e1Prog ++ e2Prog ++ [IPlus]
  | Minus e1 e2 => 
    let e1Prog := (compileExpr e1) in
    let e2Prog := (compileExpr e2) in
    e1Prog ++ e2Prog ++ [IMinus]
  | IteZero ec el er =>
    let elProg := (compileExpr el) in
    let erProg := (compileExpr er) in
    let ecProg := (compileExpr ec) in
    erProg ++ elProg ++ ecProg ++ [ICondPick]
  end.

Fixpoint compileStmt (s: Stmt): list Instr :=
  match s with
  | LetX e1 e2 =>
    let e1Prog := (compileExpr e1) in
    let e2Prog := (compileStmt e2) in
    e1Prog ++ [IStoreX ; ISwap ; ILoadX] ++ e2Prog ++ [ILoadX]
  | LetY e1 e2 =>
    let e1Prog := (compileExpr e1) in
    let e2Prog := (compileStmt e2) in
    e1Prog ++ [IStoreY ; ISwap ; ILoadY] ++ e2Prog ++ [ILoadY]
  | Write e => (compileExpr e) ++ [IWrite; IPop]
  | Seq e1 e2 =>
    let e1Prog := (compileStmt e1) in
    let e2Prog := (compileStmt e2) in
    e1Prog ++ e2Prog
  end.

Compute compileStmt (LetX (Num 1) (Write VarX)).

Example CE1: evalInstr (compileStmt (LetX (Num 1) (LetX (Num 2) (Write VarX)))) [] 0 0 = Some([], [2%Z]).
Proof. simpl. reflexivity.
Qed.

Lemma step_correct_expr: forall e: Expr, forall x0 y0: Z, forall progs: list Instr, forall st: list Z,
  (evalInstr ((compileExpr e) ++ progs) st x0 y0) = (evalInstr progs ((evalExpr e x0 y0) :: st) x0 y0).
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
  - (*IteZero*) intros x0 y0 progs st.
    simpl (compileExpr (IteZero e1 e2 e3) ++ progs). repeat rewrite <- app_assoc. rewrite IHe3. rewrite IHe2. rewrite IHe1.
    simpl (evalInstr ([ICondPick] ++ progs) (evalExpr e1 x0 y0 :: evalExpr e2 x0 y0 :: evalExpr e3 x0 y0 :: st) x0 y0).
    destruct (evalExpr e1 x0 y0) eqn:condLeft.
    all: try simpl (evalInstr progs (evalExpr (IteZero e1 e2 e3) x0 y0 :: st) x0 y0).
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (evalExpr e2 x0 y0). all:repeat auto.
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (evalExpr e3 x0 y0). all:reflexivity.
    * simpl. destruct (evalExpr e1 x0 y0).
      + discriminate. + reflexivity. + reflexivity.
Qed.

Lemma step_correct_stmt: forall s: Stmt, forall x0 y0: Z, forall progs: list Instr, forall st: list Z,
  let e1 := (evalInstr ((compileStmt s) ++ progs) st x0 y0) in
  let evt0 := (evalStmt s x0 y0) in
  let e2 := (evalInstr progs st x0 y0) in
  let l := match e1 with
           | None => None
           | Some(_, evt) => Some(evt)
           end in
  let r := match e2 with
           | None => None
           | Some(_, evt) => Some(evt0 ++ evt)
           end in
  l = r.
Proof.
  induction s.
  - (*LetX*) simpl.
    intros x0 y0 progs st.
    repeat rewrite <- app_assoc.
    simpl in IHs. rewrite -> step_correct_expr. simpl. rewrite <- app_assoc. rewrite IHs. simpl.
    reflexivity.
  - (*LetY*) simpl.
    intros x0 y0 progs st.
    repeat rewrite <- app_assoc.
    simpl in IHs. rewrite -> step_correct_expr. simpl. rewrite <- app_assoc. rewrite IHs. simpl.
    reflexivity.
  - (*Write*) simpl.
    intros x0 y0 progs st.
    assert (((compileExpr e ++ [IWrite; IPop]) ++ progs) = (compileExpr e ++ [IWrite; IPop] ++ progs)) as H.
    + rewrite app_assoc. reflexivity.
    + rewrite H. rewrite step_correct_expr. simpl. destruct (evalInstr progs st x0 y0) as [p|].
      * destruct p. reflexivity.
      * reflexivity.
  - (*Seq*) simpl in IHs1. simpl in IHs2. intros x0 y0 progs st. simpl.
    rewrite <- app_assoc. rewrite IHs1. destruct_with_eqn (evalInstr (compileStmt s2 ++ progs) st x0 y0).
    destruct_with_eqn (evalInstr progs st x0 y0).
    + specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. rewrite Heqo0 in IHs2.
      destruct_with_eqn p. destruct_with_eqn p0. rewrite <- app_assoc. inversion IHs2.
      reflexivity.
    + destruct p. exfalso. specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. rewrite Heqo0 in IHs2. inversion IHs2.
    + specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. destruct_with_eqn (evalInstr progs st x0 y0).
      ++ destruct_with_eqn p. exfalso. inversion IHs2.
      ++ reflexivity.
Qed.

Theorem compiler_correct: forall s: Stmt, forall x0 y0: Z, exists st': list Z,
  evalInstr (compileStmt s) [] x0 y0 = Some(st', evalStmt s x0 y0).
Proof.
  assert (forall s: Stmt, forall x0 y0: Z,
      evalInstr (compileStmt s ++ []) [] x0 y0 = evalInstr (compileStmt s) [] x0 y0).
  - intros. rewrite app_nil_r. reflexivity.
  - intros. rewrite <- H. destruct_with_eqn (evalInstr (compileStmt s ++ []) [] x0 y0).
    + destruct p eqn:Hp. pose proof (step_correct_stmt s x0 y0 [] []) as HC. rewrite Heqo in HC. simpl in HC. rewrite app_nil_r in HC.
      inversion HC. exists l. rewrite <- H1. reflexivity.
    + exfalso. destruct (evalInstr (compileStmt s ++ []) [] x0 y0) eqn:? in Heqo.
      ++ inversion Heqo.
      ++ pose proof (step_correct_stmt s x0 y0 [] []) as HC. rewrite Heqo0 in HC. simpl in HC. inversion HC.
Qed.

(* TODO: allow infinite registers by changing state from (x, y) into a dict *)

Inductive StmtContext: Type :=
    CHole: StmtContext
  | CWrite: Expr -> StmtContext
  | CLetX: Expr -> StmtContext -> StmtContext
  | CLetY: Expr -> StmtContext -> StmtContext
  | CSeqL: StmtContext -> Stmt -> StmtContext
  | CSeqR: Stmt -> StmtContext -> StmtContext
  .

Fixpoint link_to_context (s: Stmt) (ctx: StmtContext): Stmt :=
  match ctx with
  | CWrite e => (Write e)
  | CHole => s
  | CLetX e ctx' => LetX e (link_to_context s ctx')
  | CLetY e ctx' => LetY e (link_to_context s ctx')
  | CSeqL ctx' s' => Seq (link_to_context s ctx') s'
  | CSeqR s' ctx' => Seq s' (link_to_context s ctx')
  end.

Example LE1: (evalInstr (compileStmt (link_to_context (Write VarX) (CLetX (Num 1) (CSeqR (Write VarX) (CLetX (Num 2) CHole))))) [] 99%Z 99%Z)
           = Some([], [1%Z; 2%Z]).
Proof. auto.
Qed.

Definition context_equivalence_instr (p1 p2: list Instr): Prop :=
  forall c1 c2: list Instr, forall st: list Z, forall x y: Z,
    (evalInstr (c1 ++ p1 ++ c2) st x y) = (evalInstr (c1 ++ p2 ++ c2) st x y).

Definition context_equivalence_stmt (s1 s2: Stmt): Prop :=
  forall ctx: StmtContext, forall x y: Z,
    (evalStmt (link_to_context s1 ctx) x y) = (evalStmt (link_to_context s2 ctx) x y).

(* Part 1 of full abstraction *)
Theorem equivalence_reflection: forall p1 p2: list Instr, forall s1 s2: Stmt,
  (compileStmt s1 = p1) /\ (compileStmt s2 = p2) /\ (context_equivalence_instr p1 p2) -> (context_equivalence_stmt s1 s2).
Proof.
  intros. destruct H as [H1]. destruct H as [H2].
  unfold context_equivalence_instr in H.
  unfold context_equivalence_stmt. intros.
  revert y. revert x.

  assert (forall X: Type, forall a b c: list X, a = b -> a ++ c = b ++ c) as app_elim_r.
  induction c.
  intros. repeat rewrite app_nil_r. easy.
  intros. rewrite <- rev_involutive. rewrite distr_rev.
    rewrite <- (rev_involutive (a ++ a0 :: c)). rewrite distr_rev. rewrite H0. easy.

  assert (forall X: Type, forall a b c: list X, a = b -> c ++ a = c ++ b) as app_elim_l.
  intros. induction c.
  easy. repeat rewrite <- app_comm_cons. rewrite IHc. easy.

  induction ctx.
  + intros. unfold link_to_context.
    pose proof (compiler_correct s1 x y) as HC1. destruct HC1 as [st1]. rewrite H1 in H0.
    pose proof (compiler_correct s2 x y) as HC2. destruct HC2 as [st2]. rewrite H2 in H3.
    assert (forall p: list Instr, p = [] ++ p ++ []).
    intros. rewrite app_nil_r. rewrite app_nil_l. reflexivity.

    assert (evalInstr p1 [] x y = evalInstr p2 [] x y).
    rewrite (H4 p1). rewrite (H4 p2).
    apply (H [] []). rewrite H0 in H5. rewrite H3 in H5. inversion H5. easy.
  + simpl. easy.
  + simpl. intros. apply (IHctx (evalExpr e x y) y).
  + simpl. intros. apply (IHctx x (evalExpr e x y)).
  + simpl. intros. apply app_elim_r. apply IHctx.
  + simpl. intros. apply app_elim_l. apply IHctx.
Qed.

