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
Fixpoint evalInstr (prog: (list Instr)) (stack: list Z) (regX: Z) (regY: Z): option (list Z * list Z * (Z*Z)) :=
  match (prog, stack) with
  | (nil, result) => Some(result, [], (regX, regY))
  | (IPlus :: prog', n1 :: n2 :: rest) => (evalInstr prog' ((n2 + n1)%Z :: rest) regX regY)
  | (IMinus :: prog', n1 :: n2 :: rest) => (evalInstr prog' ((n2 - n1)%Z :: rest) regX regY)
  | (IWrite :: prog', n :: rest) => match (evalInstr prog' stack regX regY) with
                                    | Some(stack', evt', (regX', regY')) => Some(stack', n :: evt', (regX', regY'))
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

Example InstrE1: (evalInstr (IDup :: IPlus :: nil) (1%Z :: nil) 0 0) = Some([2%Z], [], (0%Z,0%Z)).
Proof.
  unfold evalInstr.
  auto.
Qed.

Example InstrE2: (evalInstr (IStoreX :: IWrite :: IPop :: nil) [] 3%Z 4%Z) = Some([], [3%Z], (3%Z, 4%Z)).
Proof.
  auto.
Qed.

Fixpoint compile_expr (e: Expr): list Instr :=
  match e with
  | VarX => [IStoreX]
  | VarY => [IStoreY]
  | Num n => [(IStoreImm n)]
  | Plus e1 e2 => 
    let e1Prog := (compile_expr e1) in
    let e2Prog := (compile_expr e2) in
    e1Prog ++ e2Prog ++ [IPlus]
  | Minus e1 e2 => 
    let e1Prog := (compile_expr e1) in
    let e2Prog := (compile_expr e2) in
    e1Prog ++ e2Prog ++ [IMinus]
  | IteZero ec el er =>
    let elProg := (compile_expr el) in
    let erProg := (compile_expr er) in
    let ecProg := (compile_expr ec) in
    erProg ++ elProg ++ ecProg ++ [ICondPick]
  end.

Fixpoint compile_stmt (s: Stmt): list Instr :=
  match s with
  | LetX e1 e2 =>
    let e1Prog := (compile_expr e1) in
    let e2Prog := (compile_stmt e2) in
    e1Prog ++ [IStoreX ; ISwap ; ILoadX] ++ e2Prog ++ [ILoadX]
  | LetY e1 e2 =>
    let e1Prog := (compile_expr e1) in
    let e2Prog := (compile_stmt e2) in
    e1Prog ++ [IStoreY ; ISwap ; ILoadY] ++ e2Prog ++ [ILoadY]
  | Write e => (compile_expr e) ++ [IWrite; IPop]
  | Seq e1 e2 =>
    let e1Prog := (compile_stmt e1) in
    let e2Prog := (compile_stmt e2) in
    e1Prog ++ e2Prog
  end.

Compute compile_stmt (LetX (Num 1) (Write VarX)).

Example CE1: evalInstr (compile_stmt (LetX (Num 1) (LetX (Num 2) (Write VarX)))) [] 0 0 = Some([], [2%Z], (0%Z, 0%Z)).
Proof. simpl. reflexivity.
Qed.

Lemma step_correct_expr: forall e: Expr, forall x0 y0: Z, forall progs: list Instr, forall st: list Z,
  (evalInstr ((compile_expr e) ++ progs) st x0 y0) = (evalInstr progs ((evalExpr e x0 y0) :: st) x0 y0).
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
    simpl (compile_expr (IteZero e1 e2 e3) ++ progs). repeat rewrite <- app_assoc. rewrite IHe3. rewrite IHe2. rewrite IHe1.
    simpl (evalInstr ([ICondPick] ++ progs) (evalExpr e1 x0 y0 :: evalExpr e2 x0 y0 :: evalExpr e3 x0 y0 :: st) x0 y0).
    destruct (evalExpr e1 x0 y0) eqn:condLeft.
    all: try simpl (evalInstr progs (evalExpr (IteZero e1 e2 e3) x0 y0 :: st) x0 y0).
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (evalExpr e2 x0 y0). all:repeat auto.
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (evalExpr e3 x0 y0). all:reflexivity.
    * simpl. destruct (evalExpr e1 x0 y0).
      + discriminate. + reflexivity. + reflexivity.
Qed.

Lemma step_correct_stmt: forall s: Stmt, forall x0 y0: Z, forall progs: list Instr, forall st: list Z,
  let e1 := (evalInstr ((compile_stmt s) ++ progs) st x0 y0) in
  let evt0 := (evalStmt s x0 y0) in
  let e2 := (evalInstr progs st x0 y0) in
  let l := match e1 with
           | None => None
           | Some(_, evt, _) => Some(evt)
           end in
  let r := match e2 with
           | None => None
           | Some(_, evt, _) => Some(evt0 ++ evt)
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
    assert (((compile_expr e ++ [IWrite; IPop]) ++ progs) = (compile_expr e ++ [IWrite; IPop] ++ progs)) as H.
    + rewrite app_assoc. reflexivity.
    + rewrite H. rewrite step_correct_expr. simpl. destruct (evalInstr progs st x0 y0) as [p|].
      * destruct p. destruct p. destruct p0. reflexivity.
      * reflexivity.
  - (*Seq*) simpl in IHs1. simpl in IHs2. intros x0 y0 progs st. simpl.
    rewrite <- app_assoc. rewrite IHs1. destruct_with_eqn (evalInstr (compile_stmt s2 ++ progs) st x0 y0).
    destruct_with_eqn (evalInstr progs st x0 y0).
    + specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. rewrite Heqo0 in IHs2.
      destruct_with_eqn p. destruct_with_eqn p0. destruct_with_eqn p1. destruct_with_eqn p3. rewrite <- app_assoc. inversion IHs2.
      reflexivity.
    + destruct p. exfalso. specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. rewrite Heqo0 in IHs2. destruct p in IHs2. inversion IHs2.
    + specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. destruct_with_eqn (evalInstr progs st x0 y0).
      ++ destruct_with_eqn p. exfalso. destruct p0 in IHs2. inversion IHs2.
      ++ reflexivity.
Qed.

Theorem compiler_correct: forall s: Stmt, forall x0 y0: Z, forall st: list Z,
  exists st': list Z, exists x0' y0': Z,
  evalInstr (compile_stmt s) st x0 y0 = Some(st', evalStmt s x0 y0, (x0', y0')).
Proof.
  assert (forall s: Stmt, forall x0 y0: Z, forall st: list Z,
      evalInstr (compile_stmt s ++ []) st x0 y0 = evalInstr (compile_stmt s) st x0 y0).
  - intros. rewrite app_nil_r. reflexivity.
  - intros. setoid_rewrite <- H. destruct_with_eqn (evalInstr (compile_stmt s ++ []) st x0 y0).
    + destruct p eqn:Hp.
      pose proof (step_correct_stmt s x0 y0 [] st) as HC. simpl in HC.
      rewrite Heqo in HC. simpl in HC.
      revert HC. destruct p0 eqn:HCp0. intros.
      rewrite app_nil_r in HC.
      inversion HC. rewrite <- H1. exists l. destruct p1. exists z. exists z0. reflexivity.
    + exfalso. destruct (evalInstr (compile_stmt s ++ []) st x0 y0) eqn:? in Heqo.
      ++ inversion Heqo.
      ++ pose proof (step_correct_stmt s x0 y0 [] st) as HC. rewrite Heqo0 in HC. simpl in HC. inversion HC.
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

Example LE1: (evalInstr (compile_stmt (link_to_context (Write VarX) (CLetX (Num 1) (CSeqR (Write VarX) (CLetX (Num 2) CHole))))) [] 99%Z 99%Z)
           = Some([], [1%Z; 2%Z], (99%Z, 99%Z)).
Proof. auto.
Qed.

Definition instr_trace_equiv (t1 t2: option (list Z * list Z * (Z * Z))): Prop :=
    (exists f0 f1 ans: list Z, exists r0 r1: Z*Z, 
      (t1 = Some(f0, ans, r0)) /\ (t2 = Some(f1, ans, r1)))
    \/ (t1 = None /\ t2 = None).

(* we currently only prepend c1. future work may allow appending c2.*)
Definition context_equivalence_instr' (p1 p2: list Instr): Prop :=
  forall c1: list Instr, forall st: list Z, forall x y: Z,
    instr_trace_equiv (evalInstr (c1 ++ p1) st x y) (evalInstr (c1 ++ p2) st x y).

Definition context_equivalence_stmt (s1 s2: Stmt): Prop :=
  forall ctx: StmtContext, forall x y: Z,
    (evalStmt (link_to_context s1 ctx) x y) = (evalStmt (link_to_context s2 ctx) x y).


(* Part 1 of full abstraction *)
Theorem equivalence_reflection: forall p1 p2: list Instr, forall s1 s2: Stmt,
  (compile_stmt s1 = p1) /\ (compile_stmt s2 = p2) /\ (context_equivalence_instr' p1 p2) -> (context_equivalence_stmt s1 s2).
Proof.
  intros. destruct H as [H1]. destruct H as [H2].
  unfold context_equivalence_instr' in H.
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
    pose proof (compiler_correct s1 x y []) as HC1. destruct HC1 as [st1 [x0 [y0 H0]]].
    rewrite H1 in H0.
    pose proof (compiler_correct s2 x y []) as HC2. destruct HC2 as [st2 [x0' [y0' H3]]]. rewrite H2 in H3.

    assert (instr_trace_equiv (evalInstr p1 [] x y) (evalInstr p2 [] x y)).
    rewrite <- (app_nil_l p1). rewrite <- (app_nil_l p2).
    apply (H [] []). rewrite H0 in H4. rewrite H3 in H4. inversion H4.
    destruct H5 as [f0 [f1 [ans [r0 [r1 [H5]]]]]]. injection H5. injection H6.
    intros. rewrite H8. easy. exfalso. destruct H5. easy.
  + simpl. easy.
  + simpl. intros. apply (IHctx (evalExpr e x y) y).
  + simpl. intros. apply (IHctx x (evalExpr e x y)).
  + simpl. intros. apply app_elim_r. apply IHctx.
  + simpl. intros. apply app_elim_l. apply IHctx.
Qed.

Lemma prefix_removal: forall p1 p2 c1: list Instr,
  (forall st: list Z, forall x y: Z, instr_trace_equiv (evalInstr p1 st x y) (evalInstr p2 st x y)) -> 
  (forall st': list Z, forall x' y': Z, instr_trace_equiv (evalInstr (c1 ++ p1) st' x' y') (evalInstr (c1 ++ p2) st' x' y')).
Proof.
  intros p1 p2 c1. intros IH0.
  induction c1.
  + repeat rewrite app_nil_l. easy.
  + repeat rewrite <- app_comm_cons. destruct a. all: try (repeat simpl; intros; rewrite IHc1; easy).
    - simpl. destruct st'. intros. * unfold instr_trace_equiv. right. easy.
      * intros. destruct st'. unfold instr_trace_equiv. right. easy. apply IHc1.
    - simpl. destruct st'.
      * intros. unfold instr_trace_equiv. right. easy.
      * intros. destruct st'. unfold instr_trace_equiv. right. easy.
        apply IHc1.
    - intros. simpl. destruct st'. unfold instr_trace_equiv. right. easy.
      destruct st'. unfold instr_trace_equiv. right. easy.
      destruct st'. unfold instr_trace_equiv. right. easy.
      destruct z. apply IHc1. apply IHc1. apply IHc1.
      all: apply IHc1. 
    - intros. Opaque instr_trace_equiv. simpl.
      Transparent instr_trace_equiv. destruct st'.
      unfold instr_trace_equiv. right. easy.
      
      assert (instr_trace_equiv (evalInstr (c1 ++ p1) (z::st') x' y')
                                (evalInstr (c1 ++ p2) (z::st') x' y')) as IHc1'.
      apply IHc1.

      destruct (evalInstr (c1 ++ p1) (z :: st') x' y') eqn:HL.
      destruct (evalInstr (c1 ++ p2) (z :: st') x' y') eqn:HR.
      destruct p eqn:?. destruct p0 eqn:?.
      destruct p3 eqn:?. destruct p4 eqn:?. destruct p5 eqn:?. destruct p6 eqn:?.
      unfold instr_trace_equiv in IHc1'.
        destruct IHc1' as [[f0 [f1 [ans [r0 [r1 [IHc2 IHc3]]]]]] | IHc1''].
        injection IHc2. injection IHc3. intros.
        rewrite <- H3 in H0. rewrite H0. unfold instr_trace_equiv.
        left. exists l. exists l1. exists(z::l0). exists (z0, z1). exists (z2, z3). easy.
        exfalso. easy.
      exfalso. unfold instr_trace_equiv in IHc1'.
        destruct IHc1' as [[f0 [f1 [ans [r0 [r1 [IHc2 IHc3]]]]]] | IHc1''].
        easy. destruct IHc1''. easy.
      destruct IHc1' as [[f0 [f1 [ans [r0 [r1 [IHc2 IHc3]]]]]] | IHc1''].
      exfalso. easy. destruct IHc1''. rewrite H0. unfold instr_trace_equiv. right. easy.
    - intros. simpl. destruct st'. unfold instr_trace_equiv. right. easy. apply IHc1.
    - intros. simpl. destruct st'. unfold instr_trace_equiv. right. easy. apply IHc1.
    - intros. simpl. destruct st'. unfold instr_trace_equiv. right. easy. apply IHc1.
    - intros. simpl. apply IHc1.
    - intros. simpl. apply IHc1.
    - intros. simpl. apply IHc1.
    - intros. simpl. destruct st'. unfold instr_trace_equiv. right. easy. apply IHc1.
    - intros. simpl. destruct st'. unfold instr_trace_equiv. right. easy.
      destruct st' eqn:?. unfold instr_trace_equiv. right. easy. apply IHc1.
Qed.

(* Part 2 of full abstraction *)
Theorem equivalence_preservation': forall p1 p2: list Instr, forall s1 s2: Stmt,
  (compile_stmt s1 = p1) /\ (compile_stmt s2 = p2) /\ (context_equivalence_stmt s1 s2) -> (context_equivalence_instr' p1 p2).
Proof.
  intros. destruct H as [H1 [H H2]].
  unfold context_equivalence_stmt in H.
  unfold context_equivalence_instr'. intros c1 c2 st.
  apply prefix_removal. intros. unfold context_equivalence_stmt in H2.
  pose proof (H2 CHole x y) as H3. unfold link_to_context in H3.
  pose proof (compiler_correct s1 x y st0) as Hs1. pose proof (compiler_correct s2 x y st0) as Hs2.
  rewrite H1 in Hs1. rewrite H in Hs2. rewrite H3 in Hs1.
  destruct Hs1 as [st' [x0' [y0' Hs1]]].
  destruct Hs2 as [st'' [x0'' [y0'' Hs2]]].
  rewrite Hs1. rewrite Hs2. unfold instr_trace_equiv. left.
  exists st'. exists st''. exists (evalStmt s2 x y). exists (x0', y0'). exists (x0'', y0'').
  easy. 
Qed.



