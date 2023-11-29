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

Fixpoint eval_expr (e: Expr) (varX: Z) (varY: Z): Z :=
  match e with
  | Num n => n
  | Plus e1 e2 => (eval_expr e1 varX varY) + (eval_expr e2 varX varY)
  | Minus e1 e2 => (eval_expr e1 varX varY) - (eval_expr e2 varX varY)
  | VarX => varX
  | VarY => varY
  | IteZero ec el er =>
       let cond := (eval_expr ec varX varY) in
       let l := (eval_expr el varX varY) in
       let r := (eval_expr er varX varY) in
       match cond with
       | Z0 => l
       | _ => r
       end
  end.

Fixpoint eval_stmt (s: Stmt) (varX: Z) (varY: Z) : list Z :=
  match s with
  | LetX e1 e2 => let varX' := (eval_expr e1 varX varY) in 
                    (eval_stmt e2 varX' varY)
  | LetY e1 e2 => let varY' := (eval_expr e1 varX varY) in
                    (eval_stmt e2 varX varY')
  | Write e => [(eval_expr e varX varY)]
  | Seq p q => (eval_stmt p varX varY) ++ (eval_stmt q varX varY)
  end.

Example E1: (Z.to_nat (eval_expr (Plus (Num 3) VarX) 2 3)) = 5.
Proof.
  auto.
Qed.

Example E2: (Z.to_nat (eval_expr (IteZero (Minus (Num 1) (Num 1)) VarX VarY) 3 5)) = 3.
Proof. unfold eval_expr. auto.
Qed.

Example E3: ((eval_stmt (Seq (LetX (Num 1) (LetY (Num 2) (Write VarX))) (Write VarY)) 3 4) = [1%Z; 4%Z]).
Proof. unfold eval_stmt. simpl. reflexivity.
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
Fixpoint eval_instr (prog: (list Instr)) (stack: list Z) (regX: Z) (regY: Z): option (list Z * list Z * (Z*Z)) :=
  match (prog, stack) with
  | (nil, result) => Some(result, [], (regX, regY))
  | (IPlus :: prog', n1 :: n2 :: rest) => (eval_instr prog' ((n2 + n1)%Z :: rest) regX regY)
  | (IMinus :: prog', n1 :: n2 :: rest) => (eval_instr prog' ((n2 - n1)%Z :: rest) regX regY)
  | (IWrite :: prog', n :: rest) => match (eval_instr prog' stack regX regY) with
                                    | Some(stack', evt', (regX', regY')) => Some(stack', n :: evt', (regX', regY'))
                                    | None => None
                                    end
  | (ICondPick :: prog', cond :: l :: r :: rest) =>
    match cond with
    | Z0 => (eval_instr prog' (l :: rest) regX regY)
    | _ => (eval_instr prog' (r :: rest) regX regY)
    end
  | (ILoadX :: prog', n :: rest) => (eval_instr prog' rest n regY)
  | (ILoadY :: prog', n :: rest) => (eval_instr prog' rest regX n)
  | (IStoreX :: prog', _) => (eval_instr prog' (regX :: stack) regX regY)
  | (IStoreY :: prog', _) => (eval_instr prog' (regY :: stack) regX regY)
  | ((IStoreImm imm) :: prog', _) => (eval_instr prog' (imm :: stack) regX regY)
  | (IPop :: prog', n :: rest) => (eval_instr prog' rest regX regY)
  | (IDup :: prog', n :: rest) => (eval_instr prog' (n :: n :: rest) regX regY)
  | (ISwap :: prog', n1 :: n2 :: rest) => (eval_instr prog' (n2 :: n1 :: rest) regX regY)
  | (_, _) => None
  end.

Example InstrE1: (eval_instr (IDup :: IPlus :: nil) (1%Z :: nil) 0 0) = Some([2%Z], [], (0%Z,0%Z)).
Proof.
  unfold eval_instr.
  auto.
Qed.

Example InstrE2: (eval_instr (IStoreX :: IWrite :: IPop :: nil) [] 3%Z 4%Z) = Some([], [3%Z], (3%Z, 4%Z)).
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

Example CE1: eval_instr (compile_stmt (LetX (Num 1) (LetX (Num 2) (Write VarX)))) [] 0 0 = Some([], [2%Z], (0%Z, 0%Z)).
Proof. simpl. reflexivity.
Qed.

Lemma step_correct_expr: forall e: Expr, forall x0 y0: Z, forall progs: list Instr, forall st: list Z,
  (eval_instr ((compile_expr e) ++ progs) st x0 y0) = (eval_instr progs ((eval_expr e x0 y0) :: st) x0 y0).
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
    simpl (eval_instr ([ICondPick] ++ progs) (eval_expr e1 x0 y0 :: eval_expr e2 x0 y0 :: eval_expr e3 x0 y0 :: st) x0 y0).
    destruct (eval_expr e1 x0 y0) eqn:condLeft.
    all: try simpl (eval_instr progs (eval_expr (IteZero e1 e2 e3) x0 y0 :: st) x0 y0).
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (eval_expr e2 x0 y0). all:repeat auto.
    * rewrite -> condLeft. try rewrite Z.mul_0_l. simpl. destruct (eval_expr e3 x0 y0). all:reflexivity.
    * simpl. destruct (eval_expr e1 x0 y0).
      + discriminate. + reflexivity. + reflexivity.
Qed.

Lemma step_correct_stmt: forall s: Stmt, forall x0 y0: Z, forall progs: list Instr, forall st: list Z,
  let e1 := (eval_instr ((compile_stmt s) ++ progs) st x0 y0) in
  let evt0 := (eval_stmt s x0 y0) in
  let e2 := (eval_instr progs st x0 y0) in
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
    + rewrite H. rewrite step_correct_expr. simpl. destruct (eval_instr progs st x0 y0) as [p|].
      * destruct p. destruct p. destruct p0. reflexivity.
      * reflexivity.
  - (*Seq*) simpl in IHs1. simpl in IHs2. intros x0 y0 progs st. simpl.
    rewrite <- app_assoc. rewrite IHs1. destruct_with_eqn (eval_instr (compile_stmt s2 ++ progs) st x0 y0).
    destruct_with_eqn (eval_instr progs st x0 y0).
    + specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. rewrite Heqo0 in IHs2.
      destruct_with_eqn p. destruct_with_eqn p0. destruct_with_eqn p1. destruct_with_eqn p3. rewrite <- app_assoc. inversion IHs2.
      reflexivity.
    + destruct p. exfalso. specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. rewrite Heqo0 in IHs2. destruct p in IHs2. inversion IHs2.
    + specialize (IHs2 x0 y0 progs st). rewrite Heqo in IHs2. destruct_with_eqn (eval_instr progs st x0 y0).
      ++ destruct_with_eqn p. exfalso. destruct p0 in IHs2. inversion IHs2.
      ++ reflexivity.
Qed.

Theorem compiler_correct: forall s: Stmt, forall x0 y0: Z, forall st: list Z,
  exists st': list Z, exists x0' y0': Z,
  eval_instr (compile_stmt s) st x0 y0 = Some(st', eval_stmt s x0 y0, (x0', y0')).
Proof.
  assert (forall s: Stmt, forall x0 y0: Z, forall st: list Z,
      eval_instr (compile_stmt s ++ []) st x0 y0 = eval_instr (compile_stmt s) st x0 y0).
  - intros. rewrite app_nil_r. reflexivity.
  - intros. setoid_rewrite <- H. destruct_with_eqn (eval_instr (compile_stmt s ++ []) st x0 y0).
    + destruct p eqn:Hp.
      pose proof (step_correct_stmt s x0 y0 [] st) as HC. simpl in HC.
      rewrite Heqo in HC. simpl in HC.
      revert HC. destruct p0 eqn:HCp0. intros.
      rewrite app_nil_r in HC.
      inversion HC. rewrite <- H1. exists l. destruct p1. exists z. exists z0. reflexivity.
    + exfalso. destruct (eval_instr (compile_stmt s ++ []) st x0 y0) eqn:? in Heqo.
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

Example LE1: (eval_instr (compile_stmt (link_to_context (Write VarX) (CLetX (Num 1) (CSeqR (Write VarX) (CLetX (Num 2) CHole))))) [] 99%Z 99%Z)
           = Some([], [1%Z; 2%Z], (99%Z, 99%Z)).
Proof. auto.
Qed.

Definition instr_trace_equiv (t1 t2: option (list Z * list Z * (Z * Z))): Prop :=
    (exists f0 f1 ans: list Z, exists r0 r1: Z*Z, 
      (t1 = Some(f0, ans, r0)) /\ (t2 = Some(f1, ans, r1)))
    \/ (t1 = None /\ t2 = None).

Definition context_equivalence_instr (p1 p2: list Instr): Prop :=
  forall c1 c2: list Instr, forall st: list Z, forall x y: Z,
    instr_trace_equiv (eval_instr (c1 ++ p1 ++ c2) st x y) (eval_instr (c1 ++ p2 ++ c2) st x y).

Definition context_equivalence_instr' (p1 p2: list Instr): Prop :=
  forall c1: list Instr, forall st: list Z, forall x y: Z,
    instr_trace_equiv (eval_instr (c1 ++ p1) st x y) (eval_instr (c1 ++ p2) st x y).

Definition context_equivalence_stmt (s1 s2: Stmt): Prop :=
  forall ctx: StmtContext, forall x y: Z,
    (eval_stmt (link_to_context s1 ctx) x y) = (eval_stmt (link_to_context s2 ctx) x y).


(* Part 1 of full abstraction *)
Theorem equivalence_reflection: forall p1 p2: list Instr, forall s1 s2: Stmt,
  (compile_stmt s1 = p1) /\ (compile_stmt s2 = p2) /\ (context_equivalence_instr p1 p2) -> (context_equivalence_stmt s1 s2).
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
    pose proof (compiler_correct s1 x y []) as HC1. destruct HC1 as [st1 [x0 [y0 H0]]].
    rewrite H1 in H0.
    pose proof (compiler_correct s2 x y []) as HC2. destruct HC2 as [st2 [x0' [y0' H3]]]. rewrite H2 in H3.

    assert (instr_trace_equiv (eval_instr p1 [] x y) (eval_instr p2 [] x y)).
    rewrite <- (app_nil_l p1). rewrite <- (app_nil_l p2).
    rewrite <- (app_nil_r p1). rewrite <- (app_nil_r p2).
    apply (H [] []). rewrite H0 in H4. rewrite H3 in H4. inversion H4.
    destruct H5 as [f0 [f1 [ans [r0 [r1 [H5]]]]]]. injection H5. injection H6.
    intros. rewrite H8. easy. exfalso. destruct H5. easy.
  + simpl. easy.
  + simpl. intros. apply (IHctx (eval_expr e x y) y).
  + simpl. intros. apply (IHctx x (eval_expr e x y)).
  + simpl. intros. apply app_elim_r. apply IHctx.
  + simpl. intros. apply app_elim_l. apply IHctx.
Qed.


(* Part 1 of full abstraction *)
Theorem equivalence_reflection': forall p1 p2: list Instr, forall s1 s2: Stmt,
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

    assert (instr_trace_equiv (eval_instr p1 [] x y) (eval_instr p2 [] x y)).
    rewrite <- (app_nil_l p1). rewrite <- (app_nil_l p2).
    apply (H [] []). rewrite H0 in H4. rewrite H3 in H4. inversion H4.
    destruct H5 as [f0 [f1 [ans [r0 [r1 [H5]]]]]]. injection H5. injection H6.
    intros. rewrite H8. easy. exfalso. destruct H5. easy.
  + simpl. easy.
  + simpl. intros. apply (IHctx (eval_expr e x y) y).
  + simpl. intros. apply (IHctx x (eval_expr e x y)).
  + simpl. intros. apply app_elim_r. apply IHctx.
  + simpl. intros. apply app_elim_l. apply IHctx.
Qed.

Lemma prefix_removal: forall p1 p2 c1: list Instr,
  (forall st: list Z, forall x y: Z, instr_trace_equiv (eval_instr p1 st x y) (eval_instr p2 st x y)) -> 
  (forall st': list Z, forall x' y': Z, instr_trace_equiv (eval_instr (c1 ++ p1) st' x' y') (eval_instr (c1 ++ p2) st' x' y')).
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
      
      assert (instr_trace_equiv (eval_instr (c1 ++ p1) (z::st') x' y')
                                (eval_instr (c1 ++ p2) (z::st') x' y')) as IHc1'.
      apply IHc1.

      destruct (eval_instr (c1 ++ p1) (z :: st') x' y') eqn:HL.
      destruct (eval_instr (c1 ++ p2) (z :: st') x' y') eqn:HR.
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

Lemma small_step_instr_none: forall p p': list Instr,
                        forall x0 y0 x1 y1: Z, forall st0 st1 w1: list Z,
  ((eval_instr p st0 x0 y0 = Some(st1, w1, (x1, y1))) /\ (eval_instr p' st1 x1 y1 = None))
    -> (eval_instr (p ++ p') st0 x0 y0 = None).
Proof.
  intros p p'. induction p. induction p'.
  - rewrite app_nil_l. simpl. intros. destruct H. injection H. intros. rewrite H1. rewrite H2. rewrite H4. rewrite H0.
    easy.
  - rewrite app_nil_l. intros. destruct H. simpl in H. inversion H. rewrite H0. easy.
  - intros. destruct H. destruct a.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. simpl in H. easy.
             apply (IHp x0 y0 x1 y1 ((z0+z)%Z :: st0) st1 w1). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. simpl in H. easy.
             apply (IHp x0 y0 x1 y1 ((z0-z)%Z :: st0) st1 w1). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. easy. destruct st0. exfalso. easy.
      destruct z. * apply (IHp x0 y0 x1 y1 (z0 :: st0) st1 w1). easy.
                  * apply (IHp x0 y0 x1 y1 (z1 :: st0) st1 w1). easy.
                  * apply (IHp x0 y0 x1 y1 (z1 :: st0) st1 w1). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy.
             simpl in H. destruct (eval_instr p (z :: st0) x0 y0) eqn:HP0. destruct p0 eqn:HP1.
             destruct p1 eqn:HP2. destruct p2 eqn:HP3. inversion H.
             * destruct (eval_instr (p ++ p') (z :: st0) x0 y0) eqn:HP4.
               ++ rewrite H2 in HP0. rewrite H4 in HP0. rewrite H5 in HP0. assert (HP0':=conj HP0 H0).
                  apply (IHp x0 y0 x1 y1 (z::st0) st1 l0) in HP0'. rewrite HP4 in HP0'.
                  destruct p3 eqn:H6. destruct p4 eqn:H7. destruct p5 eqn:H8. inversion HP0'.
               ++ easy.
             * exfalso. easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp z y0 x1 y1 st0 st1 w1). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp x0 z x1 y1 st0 st1 w1). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp x0 y0 x1 y1 st0 st1 w1). easy.
    + simpl. destruct st0. apply (IHp x0 y0 x1 y1 [x0] st1 w1). easy.
                           apply (IHp x0 y0 x1 y1 (x0::z::st0) st1 w1). easy.
    + simpl. destruct st0. apply (IHp x0 y0 x1 y1 [y0] st1 w1). easy.
                           apply (IHp x0 y0 x1 y1 (y0::z::st0) st1 w1). easy.
    + simpl. destruct st0. apply (IHp x0 y0 x1 y1 [z] st1 w1). easy.
                           apply (IHp x0 y0 x1 y1 (z::z0::st0) st1 w1). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp x0 y0 x1 y1 (z::z::st0) st1 w1). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. simpl in H. easy.
             apply (IHp x0 y0 x1 y1 (z0::z::st0) st1 w1). easy.
Qed.

Lemma small_step_instr_some: forall p p': list Instr,
                        forall x0 y0 x1 y1 x2 y2: Z, forall st0 st1 st2 w1 w2: list Z,
  ((eval_instr p st0 x0 y0 = Some(st1, w1, (x1, y1))) /\ (eval_instr p' st1 x1 y1 = Some(st2, w2, (x2, y2))))
    -> (eval_instr (p ++ p') st0 x0 y0 = Some(st2, w1 ++ w2, (x2, y2))).
Proof.
  intros p p'. induction p. induction p'.
  - rewrite app_nil_l. simpl. intros. destruct H. injection H. intros. rewrite H1. rewrite H2. rewrite H4. rewrite H0.
    rewrite <- H3. rewrite app_nil_l. easy.
  - rewrite app_nil_l. intros. destruct H. simpl in H. inversion H. rewrite H0.
    rewrite app_nil_l. easy.
  - intros. destruct H. destruct a.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. simpl in H. easy.
             apply (IHp x0 y0 x1 y1 x2 y2 ((z0+z)%Z :: st0) st1 st2).
             * easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. simpl in H. easy.
             apply (IHp x0 y0 x1 y1 x2 y2 ((z0-z)%Z :: st0) st1 st2).
             * easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. easy. destruct st0. exfalso. easy.
      destruct z. * apply (IHp x0 y0 x1 y1 x2 y2 (z0 :: st0) st1 st2). easy.
                  * apply (IHp x0 y0 x1 y1 x2 y2 (z1 :: st0) st1 st2). easy.
                  * apply (IHp x0 y0 x1 y1 x2 y2 (z1 :: st0) st1 st2). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy.
             simpl in H. destruct (eval_instr p (z :: st0) x0 y0) eqn:HP0. destruct p0 eqn:HP1.
             destruct p1 eqn:HP2. destruct p2 eqn:HP3. inversion H.
             * destruct (eval_instr (p ++ p') (z :: st0) x0 y0) eqn:HP4.
               ++ rewrite H2 in HP0. rewrite H4 in HP0. rewrite H5 in HP0. assert (HP0':=conj HP0 H0).
                  apply (IHp x0 y0 x1 y1 x2 y2 (z::st0) st1 st2 l0 w2) in HP0'. rewrite HP4 in HP0'.
                  destruct p3 eqn:H6. destruct p4 eqn:H7. destruct p5 eqn:H8. inversion HP0'.
                  rewrite app_comm_cons. easy.
               ++ exfalso. rewrite H2 in HP0. rewrite H4 in HP0. rewrite H5 in HP0. assert (HP0':=conj HP0 H0).
                  apply (IHp x0 y0 x1 y1 x2 y2 (z::st0) st1 st2 l0 w2) in HP0'. rewrite HP4 in HP0'. easy.
             * exfalso. easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp z y0 x1 y1 x2 y2 st0 st1 st2). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp x0 z x1 y1 x2 y2 st0 st1 st2). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp x0 y0 x1 y1 x2 y2 st0 st1 st2). easy.
    + simpl. destruct st0. apply (IHp x0 y0 x1 y1 x2 y2 [x0] st1 st2). easy.
                           apply (IHp x0 y0 x1 y1 x2 y2 (x0::z::st0) st1 st2). easy.
    + simpl. destruct st0. apply (IHp x0 y0 x1 y1 x2 y2 [y0] st1 st2). easy.
                           apply (IHp x0 y0 x1 y1 x2 y2 (y0::z::st0) st1 st2). easy.
    + simpl. destruct st0. apply (IHp x0 y0 x1 y1 x2 y2 [z] st1 st2). easy.
                           apply (IHp x0 y0 x1 y1 x2 y2 (z::z0::st0) st1 st2). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. apply (IHp x0 y0 x1 y1 x2 y2 (z::z::st0) st1 st2). easy.
    + simpl. destruct st0. exfalso. simpl in H. easy. destruct st0. exfalso. simpl in H. easy.
             apply (IHp x0 y0 x1 y1 x2 y2 (z0::z::st0) st1 st2). easy.
Qed.

Axiom step_stuck_safety: forall p p': list Instr, forall x0 y0: Z, forall st0: list Z,
  (eval_instr p st0 x0 y0 = None) -> (eval_instr (p ++ p') st0 x0 y0 = None).

Lemma suffix_removal: forall p1 p2 c2: list Instr,
  (forall st: list Z, forall x y: Z, (eval_instr p1 st x y) = (eval_instr p2 st x y)) -> 
  (forall st': list Z, forall x' y': Z, instr_trace_equiv (eval_instr (p1 ++ c2) st' x' y') (eval_instr (p2 ++ c2) st' x' y')).
Proof.
  intros.
  destruct (eval_instr p1 st' x' y') eqn:HP1. destruct p as [[st_p1_end w_p1_end] [x_p1_end y_p1_end]] eqn:?.
  destruct (eval_instr c2 st_p1_end x_p1_end y_p1_end) eqn:Hc.
  destruct p0 as [[st_c_end1 w_c_end1] [x_c_end1 y_c_end1]] eqn:?.
  pose proof (small_step_instr_some p1 c2 x' y' x_p1_end y_p1_end x_c_end1 y_c_end1 st' st_p1_end st_c_end1 w_p1_end w_c_end1).
  assert (HPc1 := conj HP1 Hc). apply H0 in HPc1. clear H0.
  rewrite HPc1. destruct (eval_instr p2 st' x' y') eqn:HP2. destruct p3 as [[st_p2_end w_p2_end] [x_p2_end y_p2_end]] eqn:?.
  destruct (eval_instr c2 st_p2_end x_p2_end y_p2_end) eqn:Hc'.
  { destruct p4 as [[st_c_end2 w_c_end2] [x_c_end2 y_c_end2]] eqn:?.
    assert (HPc2 := conj HP2 Hc').
    pose proof (small_step_instr_some p2 c2 x' y' x_p2_end y_p2_end x_c_end2 y_c_end2 st' st_p2_end st_c_end2 w_p2_end w_c_end2) as H0'.
    apply H0' in HPc2. clear H0'. rewrite HPc2. 
    specialize (H st' x' y').
    rewrite HP1 in H. rewrite HP2 in H. inversion H.
    unfold instr_trace_equiv. left. exists st_c_end1. exists st_c_end2. exists (w_p2_end ++ w_c_end1).
    exists (x_c_end1, y_c_end1). exists (x_c_end2, y_c_end2). split. easy. rewrite H1 in Hc. rewrite H3 in Hc. rewrite H4 in Hc.
    rewrite Hc' in Hc. inversion Hc. easy.
  }
  - exfalso. specialize (H st' x' y'). rewrite <- H in HP2. rewrite HP1 in HP2. inversion HP2.
    rewrite <- H1 in Hc'. rewrite <- H3 in Hc'. rewrite <- H4 in Hc'. rewrite Hc in Hc'. easy.
  - exfalso. specialize (H st' x' y'). rewrite <- H in HP2. rewrite HP1 in HP2. inversion HP2.
  - specialize (H st' x' y'). destruct (eval_instr p2 st' x' y') eqn:HP2. destruct p0 as [[st_p2_end w_p2_end] [x_p2_end y_p2_end]] eqn:?.
     * rewrite HP1 in H. inversion H.
       pose proof (small_step_instr_none p1 c2 x' y' x_p1_end y_p1_end st' st_p1_end w_p1_end).
       assert (HPc1 := conj HP1 Hc). apply H0 in HPc1. rewrite HPc1.
       pose proof (small_step_instr_none p2 c2 x' y' x_p2_end y_p2_end st' st_p2_end w_p2_end) as H0'.
       rewrite H1 in Hc. rewrite H3 in Hc. rewrite H4 in Hc. assert (HPc2 := conj HP2 Hc). 
       apply H0' in HPc2. rewrite HPc2. unfold instr_trace_equiv. right. easy.
     * rewrite HP1 in H. inversion H.
  - specialize (H st' x' y'). destruct (eval_instr p2 st' x' y') eqn:HP2. destruct p as [[st_p2_end w_p2_end] [x_p2_end y_p2_end]] eqn:?.
     * rewrite HP1 in H. inversion H.
     * pose proof (step_stuck_safety p1 c2 x' y' st'). apply H0 in H. rewrite H.
       pose proof (step_stuck_safety p2 c2 x' y' st'). apply H1 in HP2. rewrite HP2. unfold instr_trace_equiv. right. easy.
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
  (*apply suffix_removal. intros.
  pose proof (H2 CHole x0 y0) as H3'. unfold link_to_context in H3'.
  pose proof (compiler_correct s1 x0 y0 st1) as Hs1'. pose proof (compiler_correct s2 x0 y0 st1) as Hs2'.
  rewrite H1 in Hs1'. rewrite H in Hs2'. rewrite H3' in Hs1'.
  destruct Hs1' as [st_' [x0_' [y0_' Hs1']]].
  destruct Hs2' as [st_'' [x0_'' [y0_'' Hs2']]].*)
  unfold instr_trace_equiv. left. exists st'. exists st''. exists (eval_stmt s2 x y). exists (x0', y0'). exists (x0'', y0'').
  split. easy. easy.
Qed.

Theorem full_abstraction': forall p1 p2: list Instr, forall s1 s2: Stmt,
  ((compile_stmt s1 = p1) /\ (compile_stmt s2 = p2)) -> ((context_equivalence_stmt s1 s2) <-> (context_equivalence_instr' p1 p2)).
Proof.
  intros. split. 
  - intros. apply (equivalence_preservation' p1 p2 s1 s2). split. easy. easy.
  - intros. apply (equivalence_reflection' p1 p2 s1 s2). split. easy. easy.
Qed.


