Require Import ZArith.
From stdpp Require Import prelude.
Require Import Coq.Lists.List.
Add LoadPath "/nix/store/4w62wnc2x4a7pmk8qrhy0jwsaw8p1zsr-coq8.17-stdpp-1.9.0/lib/coq/8.17/user-contrib/stdpp".

Inductive Expr :=
    Num: Z -> Expr
  | Plus: Expr -> Expr -> Expr
  | Minus: Expr -> Expr -> Expr
  | Arg: Expr
  | Call: nat -> Z -> Expr. (* fn names are nats*)



Fixpoint evalExpr (e: Expr) (arg: Z) (globalFun: nat -> Expr): Z :=
  match e with
  | Num n => n
  | Plus e1 e2 => (evalExpr e1 arg globalFun) + (evalExpr e2 arg globalFun)
  | Minus e1 e2 => (evalExpr e1 arg globalFun) - (evalExpr e2 arg globalFun)
  | Arg => arg
  | Call fn x => evalExpr (globalFun fn) x ()
  end.

Lemma evalExprEx : (evalExpr (Plus (Num 3) Arg) 2) = Z.of_nat 5.
Proof.
  auto.
