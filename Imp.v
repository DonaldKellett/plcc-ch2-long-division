(* Adapted from Simple Imperative Programs (Imp) of Logical
   Foundations:
   https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html *)

From Coq Require Import ZArith Strings.String.
From LongDivision Require Import Maps.

Open Scope Z.

(* Program state *)

Definition state := total_map Z.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (t_update empty_st x v)
  (at level 100).

(* Arithmetic expressions *)

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Coercion AId : string >-> aexp.
Coercion ANum : Z >-> aexp.
Bind Scope imp_scope with aexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y)
  (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y)
  (at level 50, left associativity) : imp_scope.
Notation "x / y" := (ADiv x y)
  (at level 40, left associativity) : imp_scope.

Fixpoint aeval (st : state) (a : aexp) : Z :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => aeval st a1 + aeval st a2
  | AMinus a1 a2 => aeval st a1 - aeval st a2
  | ADiv a1 a2 => aeval st a1 / aeval st a2
  end.

(* Boolean expressions *)

Inductive bexp : Type :=
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp).

Bind Scope imp_scope with bexp.
Notation "x <= y" := (BLe x y)
  (at level 70, no associativity) : imp_scope.
Notation "x > y" := (BGt x y)
  (at level 70, no associativity) : imp_scope.

Definition beval (st : state) (b : bexp) : bool :=
  match b with
  | BLe a1 a2 => aeval st a1 <=? aeval st a2
  | BGt a1 a2 => aeval st a1 >? aeval st a2
  end.

(* Commands *)

Inductive com : Type :=
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CWhile (b : bexp) (c' : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CSkip.

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Ass : forall x a n st,
      aeval st a = n ->
      st =[ x ::= a ]=> (x !-> n; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_WhileTrue : forall b c' st st' st'',
      beval st b = true ->
      st =[ c' ]=> st' ->
      st' =[ WHILE b DO c' END ]=> st'' ->
      st =[ WHILE b DO c' END ]=> st''
  | E_WhileFalse : forall b c' st,
      beval st b = false ->
      st =[ WHILE b DO c' END ]=> st
  | E_IfTrue : forall b c1 c2 st st',
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall b c1 c2 st st',
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_Skip : forall st,
      st =[ SKIP ]=> st

  where "st =[ c ]=> st'" := (ceval c st st').

Close Scope Z.