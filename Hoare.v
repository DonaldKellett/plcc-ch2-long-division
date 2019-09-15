(* Adapted with minimal modifications from Hoare Logic, Part I
   (Hoare) of Programming Language Foundations:
   https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html *)

From Coq Require Import Strings.String Program.Equality.
From LongDivision Require Import Maps Imp.

(* Core definitions *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P '->>' Q" := (assert_implies P Q) (at level 80) :
  hoare_spec_scope.

Open Scope hoare_spec_scope.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
  : Prop := forall st st', P st -> st =[ c ]=> st' -> Q st'.

Notation "'{{' P '}}' c '{{' Q '}}'" := (hoare_triple P c Q)
  (at level 90, c at next level) : hoare_spec_scope.

(* Proof rules *)

Ltac inv H := inversion H; subst; clear H.

Theorem hoare_floyd : forall P x a,
  {{ P }} x ::= a {{ fun st => exists st',
  (forall y, x <> y -> st y = st' y) /\
  st x = aeval st' a /\
  P st' }}.
Proof with auto.
  unfold hoare_triple; intros; inv H0; unfold t_update.
  exists st; repeat split...
  - intros; destruct (string_dec x y)...
    contradiction H0.
  - destruct (string_dec x x)...
    now contradiction n.
Qed.

Theorem hoare_consequence : forall P P' Q Q' c,
  {{ P' }} c {{ Q' }} ->
  P ->> P' ->
  Q' ->> Q ->
  {{ P }} c {{ Q }}.
Proof. unfold hoare_triple; eauto. Qed.

Theorem hoare_skip : forall P, {{ P }} SKIP {{ P }}.
Proof. unfold hoare_triple; intros; now inv H0. Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{ P }} c1 {{ Q }} ->
  {{ Q }} c2 {{ R }} ->
  {{ P }} c1 ;; c2 {{ R }}.
Proof. unfold hoare_triple; intros; inv H2; eauto. Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{ fun st => P st /\ beval st b = true }} c1 {{ Q }} ->
  {{ fun st => P st /\ beval st b = false }} c2 {{ Q }} ->
  {{ P }} TEST b THEN c1 ELSE c2 FI {{ Q }}.
Proof. unfold hoare_triple; intros; inv H2; eauto. Qed.

Theorem hoare_while : forall P b c',
  {{ fun st => P st /\ beval st b = true }} c' {{ P }} ->
  {{ P }} WHILE b DO c' END {{ fun st => P st /\
  beval st b = false }}.
Proof.
  unfold hoare_triple; intros; dependent induction H1; eauto.
Qed.

Close Scope hoare_spec_scope.