(* Formal proof of correctness of long division algorithm as
   appearing in PLCC Chapter 2:
   https://vst.cs.princeton.edu/download/PLCC-to-chapter-3.pdf *)

From Coq Require Import Strings.String ZArith.
Require Import Lia.
From LongDivision Require Import Imp Hoare.
Open Scope string_scope.

Definition a := "a".
Definition b := "b".
Definition n := "n".
Definition z := "z".
Definition q := "q".
Definition r := "r".

Open Scope imp_scope.
Open Scope hoare_spec_scope.
Open Scope Z.
Open Scope Z_scope.

Ltac obliterate :=
  repeat match goal with
  | |- {{ _ }} _ ;; _ {{ _ }} => eapply hoare_seq
  | |- {{ _ }} _ ::= _ {{ _ }} => apply hoare_floyd
  | |- {{ _ }} TEST _ THEN _ ELSE _ FI {{ _ }} => apply hoare_if
  | |- {{ _ }} SKIP {{ _ }} => apply hoare_skip
  end.

Ltac crunch_hyp :=
  repeat match goal with
  | H : ex _ |- _ => inv H
  | H : _ /\ _ |- _ => inv H
  end.

Ltac solve_neq :=
  match goal with
  | |- ?a <> ?b => unfold a, b, not; intro; discriminate
  end.

Theorem long_division_correct : forall a0 b0,
  {{ fun st => st a >= 0 /\ st b > 0 /\ st a = a0 /\ st b = b0 }}
  n ::= 0;;
  z ::= b;;
  WHILE z <= a DO
    n ::= n + 1;;
    z ::= z + z
  END;;
  q ::= 0;;
  r ::= a;;
  WHILE n > 0 DO
    n ::= n - 1;;
    z ::= z / 2;;
    q ::= q + q;;
    TEST z <= r THEN
      q ::= q + 1;;
      r ::= r - z
    ELSE
      SKIP
    FI
  END
  {{ fun st => st a = st q * st b + st r /\ 0 <= st r < st b /\ st a = a0 /\ st b = b0 }}.
Proof.
  intros; obliterate.
  - eapply hoare_consequence with (P' := fun st =>
      st z = st b * 2 ^ st n /\ st n >= 0 /\ st a >= 0 /\
      st b > 0 /\ st a = a0 /\ st b = b0).
    + unfold assert_implies; simpl; intros; crunch_hyp;
        repeat split; try (rewrite H, H2; now try solve_neq).
      * rewrite <- H in H1; try solve_neq.
        rewrite H1; simpl; symmetry; rewrite H; try lia;
            solve_neq.
      * rewrite H; try solve_neq; lia.
    + apply hoare_while; obliterate.
      eapply hoare_consequence; obliterate.
      * unfold assert_implies; intros; exact H.
      * unfold assert_implies; simpl; intros; crunch_hyp;
          repeat split; try (rewrite H, H2; now try solve_neq).
        { apply Z.leb_le in H5.
          replace (x0 z) with (x z) in *
            by (apply H2; solve_neq).
          rewrite H0 in *; clear H0.
          replace (st b) with (x0 b) by (rewrite H, H2;
            now try solve_neq).
          replace (st n) with (x n) by (symmetry; apply H;
            solve_neq).
          rewrite H1 in *; clear H1.
          rewrite Z.pow_add_r; lia. }
        { rewrite H; try solve_neq; lia. }
    + unfold assert_implies; intros; exact H.
  - eapply hoare_consequence with (P' := fun st =>
      st a = st q * st z + st r /\ 0 <= st r < st z /\
      st z = st b * 2 ^ st n /\ st n >= 0 /\ st a = a0 /\
      st b = b0).
    + unfold assert_implies; simpl; intros; repeat split;
        crunch_hyp; rewrite Z.leb_gt in H5;
        try (repeat rewrite H, H2; now try solve_neq).
      * replace (st q) with (x q) by (rewrite H;
          now try solve_neq).
        rewrite H0.
        replace (x a) with (st a) by (apply H; solve_neq);
          nia.
      * rewrite H0, H2; try solve_neq; lia.
      * rewrite H0, H; try solve_neq.
        do 2 try rewrite H2; now try solve_neq.
    + apply hoare_while; obliterate.
      * eapply hoare_consequence; obliterate;
          unfold assert_implies; simpl; intros; try exact H;
          repeat split; crunch_hyp; rewrite Z.leb_le in H5;
          rewrite Z.gtb_lt in H12;
          try (rewrite H, H2, H3, H7, H9; now try solve_neq).
        { rewrite H, H2, H3, H7, H9, H11; try solve_neq.
          rewrite H0 in *.
          rewrite H; try solve_neq.
          rewrite H1, H4 in *.
          replace (x1 q) with (x3 q) in * by (rewrite H7, H9;
            now try solve_neq).
          replace (x2 z) with (x3 z) in * by (rewrite H9;
            now try solve_neq).
          replace (st z) with (x z) in * by (rewrite H;
            now try solve_neq).
          replace (x z) with (x1 z) in * by (rewrite H2, H3;
            now try solve_neq).
          replace (x r) with (x3 r) in *
            by (rewrite H2, H3, H7, H9; now try solve_neq).
          rewrite H6, H13.
          assert (x3 n = x2 n + 1) by lia.
          rewrite H10.
          rewrite Z.pow_add_r; try lia; simpl;
            unfold Z.pow_pos; simpl.
          replace (x3 b * (2 ^ x2 n * 2))
            with (x3 b * 2 ^ x2 n * 2) in * by lia.
          rewrite Z.div_mul; lia. }
        { do 2 rewrite H2 in H0; try solve_neq; lia. }
        { rewrite H0.
          replace (x r) with (x3 r) in *
            by (rewrite H2, H3, H7, H9; now try solve_neq).
          replace (st z) with (x z) in * by (rewrite H;
            now try solve_neq).
          replace (x z) with (x1 z) in * by (rewrite H2, H3;
            now try solve_neq).
          replace (x2 z) with (x3 z) in * by (rewrite H9;
            now try solve_neq).
          assert (x3 r < 2 * x1 z -> x3 r - x1 z < x1 z)
            by lia.
          apply H10; clear H10.
          rewrite H6, H13 in *.
          assert (x3 n = x2 n + 1) by lia.
          rewrite H10 in *.
          rewrite Z.pow_add_r in *; try lia.
          replace (2 ^ 1) with 2 in * by reflexivity.
          replace (x3 b * (2 ^ x2 n * 2))
            with (x3 b * 2 ^ x2 n * 2) in * by lia.
          rewrite Z.div_mul; lia. }
        { replace (st z) with (x z) in * by (rewrite H;
            now try solve_neq).
          replace (x z) with (x0 z) in * by (rewrite H2;
            now try solve_neq).
          replace (x0 z) with (x1 z) in * by (rewrite H3;
            now try solve_neq).
          rewrite H6 in *.
          replace (x2 z) with (x3 z) in * by (rewrite H9;
            now try solve_neq).
          rewrite H13 in *.
          assert (x3 n = x2 n + 1) by lia.
          replace (st n) with (x2 n) in *
            by (rewrite H, H2, H3, H7; now try solve_neq).
          rewrite H10 in *.
          rewrite Z.pow_add_r; try lia; simpl;
            unfold Z.pow_pos; simpl.
          replace (x3 b * (2 ^ x2 n * 2))
            with (x3 b * 2 ^ x2 n * 2) by lia.
          rewrite Z.div_mul; try lia.
          now replace (st b) with (x3 b)
            by (rewrite H, H2, H3, H7, H9; now try solve_neq). }
        { replace (st n) with (x2 n)
            by (rewrite H, H2, H3, H7; now try solve_neq);
            lia. }
      * eapply hoare_consequence; obliterate;
          unfold assert_implies; intros; try exact H;
          simpl in *; repeat split; crunch_hyp;
          rewrite Z.leb_gt in H1; rewrite Z.gtb_lt in H8;
          try (rewrite H0, H3, H5; now try solve_neq); auto.
        { replace (st a) with (x1 a) in *
            by (rewrite H0, H3, H5; now try solve_neq).
          rewrite H7 in *.
          replace (x q) with (x1 q) in * by (rewrite H3, H5;
            now try solve_neq).
          rewrite H in *.
          replace (st z) with (x z) in * by (rewrite H0;
            now try solve_neq).
          replace (x0 z) with (x1 z) in * by (rewrite H5;
            now try solve_neq).
          rewrite H2, H9 in *.
          assert (x1 n = x0 n + 1) by lia.
          rewrite H6 in *.
          rewrite Z.pow_add_r; try lia; simpl;
            unfold Z.pow_pos; simpl.
          replace (st r) with (x1 r) in *
            by (rewrite H0, H3, H5; now try solve_neq).
          replace (x1 b * (2 ^ x0 n * 2))
            with (x1 b * 2 ^ x0 n * 2) in * by lia.
          rewrite Z.div_mul; lia. }
        { replace (st z) with (x z) in * by (rewrite H0;
            now try solve_neq).
          replace (x0 z) with (x1 z) in * by (rewrite H5;
            now try solve_neq).
          rewrite H2, H9.
          replace (st b) with (x1 b) in *
            by (rewrite H0, H3, H5; now try solve_neq).
          replace (st n) with (x0 n) in * by (rewrite H0, H3;
            now try solve_neq).
          assert (x1 n = x0 n + 1) by lia.
          rewrite H6 in *.
          rewrite Z.pow_add_r; try lia; simpl;
            unfold Z.pow_pos; simpl.
          replace (x1 b * (2 ^ x0 n * 2))
            with (x1 b * 2 ^ x0 n * 2) by lia.
          rewrite Z.div_mul; lia. }
        { replace (st n) with (x0 n) by (rewrite H0, H3;
            now try solve_neq); lia. }
    + unfold assert_implies; simpl; intros; repeat split;
        crunch_hyp; rewrite Z.gtb_ltb, Z.ltb_ge in H1;
        try (replace (st n) with 0 in * by lia; simpl in *);
        nia.
Qed.

Print Assumptions long_division_correct.

Close Scope Z_scope.
Close Scope Z.
Close Scope hoare_spec_scope.
Close Scope imp_scope.
Close Scope string_scope.