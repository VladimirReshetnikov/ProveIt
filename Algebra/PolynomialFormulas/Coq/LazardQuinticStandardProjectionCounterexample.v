From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import LazardQuinticProjection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The standard projection denominator can vanish when [-1] is a square.
    This is the elementary obstruction behind the field-hypothesis caveat in
    Lazard's Section 5; the alternate matrix repairs this particular failure. *)
Module PolynomialFormulasLazardQuinticStandardProjectionCounterexample.

Import GRing.Theory.
Local Open Scope ring_scope.

Module P := PolynomialFormulasLazardQuinticProjection.

Section Counterexample.

Variable F : fieldType.

Lemma lazard_standard_projection_matrix_singular_of_sqrt_neg_one
    (epsilon i : F) (hi : i ^+ 2 = - 1) :
  \det (P.lazard_standard_projection_matrix epsilon 1 i) = 0.
Proof.
by rewrite P.lazard_standard_projection_matrix_det expr1n hi addrN mulr0.
Qed.

Lemma lazard_alternate_denominator_one_neq0_of_sqrt_neg_one
    (i : F) (hi : i ^+ 2 = - 1)
    (five_neq0 : (5%:R : F) != 0) :
  P.lazard_alternate_denominator 1 i != 0.
Proof.
apply/eqP=> hden.
have hi_two : i = 2%:R.
  rewrite (@natrD F 1 1).
  apply: subr0_eq.
  rewrite opprD.
  move: hden.
  rewrite /P.lazard_alternate_denominator mul1r expr1n hi.
  move=> hden'.
  by rewrite -addrA in hden'.
have hfour : (4%:R : F) = - 1.
  rewrite (@natrM F 2 2) -expr2 -hi_two.
  exact hi.
have hfive : (5%:R : F) = 0.
  rewrite (@natrD F 4 1) hfour.
  exact: addNr.
move: five_neq0.
by rewrite hfive eqxx.
Qed.

Lemma lazard_alternate_projection_matrix_nonsingular_of_sqrt_neg_one
    (epsilon i : F) (hi : i ^+ 2 = - 1)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0) :
  \det (P.lazard_alternate_projection_matrix epsilon 1 i) != 0.
Proof.
exact: P.lazard_alternate_projection_matrix_det_neq0
  two_neq0 epsilon_neq0
  (lazard_alternate_denominator_one_neq0_of_sqrt_neg_one hi five_neq0).
Qed.

End Counterexample.

Print Assumptions
  lazard_standard_projection_matrix_singular_of_sqrt_neg_one.
Print Assumptions
  lazard_alternate_projection_matrix_nonsingular_of_sqrt_neg_one.

End PolynomialFormulasLazardQuinticStandardProjectionCounterexample.
