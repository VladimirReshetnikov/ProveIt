From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections
  LazardQuinticRootProjectionI LazardQuinticFourierNumerators
  LazardQuinticRootFourierNumeratorP4Common
  LazardQuinticRootFourierNumeratorP4Ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Third adjacent-coefficient certificate for Lazard's P4 numerator. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP4Coeff23.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticRootProjectionI.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Import PolynomialFormulasLazardQuinticRootFourierNumeratorP4Common.
Module P4Ring :=
  PolynomialFormulasLazardQuinticRootFourierNumeratorP4Ring.
Local Open Scope ring_scope.

Section RootFourierNumeratorP4Coeff23.

Variable F : fieldType.

Add Ring lazard_root_fourier_numerator_P4_coeff23_ring :
  (@P4Ring.lazard_p4_ring_theory F).
Opaque P4Ring.lazard_p4_ring_zero P4Ring.lazard_p4_ring_one
  P4Ring.lazard_p4_ring_add P4Ring.lazard_p4_ring_mul
  P4Ring.lazard_p4_ring_sub P4Ring.lazard_p4_ring_opp
  P4Ring.lazard_p4_ring_eq.

Ltac finish_lazard_root_fourier_numerator_P4_coeff23_ring :=
  repeat first
    [ rewrite P4Ring.lazard_p4_seventy_two_natrE
    | rewrite P4Ring.lazard_p4_forty_five_natrE
    | rewrite P4Ring.lazard_p4_fourteen_natrE
    | rewrite lazard_root_projection_seventy_natrE
    | rewrite lazard_root_projection_forty_natrE
    | rewrite lazard_root_projection_ten_natrE
    | rewrite lazard_root_projection_eight_natrE
    | rewrite lazard_root_projection_seven_natrE
    | rewrite lazard_root_projection_five_natrE
    | rewrite lazard_root_projection_four_natrE
    | rewrite lazard_root_projection_three_natrE
    | rewrite lazard_root_projection_two_natrE
    | rewrite lazard_root_projection_expr4
    | rewrite lazard_root_projection_expr3
    | rewrite lazard_root_projection_expr2
    | rewrite expr1
    | rewrite P4Ring.lazard_p4_ring_addE
    | rewrite P4Ring.lazard_p4_ring_mulE
    | rewrite P4Ring.lazard_p4_ring_subE
    | rewrite P4Ring.lazard_p4_ring_oppE
    | rewrite P4Ring.lazard_p4_ring_zeroE
    | rewrite P4Ring.lazard_p4_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (P4Ring.lazard_p4_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_cyclic_p42_difference_coefficient23
    (roots : 5.-tuple F) (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic2 (lazard_cyclic_p42_difference roots) =
    lazard_cyclic3 (lazard_cyclic_p42_difference roots).
Proof.
have hx4 := lazard_root_sum_zero_last hsum.
rewrite /lazard_cyclic_p42_difference /lazard_cyclic_p42_constant
  /lazard_cyclic_p42_fourier /lazard_cyclic_root_epsilon
  /lazard_cyclic_sub /lazard_cyclic_add /lazard_cyclic_neg
  /lazard_cyclic_scale /lazard_cyclic_mul /lazard_cyclic_discriminant
  /lazard_cyclic_fourier_P1 /lazard_cyclic_fourier_P2
  /lazard_cyclic_fourier_P3 /lazard_cyclic_fourier_P4
  /lazard_p42 /lazard_depressed_of_roots /lazard_root_invariants
  /lazard_root_orbit_formula /lazard_root_esymm2 /lazard_root_esymm3
  /lazard_root_esymm4 /lazard_root_esymm5
  /lazard_root_epsilon_product hx4 /=.
finish_lazard_root_fourier_numerator_P4_coeff23_ring.
Qed.

End RootFourierNumeratorP4Coeff23.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP4Coeff23.
