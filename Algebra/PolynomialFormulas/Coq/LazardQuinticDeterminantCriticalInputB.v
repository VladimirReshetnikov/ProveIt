From Stdlib Require Import Ring Field.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticResolventPolynomial
  LazardQuinticCriticalElimination
  LazardQuinticDeterminantCriticalData
  LazardQuinticDeterminantCriticalSupport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticDeterminantCriticalInputB.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module LR := PolynomialFormulasLazardQuinticResolventPolynomial.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Module D := PolynomialFormulasLazardQuinticDeterminantCriticalData.
Local Open Scope ring_scope.

Section InputB.

Variable F : fieldType.

Add Ring lazard_detcritical_inputB_ring :
  (@NR.lazard_numerator_ring_theory F).
Add Field lazard_detcritical_inputB_field :
  (@CE.lazard_critical_field_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq CE.lazard_critical_div
  CE.lazard_critical_inv.

Ltac finish_lazard_detcritical_inputB_field :=
  lazard_detcritical_prepare;
  repeat first
    [ rewrite CE.lazard_critical_divE | rewrite CE.lazard_critical_invE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  field.

Theorem lazard_detcritical_PB0_eval c
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  (D.lazard_detcritical_PB0 c).[RP.lazard_root_s c] =
    CE.lazard_critical_remainder0 c.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0; by rewrite htwo eqxx.
have five_not0 : (5%:R : F) <> 0.
  move=> hfive; move: five_neq0; by rewrite hfive eqxx.
rewrite /D.lazard_detcritical_PB0 !hornerE
  /D.lazard_detcritical_B00 /D.lazard_detcritical_B01
  /D.lazard_detcritical_B02 /D.lazard_detcritical_B03
  /D.lazard_detcritical_B04
  /CE.lazard_critical_remainder0
  /CE.lazard_square_linear_critical_remainder0
  /CE.lazard_critical_a /CE.lazard_critical_b
  /CE.lazard_critical_g /CE.lazard_critical_d /CE.lazard_critical_e
  /LR.lazard_resolvent_cubic_a /LR.lazard_resolvent_cubic_b
  /LR.lazard_resolvent_cubic_g /LR.lazard_resolvent_linear_e
  /LR.lazard_resolvent_core_linear /LR.lazard_resolvent_core_constant
  /LR.lazard_resolvent_discriminant.
finish_lazard_detcritical_inputB_field.
Qed.

Theorem lazard_detcritical_PB1_eval c
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  (D.lazard_detcritical_PB1 c).[RP.lazard_root_s c] =
    CE.lazard_critical_remainder1 c.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0; by rewrite htwo eqxx.
have five_not0 : (5%:R : F) <> 0.
  move=> hfive; move: five_neq0; by rewrite hfive eqxx.
rewrite /D.lazard_detcritical_PB1 !hornerE
  /D.lazard_detcritical_B10 /D.lazard_detcritical_B11
  /D.lazard_detcritical_B12
  /CE.lazard_critical_remainder1
  /CE.lazard_square_linear_critical_remainder1
  /CE.lazard_critical_a /CE.lazard_critical_b
  /CE.lazard_critical_g /CE.lazard_critical_e
  /LR.lazard_resolvent_cubic_a /LR.lazard_resolvent_cubic_b
  /LR.lazard_resolvent_cubic_g /LR.lazard_resolvent_linear_e
  /LR.lazard_resolvent_core_linear /LR.lazard_resolvent_core_constant.
finish_lazard_detcritical_inputB_field.
Qed.

Theorem lazard_detcritical_PB2_eval c
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  (D.lazard_detcritical_PB2 c).[RP.lazard_root_s c] =
    CE.lazard_critical_remainder2 c.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0; by rewrite htwo eqxx.
have five_not0 : (5%:R : F) <> 0.
  move=> hfive; move: five_neq0; by rewrite hfive eqxx.
rewrite /D.lazard_detcritical_PB2 !hornerE
  /D.lazard_detcritical_B20 /D.lazard_detcritical_B21
  /D.lazard_detcritical_B22
  /CE.lazard_critical_remainder2
  /CE.lazard_square_linear_critical_remainder2
  /CE.lazard_critical_a /CE.lazard_critical_b
  /CE.lazard_critical_g /CE.lazard_critical_e
  /LR.lazard_resolvent_cubic_a /LR.lazard_resolvent_cubic_b
  /LR.lazard_resolvent_cubic_g /LR.lazard_resolvent_linear_e
  /LR.lazard_resolvent_core_linear /LR.lazard_resolvent_core_constant.
finish_lazard_detcritical_inputB_field.
Qed.

End InputB.

Print Assumptions lazard_detcritical_PB0_eval.
Print Assumptions lazard_detcritical_PB1_eval.
Print Assumptions lazard_detcritical_PB2_eval.

End PolynomialFormulasLazardQuinticDeterminantCriticalInputB.
