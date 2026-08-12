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

Module PolynomialFormulasLazardQuinticDeterminantCriticalInputA.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module LR := PolynomialFormulasLazardQuinticResolventPolynomial.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Module D := PolynomialFormulasLazardQuinticDeterminantCriticalData.
Local Open Scope ring_scope.

Section InputA.

Variable F : fieldType.

Add Ring lazard_detcritical_inputA_ring :
  (@NR.lazard_numerator_ring_theory F).
Add Field lazard_detcritical_inputA_field :
  (@CE.lazard_critical_field_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq CE.lazard_critical_div
  CE.lazard_critical_inv.

Ltac finish_lazard_detcritical_inputA_field :=
  lazard_detcritical_prepare;
  repeat first
    [ rewrite CE.lazard_critical_divE | rewrite CE.lazard_critical_invE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  field.

Theorem lazard_detcritical_PA0_eval c
    (two_neq0 : (2%:R : F) != 0) :
  (D.lazard_detcritical_PA0 c).[RP.lazard_root_s c] =
    CE.lazard_critical_g c -
      2%:R * CE.lazard_critical_b c * CE.lazard_critical_e c.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0; by rewrite htwo eqxx.
rewrite /D.lazard_detcritical_PA0 !hornerE
  /D.lazard_detcritical_A00 /D.lazard_detcritical_A01
  /D.lazard_detcritical_A02
  /CE.lazard_critical_a /CE.lazard_critical_b
  /CE.lazard_critical_g /CE.lazard_critical_e
  /LR.lazard_resolvent_cubic_a /LR.lazard_resolvent_cubic_b
  /LR.lazard_resolvent_cubic_g /LR.lazard_resolvent_linear_e
  /LR.lazard_resolvent_core_linear /LR.lazard_resolvent_core_constant.
finish_lazard_detcritical_inputA_field.
Qed.

Theorem lazard_detcritical_PA1_eval c
    (two_neq0 : (2%:R : F) != 0) :
  (D.lazard_detcritical_PA1 c).[RP.lazard_root_s c] =
    - 4%:R * CE.lazard_critical_a c * CE.lazard_critical_e c -
      CE.lazard_critical_b c.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0; by rewrite htwo eqxx.
rewrite /D.lazard_detcritical_PA1 !hornerE
  /D.lazard_detcritical_A10 /D.lazard_detcritical_A11
  /CE.lazard_critical_a /CE.lazard_critical_b /CE.lazard_critical_e
  /LR.lazard_resolvent_cubic_a /LR.lazard_resolvent_cubic_b
  /LR.lazard_resolvent_linear_e /LR.lazard_resolvent_core_linear.
finish_lazard_detcritical_inputA_field.
Qed.

Theorem lazard_detcritical_PA2_eval c
    (two_neq0 : (2%:R : F) != 0) :
  (D.lazard_detcritical_PA2 c).[RP.lazard_root_s c] =
    - 3%:R * CE.lazard_critical_a c -
      6%:R * CE.lazard_critical_e c.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0; by rewrite htwo eqxx.
rewrite /D.lazard_detcritical_PA2 !hornerE
  /D.lazard_detcritical_A20 /CE.lazard_critical_a
  /CE.lazard_critical_e /LR.lazard_resolvent_cubic_a
  /LR.lazard_resolvent_linear_e.
finish_lazard_detcritical_inputA_field.
Qed.

Theorem lazard_detcritical_PA3_eval c :
  (D.lazard_detcritical_PA3 c).[RP.lazard_root_s c] = - 5%:R.
Proof. by rewrite /D.lazard_detcritical_PA3 /D.lazard_detcritical_A30 hornerC. Qed.

End InputA.

Print Assumptions lazard_detcritical_PA0_eval.
Print Assumptions lazard_detcritical_PA1_eval.
Print Assumptions lazard_detcritical_PA2_eval.

End PolynomialFormulasLazardQuinticDeterminantCriticalInputA.
