From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootFourierNumeratorCommon
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Cyclic-algebra presentation of the cleared P3 numerator. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3Common.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module C := PolynomialFormulasLazardQuinticRootFourierNumeratorCommon.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section RootFourierNumeratorP3Common.

Variable F : fieldType.

Add Ring lazard_root_fourier_numerator_P3_common_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_fourier_numerator_P3_common_ring :=
  repeat first
    [ rewrite NR.lazard_numerator_expr2
    | rewrite NR.lazard_numerator_ring_addE
    | rewrite NR.lazard_numerator_ring_mulE
    | rewrite NR.lazard_numerator_ring_subE
    | rewrite NR.lazard_numerator_ring_oppE
    | rewrite NR.lazard_numerator_ring_zeroE
    | rewrite NR.lazard_numerator_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Definition lazard_cyclic_p3_numerator_left (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  let c := lazard_depressed_of_roots roots in
  let i := lazard_root_invariants roots in
  let E := Q.lazard_root_E roots in
  lazard_cyclic_add
    (lazard_cyclic_scale (5%:R * E * lazard_p31 c)
      (C.lazard_cyclic_root_epsilon roots))
    (lazard_cyclic_add
      (C.lazard_cyclic_constant (5%:R * E * lazard_p32 c i))
      (lazard_cyclic_scale 2%:R
        (lazard_cyclic_mul (C.lazard_cyclic_root_epsilon roots)
          (lazard_cyclic_add
            (lazard_cyclic_scale (lazard_p33 c i)
              (C.lazard_cyclic_root_T roots))
            (lazard_cyclic_scale (lazard_p34 c i)
              (C.lazard_cyclic_root_formula_U roots)))))).

Definition lazard_cyclic_p3_numerator_right (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  let E := Q.lazard_root_E roots in
  lazard_cyclic_scale (20%:R * E)
    (lazard_cyclic_mul (C.lazard_cyclic_root_epsilon roots)
      (lazard_cyclic_mul
        (lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
          (lazard_cyclic_fourier_P1 roots))
        (lazard_cyclic_fourier_P3 roots))).

Definition lazard_cyclic_p3_numerator_difference (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_sub (lazard_cyclic_p3_numerator_left roots)
    (lazard_cyclic_p3_numerator_right roots).

Lemma lazard_cyclic_p3_numerator_difference_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega
      (lazard_cyclic_p3_numerator_difference roots) =
    (5%:R * lazard_root_epsilon omega roots * Q.lazard_root_E roots *
        lazard_p31 (lazard_depressed_of_roots roots) +
      5%:R * Q.lazard_root_E roots *
        lazard_p32 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) +
      2%:R * lazard_root_epsilon omega roots *
        (lazard_p33 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) * RR.lazard_root_T omega roots +
         lazard_p34 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) *
              RR.lazard_root_formula_U omega roots)) -
    20%:R * lazard_root_epsilon omega roots * Q.lazard_root_E roots *
      lazard_root_fourier_P1 omega roots ^+ 2 *
      lazard_root_fourier_P3 omega roots.
Proof.
rewrite /lazard_cyclic_p3_numerator_difference
  /lazard_cyclic_p3_numerator_left /lazard_cyclic_p3_numerator_right.
repeat first
  [ rewrite C.lazard_cyclic_constant_eval
  | rewrite C.lazard_cyclic_root_epsilon_eval
  | rewrite C.lazard_cyclic_root_T_eval
  | rewrite C.lazard_cyclic_root_formula_U_eval
  | rewrite lazard_cyclic_fourier_P1_eval
  | rewrite lazard_cyclic_fourier_P3_eval
  | rewrite lazard_cyclic_eval_sub
  | rewrite lazard_cyclic_eval_add
  | rewrite lazard_cyclic_eval_scale
  | rewrite (@lazard_cyclic_eval_mul F omega _ _ omega_primitive) ].
finish_lazard_root_fourier_numerator_P3_common_ring.
Qed.

End RootFourierNumeratorP3Common.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP3Common.
