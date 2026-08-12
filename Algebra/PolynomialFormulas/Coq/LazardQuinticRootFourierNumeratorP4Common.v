From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections
  LazardQuinticRootProjectionI LazardQuinticFourierNumerators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Cyclic-algebra presentation of Lazard's cleared P4 numerator identity.
    Keeping the fifth-root relation outside the coefficient definitions lets
    the final proof reduce to equality of five small root polynomials. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP4Common.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticRootProjectionI.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Local Open Scope ring_scope.

Section RootFourierNumeratorP4Common.

Variable F : fieldType.

(** The group-algebra representative of the root-defined epsilon. *)
Definition lazard_cyclic_root_epsilon (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_scale (lazard_root_epsilon_product roots)
    (@lazard_cyclic_discriminant F).

Lemma lazard_cyclic_root_epsilon_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_root_epsilon roots) =
    lazard_root_epsilon omega roots.
Proof.
rewrite /lazard_cyclic_root_epsilon lazard_cyclic_eval_scale
  lazard_cyclic_discriminant_eval /lazard_root_epsilon.
by rewrite mulrC.
Qed.

(** P42 is omega-free, hence occupies only the zeroth cyclic coordinate. *)
Definition lazard_cyclic_p42_constant (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  {| lazard_cyclic0 :=
       lazard_p42 (lazard_depressed_of_roots roots)
         (lazard_root_invariants roots);
     lazard_cyclic1 := 0;
     lazard_cyclic2 := 0;
     lazard_cyclic3 := 0;
     lazard_cyclic4 := 0 |}.

Lemma lazard_cyclic_p42_constant_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_p42_constant roots) =
    lazard_p42 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
by rewrite /lazard_cyclic_eval /lazard_cyclic_p42_constant /=
  !mulr0 !addr0.
Qed.

(** The cyclic representative of
    [epsilon * (P1 * P4 - P2 * P3)]. *)
Definition lazard_cyclic_p42_fourier (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_mul (lazard_cyclic_root_epsilon roots)
    (lazard_cyclic_sub
      (lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
        (lazard_cyclic_fourier_P4 roots))
      (lazard_cyclic_mul (lazard_cyclic_fourier_P2 roots)
        (lazard_cyclic_fourier_P3 roots))).

Lemma lazard_cyclic_p42_fourier_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_p42_fourier roots) =
    lazard_root_epsilon omega roots *
      (lazard_root_fourier_P1 omega roots *
          lazard_root_fourier_P4 omega roots -
       lazard_root_fourier_P2 omega roots *
          lazard_root_fourier_P3 omega roots).
Proof.
by rewrite /lazard_cyclic_p42_fourier
  (@lazard_cyclic_eval_mul F omega _ _ omega_primitive)
  lazard_cyclic_root_epsilon_eval lazard_cyclic_eval_sub
  (@lazard_cyclic_eval_mul F omega _ _ omega_primitive)
  (@lazard_cyclic_eval_mul F omega _ _ omega_primitive)
  lazard_cyclic_fourier_P1_eval lazard_cyclic_fourier_P2_eval
  lazard_cyclic_fourier_P3_eval lazard_cyclic_fourier_P4_eval.
Qed.

(** Difference whose five coefficients become identical after eliminating
    the depressed fifth root.  Its evaluation therefore vanishes at a
    primitive fifth root. *)
Definition lazard_cyclic_p42_difference (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_sub (lazard_cyclic_p42_constant roots)
    (lazard_cyclic_p42_fourier roots).

Lemma lazard_cyclic_p42_difference_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_p42_difference roots) =
    lazard_p42 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots) -
      lazard_root_epsilon omega roots *
        (lazard_root_fourier_P1 omega roots *
            lazard_root_fourier_P4 omega roots -
         lazard_root_fourier_P2 omega roots *
            lazard_root_fourier_P3 omega roots).
Proof.
by rewrite /lazard_cyclic_p42_difference lazard_cyclic_eval_sub
  lazard_cyclic_p42_constant_eval
  (lazard_cyclic_p42_fourier_eval roots omega_primitive).
Qed.

End RootFourierNumeratorP4Common.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP4Common.
