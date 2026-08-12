From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticRootProjectionI LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Small cyclic-algebra representatives shared by the P2 and P3
    numerator certificates.  Their evaluation lemmas are the semantic
    boundary between the five-coordinate computations and Lazard's root
    formulas. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorCommon.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section RootFourierNumeratorCommon.

Variable F : fieldType.

Add Ring lazard_root_fourier_numerator_common_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_fourier_numerator_common_ring :=
  repeat first
    [ rewrite NR.lazard_numerator_ring_addE
    | rewrite NR.lazard_numerator_ring_mulE
    | rewrite NR.lazard_numerator_ring_subE
    | rewrite NR.lazard_numerator_ring_oppE
    | rewrite NR.lazard_numerator_ring_zeroE
    | rewrite NR.lazard_numerator_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Definition lazard_cyclic_constant (c : F) : LazardCyclicFive F :=
  {| lazard_cyclic0 := c;
     lazard_cyclic1 := 0;
     lazard_cyclic2 := 0;
     lazard_cyclic3 := 0;
     lazard_cyclic4 := 0 |}.

Lemma lazard_cyclic_constant_eval omega c :
  lazard_cyclic_eval omega (lazard_cyclic_constant c) = c.
Proof.
by rewrite /lazard_cyclic_eval /lazard_cyclic_constant /=
  !mulr0 !addr0.
Qed.

(** Cyclic representatives of [A = omega - omega^4] and
    [B = omega^2 - omega^3]. *)
Definition lazard_cyclic_fifth_root_A : LazardCyclicFive F :=
  {| lazard_cyclic0 := 0;
     lazard_cyclic1 := 1;
     lazard_cyclic2 := 0;
     lazard_cyclic3 := 0;
     lazard_cyclic4 := -1 |}.

Definition lazard_cyclic_fifth_root_B : LazardCyclicFive F :=
  {| lazard_cyclic0 := 0;
     lazard_cyclic1 := 0;
     lazard_cyclic2 := 1;
     lazard_cyclic3 := -1;
     lazard_cyclic4 := 0 |}.

Lemma lazard_cyclic_fifth_root_A_eval omega :
  lazard_cyclic_eval omega lazard_cyclic_fifth_root_A =
    RR.lazard_fifth_root_A omega.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_fifth_root_A
  /RR.lazard_fifth_root_A /=.
finish_lazard_root_fourier_numerator_common_ring.
Qed.

Lemma lazard_cyclic_fifth_root_B_eval omega :
  lazard_cyclic_eval omega lazard_cyclic_fifth_root_B =
    RR.lazard_fifth_root_B omega.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_fifth_root_B
  /RR.lazard_fifth_root_B /=.
finish_lazard_root_fourier_numerator_common_ring.
Qed.

(** Root epsilon in the cyclic algebra. *)
Definition lazard_cyclic_root_epsilon (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_scale (lazard_root_epsilon_product roots)
    (@PolynomialFormulasLazardQuinticRootProjectionI.lazard_cyclic_discriminant F).

Lemma lazard_cyclic_root_epsilon_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_root_epsilon roots) =
    lazard_root_epsilon omega roots.
Proof.
rewrite /lazard_cyclic_root_epsilon lazard_cyclic_eval_scale
  PolynomialFormulasLazardQuinticRootProjectionI.lazard_cyclic_discriminant_eval
  /lazard_root_epsilon.
by rewrite mulrC.
Qed.

(** [T = A T' + B U'] in cyclic form. *)
Definition lazard_cyclic_root_T (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_add
    (lazard_cyclic_scale (RR.lazard_root_T_prime roots)
      lazard_cyclic_fifth_root_A)
    (lazard_cyclic_scale (RR.lazard_root_U_prime roots)
      lazard_cyclic_fifth_root_B).

Lemma lazard_cyclic_root_T_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_root_T roots) =
    RR.lazard_root_T omega roots.
Proof.
rewrite /lazard_cyclic_root_T lazard_cyclic_eval_add
  !lazard_cyclic_eval_scale lazard_cyclic_fifth_root_A_eval
  lazard_cyclic_fifth_root_B_eval /RR.lazard_root_T.
finish_lazard_root_fourier_numerator_common_ring.
Qed.

(** Formula-sign [U = A U' - B T'] in cyclic form. *)
Definition lazard_cyclic_root_formula_U (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_sub
    (lazard_cyclic_scale (RR.lazard_root_U_prime roots)
      lazard_cyclic_fifth_root_A)
    (lazard_cyclic_scale (RR.lazard_root_T_prime roots)
      lazard_cyclic_fifth_root_B).

Lemma lazard_cyclic_root_formula_U_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_root_formula_U roots) =
    RR.lazard_root_formula_U omega roots.
Proof.
rewrite /lazard_cyclic_root_formula_U lazard_cyclic_eval_sub
  !lazard_cyclic_eval_scale lazard_cyclic_fifth_root_A_eval
  lazard_cyclic_fifth_root_B_eval /RR.lazard_root_formula_U
  /RR.lazard_root_printed_U.
finish_lazard_root_fourier_numerator_common_ring.
Qed.

End RootFourierNumeratorCommon.

End PolynomialFormulasLazardQuinticRootFourierNumeratorCommon.
