From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootInvariantE LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootFourierNumeratorP3Common
  LazardQuinticRootFourierNumeratorP3Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's P3 numerator identity and its displayed division formula,
    derived directly from ordered roots. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module RE := PolynomialFormulasLazardQuinticRootInvariantE.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module Common := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Common.
Module Core := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Core.
Local Open Scope ring_scope.

Section RootFourierNumeratorP3.
Variable F : fieldType.

Add Ring lazard_root_fourier_numerator_P3_final_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_fourier_numerator_P3_final_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** First, the raw root-product normalization [E = -(T'^2+U'^2)]. *)
Lemma lazard_root_fourier_P3_cleared_numerator_raw omega
    (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  5%:R * lazard_root_epsilon omega roots * Q.lazard_root_E roots *
        lazard_p31 (lazard_depressed_of_roots roots) +
      5%:R * Q.lazard_root_E roots *
        lazard_p32 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) +
      2%:R * lazard_root_epsilon omega roots *
        (lazard_p33 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) * RR.lazard_root_T omega roots +
         lazard_p34 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) *
              RR.lazard_root_formula_U omega roots) =
    20%:R * lazard_root_epsilon omega roots * Q.lazard_root_E roots *
      lazard_root_fourier_P1 omega roots ^+ 2 *
      lazard_root_fourier_P3 omega roots.
Proof.
have [h01 [h12 [h23 h34]]] :=
  Core.lazard_cyclic_p3_numerator_difference_coefficients_equal
    (roots := roots) (hsum := hsum).
have heval := lazard_cyclic_eval_equal_tail
  (omega := omega)
  (a := Common.lazard_cyclic_p3_numerator_difference roots)
  (omega_primitive := omega_primitive)
  (h12 := h12) (h23 := h23) (h34 := h34).
rewrite h01 subrr in heval.
rewrite (Common.lazard_cyclic_p3_numerator_difference_eval
  (omega := omega) (roots := roots)
  (omega_primitive := omega_primitive)) in heval.
exact: subr0_eq heval.
Qed.

(** Displayed-coefficient form of the same denominator-free identity. *)
Theorem lazard_root_fourier_P3_cleared_numerator omega
    (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  5%:R * lazard_root_epsilon omega roots *
        lazard_invariant_E (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) *
        lazard_p31 (lazard_depressed_of_roots roots) +
      5%:R * lazard_invariant_E (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) *
        lazard_p32 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) +
      2%:R * lazard_root_epsilon omega roots *
        (lazard_p33 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) * RR.lazard_root_T omega roots +
         lazard_p34 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) *
              RR.lazard_root_formula_U omega roots) =
    20%:R * lazard_root_epsilon omega roots *
      lazard_invariant_E (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots) *
      lazard_root_fourier_P1 omega roots ^+ 2 *
      lazard_root_fourier_P3 omega roots.
Proof.
rewrite !(@RE.lazard_root_invariant_E_eq F roots hsum).
exact: (@lazard_root_fourier_P3_cleared_numerator_raw F omega roots
  omega_primitive hsum).
Qed.

(** Clearing and then cancelling exactly the three displayed denominators. *)
Lemma lazard_fourier_P3_formula_of_cleared_numerator
    (c : LazardDepressedRootCoefficients F)
    (i : LazardRootInvariants F) (v : Q.lazard_quadratic_triple F)
    (p1 p3 : F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : Q.lazard_epsilon v != 0)
    (E_neq0 : lazard_invariant_E c i != 0)
    (p1_neq0 : p1 != 0)
    (hcleared :
      5%:R * Q.lazard_epsilon v * lazard_invariant_E c i *
            lazard_p31 c +
        5%:R * lazard_invariant_E c i * lazard_p32 c i +
        2%:R * Q.lazard_epsilon v *
          (lazard_p33 c i * Q.lazard_t v +
            lazard_p34 c i * Q.lazard_u v) =
      20%:R * Q.lazard_epsilon v * lazard_invariant_E c i *
        p1 ^+ 2 * p3) :
  lazard_fourier_P3_formula c i v p1 = p3.
Proof.
have four_neq0 : (4%:R : F) != 0.
  rewrite NR.lazard_numerator_four_natrE.
  exact: mulf_neq0 two_neq0 two_neq0.
have ten_neq0 : (10%:R : F) != 0.
  rewrite NR.lazard_numerator_ten_natrE.
  exact: mulf_neq0 five_neq0 two_neq0.
have twenty_neq0 : (20%:R : F) != 0.
  rewrite NR.lazard_numerator_twenty_natrE.
  exact: mulf_neq0 ten_neq0 two_neq0.
have p1_sq_neq0 : p1 ^+ 2 != 0 := expf_neq0 2 p1_neq0.
have d1_neq0 : 4%:R * p1 ^+ 2 != 0 :=
  mulf_neq0 four_neq0 p1_sq_neq0.
have d2_neq0 : 4%:R * Q.lazard_epsilon v * p1 ^+ 2 != 0 :=
  mulf_neq0 (mulf_neq0 four_neq0 epsilon_neq0) p1_sq_neq0.
have d3_neq0 :
    10%:R * lazard_invariant_E c i * p1 ^+ 2 != 0 :=
  mulf_neq0 (mulf_neq0 ten_neq0 E_neq0) p1_sq_neq0.
have common_neq0 :
    20%:R * Q.lazard_epsilon v * lazard_invariant_E c i *
      p1 ^+ 2 != 0 :=
  mulf_neq0
    (mulf_neq0 (mulf_neq0 twenty_neq0 epsilon_neq0) E_neq0)
    p1_sq_neq0.
have h1 :
    (20%:R * Q.lazard_epsilon v * lazard_invariant_E c i * p1 ^+ 2) *
        (lazard_p31 c / (4%:R * p1 ^+ 2)) =
      5%:R * Q.lazard_epsilon v * lazard_invariant_E c i *
        lazard_p31 c.
  transitivity
    ((5%:R * Q.lazard_epsilon v * lazard_invariant_E c i) *
      ((lazard_p31 c / (4%:R * p1 ^+ 2)) *
        (4%:R * p1 ^+ 2))).
  - finish_lazard_root_fourier_numerator_P3_final_ring.
  - by rewrite divfK //; finish_lazard_root_fourier_numerator_P3_final_ring.
have h2 :
    (20%:R * Q.lazard_epsilon v * lazard_invariant_E c i * p1 ^+ 2) *
        (lazard_p32 c i /
          (4%:R * Q.lazard_epsilon v * p1 ^+ 2)) =
      5%:R * lazard_invariant_E c i * lazard_p32 c i.
  transitivity
    ((5%:R * lazard_invariant_E c i) *
      ((lazard_p32 c i /
        (4%:R * Q.lazard_epsilon v * p1 ^+ 2)) *
        (4%:R * Q.lazard_epsilon v * p1 ^+ 2))).
  - finish_lazard_root_fourier_numerator_P3_final_ring.
  - by rewrite divfK //; finish_lazard_root_fourier_numerator_P3_final_ring.
have h3 :
    (20%:R * Q.lazard_epsilon v * lazard_invariant_E c i * p1 ^+ 2) *
        ((lazard_p33 c i * Q.lazard_t v +
            lazard_p34 c i * Q.lazard_u v) /
          (10%:R * lazard_invariant_E c i * p1 ^+ 2)) =
      2%:R * Q.lazard_epsilon v *
        (lazard_p33 c i * Q.lazard_t v +
          lazard_p34 c i * Q.lazard_u v).
  transitivity
    ((2%:R * Q.lazard_epsilon v) *
      (((lazard_p33 c i * Q.lazard_t v +
          lazard_p34 c i * Q.lazard_u v) /
        (10%:R * lazard_invariant_E c i * p1 ^+ 2)) *
        (10%:R * lazard_invariant_E c i * p1 ^+ 2))).
  - finish_lazard_root_fourier_numerator_P3_final_ring.
  - by rewrite divfK //; finish_lazard_root_fourier_numerator_P3_final_ring.
apply: (mulfI common_neq0).
rewrite /lazard_fourier_P3_formula !mulrDr h1 h2 h3 hcleared.
Qed.

Theorem lazard_root_fourier_P3_formula omega (roots : 5.-tuple F)
    (v : Q.lazard_quadratic_triple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (epsilon_matches : Q.lazard_epsilon v = lazard_root_epsilon omega roots)
    (t_matches : Q.lazard_t v = RR.lazard_root_T omega roots)
    (u_matches : Q.lazard_u v = RR.lazard_root_formula_U omega roots)
    (epsilon_neq0 : Q.lazard_epsilon v != 0)
    (E_neq0 : lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) != 0)
    (p1_neq0 : lazard_root_fourier_P1 omega roots != 0) :
  lazard_fourier_P3_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      v (lazard_root_fourier_P1 omega roots) =
    lazard_root_fourier_P3 omega roots.
Proof.
apply: (@lazard_fourier_P3_formula_of_cleared_numerator
  F (lazard_depressed_of_roots roots) (lazard_root_invariants roots) v
  (lazard_root_fourier_P1 omega roots)
  (lazard_root_fourier_P3 omega roots)
  two_neq0 five_neq0 epsilon_neq0 E_neq0 p1_neq0).
rewrite epsilon_matches t_matches u_matches.
exact: (@lazard_root_fourier_P3_cleared_numerator F omega roots
  omega_primitive hsum).
Qed.

Corollary lazard_root_fourier_P3_formula_root_triple omega
    (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (epsilon_neq0 : lazard_root_epsilon omega roots != 0)
    (E_neq0 : lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) != 0)
    (p1_neq0 : lazard_root_fourier_P1 omega roots != 0) :
  lazard_fourier_P3_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      (Q.LazardQuadraticTriple
        (lazard_root_epsilon omega roots)
        (RR.lazard_root_T omega roots)
        (RR.lazard_root_formula_U omega roots))
      (lazard_root_fourier_P1 omega roots) =
    lazard_root_fourier_P3 omega roots.
Proof.
exact: (@lazard_root_fourier_P3_formula F omega roots
  (Q.LazardQuadraticTriple
    (lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots)
    (RR.lazard_root_formula_U omega roots))
  two_neq0 five_neq0 omega_primitive hsum erefl erefl erefl
  epsilon_neq0 E_neq0 p1_neq0).
Qed.

End RootFourierNumeratorP3.
End PolynomialFormulasLazardQuinticRootFourierNumeratorP3.
