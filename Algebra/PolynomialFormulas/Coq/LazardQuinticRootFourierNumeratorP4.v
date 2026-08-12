From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticVieta LazardQuinticRootProjections
  LazardQuinticRootFourierRelations LazardQuinticFourierNumerators
  LazardQuinticRootFourierNumeratorP4Common
  LazardQuinticRootFourierNumeratorP4Ring
  LazardQuinticRootFourierNumeratorP4Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's P4 numerator identity, derived from the raw ordered roots and
    the already proved Fourier/Vieta relations. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP4.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module V := PolynomialFormulasLazardQuinticVieta.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module Common :=
  PolynomialFormulasLazardQuinticRootFourierNumeratorP4Common.
Module P4Ring :=
  PolynomialFormulasLazardQuinticRootFourierNumeratorP4Ring.
Module Core := PolynomialFormulasLazardQuinticRootFourierNumeratorP4Core.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Local Open Scope ring_scope.

Section RootFourierNumeratorP4.

Variable F : fieldType.

Add Ring lazard_root_fourier_numerator_P4_final_ring :
  (@P4Ring.lazard_p4_ring_theory F).
Opaque P4Ring.lazard_p4_ring_zero P4Ring.lazard_p4_ring_one
  P4Ring.lazard_p4_ring_add P4Ring.lazard_p4_ring_mul
  P4Ring.lazard_p4_ring_sub P4Ring.lazard_p4_ring_opp
  P4Ring.lazard_p4_ring_eq.

Ltac finish_lazard_root_fourier_numerator_P4_final_ring :=
  repeat first
    [ rewrite lazard_root_projection_two_natrE
    | rewrite P4Ring.lazard_p4_ring_addE
    | rewrite P4Ring.lazard_p4_ring_mulE
    | rewrite P4Ring.lazard_p4_ring_subE
    | rewrite P4Ring.lazard_p4_ring_oppE
    | rewrite P4Ring.lazard_p4_ring_zeroE
    | rewrite P4Ring.lazard_p4_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs =>
      change (@P4Ring.lazard_p4_ring_eq F lhs rhs)
  end;
  ring.

(** The antisymmetric P42 identity is the content of the four isolated
    cyclic coefficient certificates. *)
Lemma lazard_root_p42_fourier_difference omega (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_p42 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) =
    lazard_root_epsilon omega roots *
      (lazard_root_fourier_P1 omega roots *
          lazard_root_fourier_P4 omega roots -
       lazard_root_fourier_P2 omega roots *
          lazard_root_fourier_P3 omega roots).
Proof.
have [h01 [h12 [h23 h34]]] :=
  Core.lazard_cyclic_p42_difference_coefficients_equal
    (roots := roots) (hsum := hsum).
have heval := lazard_cyclic_eval_equal_tail
  (omega := omega) (a := Common.lazard_cyclic_p42_difference roots)
  (omega_primitive := omega_primitive)
  (h12 := h12) (h23 := h23) (h34 := h34).
rewrite h01 subrr in heval.
rewrite (Common.lazard_cyclic_p42_difference_eval
  (omega := omega) (roots := roots)
  (omega_primitive := omega_primitive)) in heval.
exact: subr0_eq heval.
Qed.

(** The symmetric P41 identity is exactly Lazard's cyclic-two Vieta
    relation for the actual Fourier sums. *)
Lemma lazard_root_p41_fourier_sum omega (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (five_neq0 : (5%:R : F) != 0)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_p41 (lazard_depressed_of_roots roots) =
    lazard_root_fourier_P1 omega roots *
        lazard_root_fourier_P4 omega roots +
    lazard_root_fourier_P2 omega roots *
        lazard_root_fourier_P3 omega roots.
Proof.
have hrelations := RFR.lazard_root_fourier_relations
  (omega := omega) (omega_primitive := omega_primitive)
  (five_neq0 := five_neq0) (roots := roots) (hsum := hsum).
have hcyclic := V.lazard_relation_cyclic2 hrelations.
rewrite /V.lazard_fourier_cyclic2 expr1 in hcyclic.
rewrite /lazard_p41.
exact: esym hcyclic.
Qed.

(** Denominator-free form of Lazard's P4 reconstruction formula:
    epsilon*p41 + p42 = 2*epsilon*P1*P4. *)
Theorem lazard_root_fourier_P4_cleared_numerator omega
    (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (five_neq0 : (5%:R : F) != 0)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_root_epsilon omega roots *
      lazard_p41 (lazard_depressed_of_roots roots) +
    lazard_p42 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) =
  2%:R * lazard_root_epsilon omega roots *
    lazard_root_fourier_P1 omega roots *
    lazard_root_fourier_P4 omega roots.
Proof.
rewrite (lazard_root_p41_fourier_sum
  (omega := omega) (roots := roots)
  (omega_primitive := omega_primitive)
  (five_neq0 := five_neq0) (hsum := hsum)).
rewrite (lazard_root_p42_fourier_difference
  (omega := omega) (roots := roots)
  (omega_primitive := omega_primitive) (hsum := hsum)).
finish_lazard_root_fourier_numerator_P4_final_ring.
Qed.

(** Division bridge for the displayed P4 formula.  These are exactly its
    three nonzero denominator factors; no genericity condition is hidden in
    the cleared polynomial identity. *)
Lemma lazard_fourier_P4_formula_of_cleared_numerator
    (c : LazardDepressedRootCoefficients F)
    (i : LazardRootInvariants F) (v : Q.lazard_quadratic_triple F)
    (p1 p4 : F)
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : Q.lazard_epsilon v != 0)
    (p1_neq0 : p1 != 0)
    (hcleared :
      Q.lazard_epsilon v * lazard_p41 c + lazard_p42 c i =
        2%:R * Q.lazard_epsilon v * p1 * p4) :
  lazard_fourier_P4_formula c i v p1 = p4.
Proof.
have two_p1_neq0 : 2%:R * p1 != 0 :=
  mulf_neq0 two_neq0 p1_neq0.
have common_neq0 : 2%:R * Q.lazard_epsilon v * p1 != 0 :=
  mulf_neq0 (mulf_neq0 two_neq0 epsilon_neq0) p1_neq0.
have hfirst :
    (2%:R * Q.lazard_epsilon v * p1) *
        (lazard_p41 c / (2%:R * p1)) =
      Q.lazard_epsilon v * lazard_p41 c.
  transitivity
    (Q.lazard_epsilon v *
      ((lazard_p41 c / (2%:R * p1)) * (2%:R * p1))).
  - finish_lazard_root_fourier_numerator_P4_final_ring.
  - by rewrite divfK.
have hsecond :
    (2%:R * Q.lazard_epsilon v * p1) *
        (lazard_p42 c i /
          (2%:R * Q.lazard_epsilon v * p1)) =
      lazard_p42 c i.
  by rewrite [((2%:R * Q.lazard_epsilon v * p1) * _)]mulrC divfK.
apply: (mulfI common_neq0).
rewrite /lazard_fourier_P4_formula mulrDr hfirst hsecond hcleared.
Qed.

(** Therefore the public displayed formula reconstructs the actual fourth
    Fourier component whenever its quadratic certificate carries the
    root-derived epsilon and the displayed denominators are nonzero. *)
Theorem lazard_root_fourier_P4_formula omega (roots : 5.-tuple F)
    (v : Q.lazard_quadratic_triple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (epsilon_matches :
      Q.lazard_epsilon v = lazard_root_epsilon omega roots)
    (epsilon_neq0 : Q.lazard_epsilon v != 0)
    (p1_neq0 : lazard_root_fourier_P1 omega roots != 0) :
  lazard_fourier_P4_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      v (lazard_root_fourier_P1 omega roots) =
    lazard_root_fourier_P4 omega roots.
Proof.
apply: (@lazard_fourier_P4_formula_of_cleared_numerator
  F (lazard_depressed_of_roots roots) (lazard_root_invariants roots) v
  (lazard_root_fourier_P1 omega roots)
  (lazard_root_fourier_P4 omega roots)
  two_neq0 epsilon_neq0 p1_neq0).
rewrite epsilon_matches.
exact: (@lazard_root_fourier_P4_cleared_numerator F omega roots
  omega_primitive five_neq0 hsum).
Qed.

(** Direct root-origin specialization, using the same epsilon, T, and U
    that already satisfy Lazard's quadratic-stage relations. *)
Corollary lazard_root_fourier_P4_formula_root_triple omega
    (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (epsilon_neq0 : lazard_root_epsilon omega roots != 0)
    (p1_neq0 : lazard_root_fourier_P1 omega roots != 0) :
  lazard_fourier_P4_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      (Q.LazardQuadraticTriple
        (lazard_root_epsilon omega roots)
        (RR.lazard_root_T omega roots)
        (RR.lazard_root_formula_U omega roots))
      (lazard_root_fourier_P1 omega roots) =
    lazard_root_fourier_P4 omega roots.
Proof.
exact: (@lazard_root_fourier_P4_formula F omega roots
  (Q.LazardQuadraticTriple
    (lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots)
    (RR.lazard_root_formula_U omega roots))
  two_neq0 five_neq0 omega_primitive hsum erefl epsilon_neq0 p1_neq0).
Qed.

End RootFourierNumeratorP4.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP4.
