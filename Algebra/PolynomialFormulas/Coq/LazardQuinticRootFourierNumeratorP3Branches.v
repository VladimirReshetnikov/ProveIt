From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections LazardQuinticQuadratic
  LazardQuinticFourierNumerators LazardQuinticRootBranchEquivariance
  LazardQuinticRootFourierNumeratorP3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** P3 numerator and division formulas on every coherent root branch. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3Branches.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticQuadratic.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module P3 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3.
Local Open Scope ring_scope.

Section RootFourierNumeratorP3Branches.
Variable F : fieldType.

Theorem lazard_root_fourier_P3_cleared_numerator_branch
    omega (roots : 5.-tuple F) branch
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  let v := lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
    branch in
  let source := BE.lazard_source_for_branch
    (BE.lazard_root_fourier_orbit omega roots) branch in
  5%:R * lazard_epsilon v *
        lazard_invariant_E (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) *
        lazard_p31 (lazard_depressed_of_roots roots) +
      5%:R * lazard_invariant_E (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) *
        lazard_p32 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) +
      2%:R * lazard_epsilon v *
        (lazard_p33 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) * lazard_t v +
         lazard_p34 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) * lazard_u v) =
    20%:R * lazard_epsilon v *
      lazard_invariant_E (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots) * source p0 ^+ 2 * source p3.
Proof.
rewrite /=.
pose y := BE.lazard_roots_for_branch roots branch.
have hsum_y : lazard_root_esymm1 y = 0.
  by rewrite /y BE.lazard_root_esymm1_roots_for_branch.
have h := @P3.lazard_root_fourier_P3_cleared_numerator F omega y
  omega_primitive hsum_y.
change
  (5%:R * lazard_epsilon (BE.lazard_root_quadratic_triple omega y) *
        lazard_invariant_E (lazard_depressed_of_roots y)
          (lazard_root_invariants y) *
        lazard_p31 (lazard_depressed_of_roots y) +
      5%:R * lazard_invariant_E (lazard_depressed_of_roots y)
          (lazard_root_invariants y) *
        lazard_p32 (lazard_depressed_of_roots y)
          (lazard_root_invariants y) +
      2%:R * lazard_epsilon (BE.lazard_root_quadratic_triple omega y) *
        (lazard_p33 (lazard_depressed_of_roots y)
            (lazard_root_invariants y) *
              lazard_t (BE.lazard_root_quadratic_triple omega y) +
         lazard_p34 (lazard_depressed_of_roots y)
            (lazard_root_invariants y) *
              lazard_u (BE.lazard_root_quadratic_triple omega y)) =
    20%:R * lazard_epsilon (BE.lazard_root_quadratic_triple omega y) *
      lazard_invariant_E (lazard_depressed_of_roots y)
        (lazard_root_invariants y) *
      BE.lazard_root_fourier_orbit omega y p0 ^+ 2 *
      BE.lazard_root_fourier_orbit omega y p3) at h.
rewrite /y BE.lazard_depressed_of_roots_for_branch
  BE.lazard_root_invariants_roots_for_branch
  BE.lazard_root_quadratic_triple_roots_for_branch
  !BE.lazard_root_fourier_orbit_roots_for_branch in h.
exact h.
Qed.

Theorem lazard_root_fourier_P3_cleared_numerator_two_branches
    omega (roots : 5.-tuple F) first second
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  let v := lazard_branch_triple
    (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots) first)
    second in
  let source := BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second in
  5%:R * lazard_epsilon v *
        lazard_invariant_E (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) *
        lazard_p31 (lazard_depressed_of_roots roots) +
      5%:R * lazard_invariant_E (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) *
        lazard_p32 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots) +
      2%:R * lazard_epsilon v *
        (lazard_p33 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) * lazard_t v +
         lazard_p34 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots) * lazard_u v) =
    20%:R * lazard_epsilon v *
      lazard_invariant_E (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots) * source p0 ^+ 2 * source p3.
Proof.
rewrite /=.
pose y := BE.lazard_roots_for_branch roots first.
have hsum_y : lazard_root_esymm1 y = 0.
  by rewrite /y BE.lazard_root_esymm1_roots_for_branch.
have h := @lazard_root_fourier_P3_cleared_numerator_branch
  omega y second omega_primitive hsum_y.
move: h; rewrite /y BE.lazard_depressed_of_roots_for_branch
  BE.lazard_root_invariants_roots_for_branch
  BE.lazard_root_quadratic_triple_roots_for_branch
  !BE.lazard_root_fourier_orbit_roots_for_branch.
by [].
Qed.

Theorem lazard_root_fourier_P3_formula_two_branches
    omega (roots : 5.-tuple F) first second
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (epsilon_neq0 :
      lazard_epsilon
        (lazard_branch_triple
          (lazard_branch_triple
            (BE.lazard_root_quadratic_triple omega roots) first) second) != 0)
    (E_neq0 : lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) != 0)
    (p1_neq0 :
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 != 0) :
  let v := lazard_branch_triple
    (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots) first)
    second in
  let source := BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second in
  lazard_fourier_P3_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      v (source p0) = source p3.
Proof.
rewrite /=.
apply: (@P3.lazard_fourier_P3_formula_of_cleared_numerator F
  (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
  (lazard_branch_triple
    (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots) first)
    second)
  (BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second p0)
  (BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second p3)
  two_neq0 five_neq0 epsilon_neq0 E_neq0 p1_neq0).
exact: (@lazard_root_fourier_P3_cleared_numerator_two_branches
  omega roots first second omega_primitive hsum).
Qed.

End RootFourierNumeratorP3Branches.
End PolynomialFormulasLazardQuinticRootFourierNumeratorP3Branches.
