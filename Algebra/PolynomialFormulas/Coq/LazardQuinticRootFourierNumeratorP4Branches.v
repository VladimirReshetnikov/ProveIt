From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections LazardQuinticQuadratic
  LazardQuinticFourierNumerators LazardQuinticRootBranchEquivariance
  LazardQuinticRootFourierNumeratorP4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The already checked P4 identity transported to every coherent root
    branch and to the two-branch composition used by reconstruction. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP4Branches.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticQuadratic.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module P4 := PolynomialFormulasLazardQuinticRootFourierNumeratorP4.
Local Open Scope ring_scope.

Section RootFourierNumeratorP4Branches.
Variable F : fieldType.

Theorem lazard_root_fourier_P4_cleared_numerator_branch
    omega (roots : 5.-tuple F) branch
    (omega_primitive : 5.-primitive_root omega)
    (five_neq0 : (5%:R : F) != 0)
    (hsum : lazard_root_esymm1 roots = 0) :
  let v := lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
    branch in
  let source := BE.lazard_source_for_branch
    (BE.lazard_root_fourier_orbit omega roots) branch in
  lazard_epsilon v * lazard_p41 (lazard_depressed_of_roots roots) +
    lazard_p42 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) =
  2%:R * lazard_epsilon v * source p0 * source p2.
Proof.
rewrite /=.
pose y := BE.lazard_roots_for_branch roots branch.
have hsum_y : lazard_root_esymm1 y = 0.
  by rewrite /y BE.lazard_root_esymm1_roots_for_branch.
have h := @P4.lazard_root_fourier_P4_cleared_numerator F omega y
  omega_primitive five_neq0 hsum_y.
change
  (lazard_epsilon (BE.lazard_root_quadratic_triple omega y) *
      lazard_p41 (lazard_depressed_of_roots y) +
    lazard_p42 (lazard_depressed_of_roots y)
      (lazard_root_invariants y) =
   2%:R * lazard_epsilon (BE.lazard_root_quadratic_triple omega y) *
      BE.lazard_root_fourier_orbit omega y p0 *
      BE.lazard_root_fourier_orbit omega y p2) at h.
rewrite /y BE.lazard_depressed_of_roots_for_branch
  BE.lazard_root_invariants_roots_for_branch
  BE.lazard_root_quadratic_triple_roots_for_branch
  !BE.lazard_root_fourier_orbit_roots_for_branch in h.
exact h.
Qed.

Theorem lazard_root_fourier_P4_cleared_numerator_two_branches
    omega (roots : 5.-tuple F) first second
    (omega_primitive : 5.-primitive_root omega)
    (five_neq0 : (5%:R : F) != 0)
    (hsum : lazard_root_esymm1 roots = 0) :
  let v := lazard_branch_triple
    (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots) first)
    second in
  let source := BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second in
  lazard_epsilon v * lazard_p41 (lazard_depressed_of_roots roots) +
    lazard_p42 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) =
  2%:R * lazard_epsilon v * source p0 * source p2.
Proof.
rewrite /=.
pose y := BE.lazard_roots_for_branch roots first.
have hsum_y : lazard_root_esymm1 y = 0.
  by rewrite /y BE.lazard_root_esymm1_roots_for_branch.
have h := @lazard_root_fourier_P4_cleared_numerator_branch
  omega y second omega_primitive five_neq0 hsum_y.
move: h; rewrite /y BE.lazard_depressed_of_roots_for_branch
  BE.lazard_root_invariants_roots_for_branch
  BE.lazard_root_quadratic_triple_roots_for_branch
  !BE.lazard_root_fourier_orbit_roots_for_branch.
by [].
Qed.

Theorem lazard_root_fourier_P4_formula_two_branches
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
  lazard_fourier_P4_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      v (source p0) = source p2.
Proof.
rewrite /=.
apply: (@P4.lazard_fourier_P4_formula_of_cleared_numerator F
  (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
  (lazard_branch_triple
    (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots) first)
    second)
  (BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second p0)
  (BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second p2)
  two_neq0 epsilon_neq0 p1_neq0).
exact: (@lazard_root_fourier_P4_cleared_numerator_two_branches
  omega roots first second omega_primitive five_neq0 hsum).
Qed.

End RootFourierNumeratorP4Branches.
End PolynomialFormulasLazardQuinticRootFourierNumeratorP4Branches.
