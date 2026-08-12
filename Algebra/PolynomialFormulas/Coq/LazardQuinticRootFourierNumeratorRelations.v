From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections LazardQuinticQuadratic
  LazardQuinticFourierNumerators LazardQuinticRootBranchEquivariance
  LazardQuinticRootFourierNumeratorP2Branches
  LazardQuinticRootFourierNumeratorP3Branches
  LazardQuinticRootFourierNumeratorP4Branches.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Assembly of the three independently derived Fourier numerator
    identities on a coherent two-branch root orbit. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorRelations.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticQuadratic.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module P2B := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Branches.
Module P3B := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Branches.
Module P4B := PolynomialFormulasLazardQuinticRootFourierNumeratorP4Branches.
Local Open Scope ring_scope.

Section RootFourierNumeratorRelations.
Variable F : fieldType.

Record lazard_fourier_numerator_relations
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (v : lazard_quadratic_triple F) (p1 p2 p3 p4 : F) : Prop :=
    LazardFourierNumeratorRelations {
  lazard_numerator_relation_P4 :
    lazard_epsilon v * lazard_p41 c + lazard_p42 c i =
      2%:R * lazard_epsilon v * p1 * p4;
  lazard_numerator_relation_P3 :
    5%:R * lazard_epsilon v * lazard_invariant_E c i * lazard_p31 c +
        5%:R * lazard_invariant_E c i * lazard_p32 c i +
        2%:R * lazard_epsilon v *
          (lazard_p33 c i * lazard_t v + lazard_p34 c i * lazard_u v) =
      20%:R * lazard_epsilon v * lazard_invariant_E c i *
        p1 ^+ 2 * p3;
  lazard_numerator_relation_P2 :
    5%:R * lazard_epsilon v * lazard_invariant_E c i * lazard_p21 c i +
        5%:R * lazard_invariant_E c i * lazard_p22 c i +
        2%:R * lazard_epsilon v *
          (lazard_p23 c i * lazard_t v + lazard_p24 c i * lazard_u v) =
      20%:R * lazard_epsilon v * lazard_invariant_E c i *
        p1 ^+ 3 * p2
}.

Theorem lazard_root_fourier_numerator_relations_two_branches
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
  lazard_fourier_numerator_relations
    (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
    v (source p0) (source p1) (source p3) (source p2).
Proof.
rewrite /=.
constructor.
- exact: (@P4B.lazard_root_fourier_P4_cleared_numerator_two_branches
    F omega roots first second omega_primitive five_neq0 hsum).
- exact: (@P3B.lazard_root_fourier_P3_cleared_numerator_two_branches
    F omega roots first second omega_primitive hsum).
- exact: (@P2B.lazard_root_fourier_P2_cleared_numerator_two_branches
    F omega roots first second omega_primitive hsum).
Qed.

Record lazard_fourier_formula_components
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (v : lazard_quadratic_triple F) (p1 p2 p3 p4 : F) : Prop :=
    LazardFourierFormulaComponents {
  lazard_formula_component_P2 : lazard_fourier_P2_formula c i v p1 = p2;
  lazard_formula_component_P3 : lazard_fourier_P3_formula c i v p1 = p3;
  lazard_formula_component_P4 : lazard_fourier_P4_formula c i v p1 = p4
}.

Theorem lazard_root_fourier_formula_components_two_branches
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
  lazard_fourier_formula_components
    (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
    v (source p0) (source p1) (source p3) (source p2).
Proof.
rewrite /=.
constructor.
- exact: (@P2B.lazard_root_fourier_P2_formula_two_branches F omega roots
    first second two_neq0 five_neq0 omega_primitive hsum
    epsilon_neq0 E_neq0 p1_neq0).
- exact: (@P3B.lazard_root_fourier_P3_formula_two_branches F omega roots
    first second two_neq0 five_neq0 omega_primitive hsum
    epsilon_neq0 E_neq0 p1_neq0).
- exact: (@P4B.lazard_root_fourier_P4_formula_two_branches F omega roots
    first second two_neq0 five_neq0 omega_primitive hsum
    epsilon_neq0 p1_neq0).
Qed.

End RootFourierNumeratorRelations.
End PolynomialFormulasLazardQuinticRootFourierNumeratorRelations.
