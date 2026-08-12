From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticVieta LazardQuinticRootProjections
  LazardQuinticRootFourierRelations LazardQuinticQuadratic
  LazardQuinticFourierNumerators LazardQuinticRootBranchEquivariance
  LazardQuinticRootFourierNumeratorRelations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Exact inverse-Fourier reconstruction from the three proved Lazard
    numerator formulas.  This yields equality with all five ordered roots,
    then all Vieta relations and an exact multiplicity-preserving
    factorization. *)
Module PolynomialFormulasLazardQuinticRootFormulaReconstruction.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticVieta.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticQuadratic.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRelations.
Local Open Scope ring_scope.

Section RootFormulaReconstruction.
Variable F : fieldType.

Definition lazard_formula_output_two_branches
    (omega : F) (roots : 5.-tuple F)
    (first second : lazard_sign_branch) (k : 'I_5) : F :=
  let v := lazard_branch_triple
    (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots) first)
    second in
  let source := BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second in
  lazard_inverse_fourier_output omega
    (source p0)
    (lazard_fourier_P2_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      v (source p0))
    (lazard_fourier_P3_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      v (source p0))
    (lazard_fourier_P4_formula
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots)
      v (source p0)) k.

Theorem lazard_formula_output_two_branches_eq_reversed_roots
    omega (roots : 5.-tuple F) first second
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : lazard_root_epsilon omega roots != 0)
    (E_neq0 : lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) != 0)
    (p1_neq0 :
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 != 0)
    (k : 'I_5) :
  lazard_formula_output_two_branches omega roots first second k =
    RFR.lazard_reversed_root_tuple
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second) k.
Proof.
have he0 : lazard_epsilon (BE.lazard_root_quadratic_triple omega roots) != 0.
  exact root_epsilon_neq0.
have he1 : lazard_epsilon
    (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
      first) != 0 := BE.lazard_branch_epsilon_neq0 first he0.
have he2 : lazard_epsilon
    (lazard_branch_triple
      (lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
        first) second) != 0 := BE.lazard_branch_epsilon_neq0 second he1.
have hc := @NR.lazard_root_fourier_formula_components_two_branches
  F omega roots first second two_neq0 five_neq0 omega_primitive hsum
  he2 E_neq0 p1_neq0.
move: hc=> /= hc.
case: hc=> hp2 hp3 hp4.
rewrite /lazard_formula_output_two_branches /= hp2 hp3 hp4.
rewrite -(@BE.lazard_root_fourier_orbit_roots_for_two_branches
    F omega roots first second p0)
  -(@BE.lazard_root_fourier_orbit_roots_for_two_branches
    F omega roots first second p1)
  -(@BE.lazard_root_fourier_orbit_roots_for_two_branches
    F omega roots first second p3)
  -(@BE.lazard_root_fourier_orbit_roots_for_two_branches
    F omega roots first second p2).
change
  (lazard_inverse_fourier_output omega
    (lazard_root_fourier_P1 omega
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second))
    (lazard_root_fourier_P2 omega
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second))
    (lazard_root_fourier_P3 omega
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second))
    (lazard_root_fourier_P4 omega
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second)) k = _).
have hsum_y : lazard_root_esymm1
    (BE.lazard_roots_for_branch
      (BE.lazard_roots_for_branch roots first) second) = 0.
  by rewrite BE.lazard_root_esymm1_roots_for_two_branches.
exact: (@RFR.lazard_inverse_fourier_root_fourier_coordinate
  F omega omega_primitive five_neq0
  (BE.lazard_roots_for_branch
    (BE.lazard_roots_for_branch roots first) second) k hsum_y).
Qed.

Theorem lazard_formula_output_two_branches_five_root_relations
    omega (roots : 5.-tuple F) first second
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : lazard_root_epsilon omega roots != 0)
    (E_neq0 : lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) != 0)
    (p1_neq0 :
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 != 0) :
  lazard_depressed_five_root_relations
    (lazard_root_p (lazard_depressed_of_roots roots))
    (lazard_root_q (lazard_depressed_of_roots roots))
    (lazard_root_r (lazard_depressed_of_roots roots))
    (lazard_root_s (lazard_depressed_of_roots roots))
    (lazard_formula_output_two_branches omega roots first second).
Proof.
pose y := BE.lazard_roots_for_branch
  (BE.lazard_roots_for_branch roots first) second.
have hsum_y : lazard_root_esymm1 y = 0.
  by rewrite /y BE.lazard_root_esymm1_roots_for_two_branches.
have hy := @RFR.lazard_reversed_root_relations F y hsum_y.
have hout : lazard_formula_output_two_branches omega roots first second =
    RFR.lazard_reversed_root_tuple y.
  apply/funext=> k.
  exact: (@lazard_formula_output_two_branches_eq_reversed_roots
    omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 p1_neq0 k).
rewrite hout.
move: hy.
by rewrite /y BE.lazard_depressed_of_roots_for_two_branches.
Qed.

Theorem lazard_formula_output_two_branches_eval_factorization
    omega (roots : 5.-tuple F) first second
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : lazard_root_epsilon omega roots != 0)
    (E_neq0 : lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) != 0)
    (p1_neq0 :
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 != 0)
    (z : F) :
  lazard_depressed_quintic_eval
      (lazard_root_p (lazard_depressed_of_roots roots))
      (lazard_root_q (lazard_depressed_of_roots roots))
      (lazard_root_r (lazard_depressed_of_roots roots))
      (lazard_root_s (lazard_depressed_of_roots roots)) z =
    (z - lazard_formula_output_two_branches omega roots first second o0) *
    (z - lazard_formula_output_two_branches omega roots first second o1) *
    (z - lazard_formula_output_two_branches omega roots first second o2) *
    (z - lazard_formula_output_two_branches omega roots first second o3) *
    (z - lazard_formula_output_two_branches omega roots first second o4).
Proof.
exact: (lazard_depressed_vieta_eval_factorization
  (@lazard_formula_output_two_branches_five_root_relations
    omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 p1_neq0) z).
Qed.

Corollary lazard_formula_output_two_branches_is_root
    omega (roots : 5.-tuple F) first second
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : lazard_root_epsilon omega roots != 0)
    (E_neq0 : lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) != 0)
    (p1_neq0 :
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 != 0)
    (k : 'I_5) :
  lazard_depressed_quintic_eval
      (lazard_root_p (lazard_depressed_of_roots roots))
      (lazard_root_q (lazard_depressed_of_roots roots))
      (lazard_root_r (lazard_depressed_of_roots roots))
      (lazard_root_s (lazard_depressed_of_roots roots))
      (lazard_formula_output_two_branches omega roots first second k) = 0.
Proof.
have hrel := @lazard_formula_output_two_branches_five_root_relations
  omega roots first second two_neq0 five_neq0 omega_primitive hsum
  root_epsilon_neq0 E_neq0 p1_neq0.
rewrite (lazard_depressed_vieta_eval_factorization hrel).
case: k=> [[|[|[|[|[|k]]]]] hk].
- have -> : @Ordinal 5 0 hk = o0 by apply: val_inj.
  by rewrite subrr !mul0r.
- have -> : @Ordinal 5 1 hk = o1 by apply: val_inj.
  by rewrite subrr !mulr0 !mul0r.
- have -> : @Ordinal 5 2 hk = o2 by apply: val_inj.
  by rewrite subrr !mulr0 !mul0r.
- have -> : @Ordinal 5 3 hk = o3 by apply: val_inj.
  by rewrite subrr !mulr0 !mul0r.
- have -> : @Ordinal 5 4 hk = o4 by apply: val_inj.
  by rewrite subrr !mulr0.
- by move: hk.
Qed.

End RootFormulaReconstruction.
End PolynomialFormulasLazardQuinticRootFormulaReconstruction.
