From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticVieta LazardQuinticQuadratic
  LazardQuinticFourierNumerators LazardQuinticRootProjections
  LazardQuinticRootBranchEquivariance LazardQuinticRootFourierRelations
  LazardQuinticRootFormulaReconstruction
  LazardQuinticRootFourierNonzero
  LazardQuinticGeneralDepression LazardQuinticGeneralFormulaReconstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root reconstruction with the nonzero Fourier branch selected
    internally.  Earlier public reconstruction theorems accepted a
    particular nonzero [P1] branch as a premise.  Here injectivity and the
    depressed relation prove that such a branch exists, so the aggregate
    theorem no longer exposes that certificate. *)
Module PolynomialFormulasLazardQuinticRootBranchSelectionReconstruction.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module V := PolynomialFormulasLazardQuinticVieta.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module RF := PolynomialFormulasLazardQuinticRootFormulaReconstruction.
Module FNZ := PolynomialFormulasLazardQuinticRootFourierNonzero.
Module GD := PolynomialFormulasLazardQuinticGeneralDepression.
Module GF := PolynomialFormulasLazardQuinticGeneralFormulaReconstruction.

Local Open Scope ring_scope.

Section SelectedReconstruction.

Variable F : fieldType.

(** The two coherent branches, their exact root identification, and all
    five Vieta relations are obtained without a supplied [P1 != 0]. *)
Theorem lazard_exists_root_formula_reconstruction
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots) != 0) :
  exists first second : Q.lazard_sign_branch,
    (forall k : 'I_5,
      RF.lazard_formula_output_two_branches omega roots first second k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch roots first) second) k) /\
    V.lazard_depressed_five_root_relations
      (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
      (RF.lazard_formula_output_two_branches omega roots first second).
Proof.
have [first [second hp1]] :=
  FNZ.lazard_exists_two_branches_with_nonzero_P1
    omega_primitive five_neq0 hroots hsum.
exists first, second; split.
- move=> k.
  exact: (@RF.lazard_formula_output_two_branches_eq_reversed_roots
    F omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 hp1 k).
- exact: (@RF.lazard_formula_output_two_branches_five_root_relations
    F omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 hp1).
Qed.

(** Multiplicity-preserving factorization and root soundness, still with no
    branch/nonzero-[P1] premise. *)
Theorem lazard_exists_root_formula_factorization
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots) != 0) :
  exists first second : Q.lazard_sign_branch,
    (forall z : F,
      V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
      (z - RF.lazard_formula_output_two_branches
        omega roots first second o0) *
      (z - RF.lazard_formula_output_two_branches
        omega roots first second o1) *
      (z - RF.lazard_formula_output_two_branches
        omega roots first second o2) *
      (z - RF.lazard_formula_output_two_branches
        omega roots first second o3) *
      (z - RF.lazard_formula_output_two_branches
        omega roots first second o4)) /\
    (forall k : 'I_5,
      V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
        (RF.lazard_formula_output_two_branches
          omega roots first second k) = 0).
Proof.
have [first [second hp1]] :=
  FNZ.lazard_exists_two_branches_with_nonzero_P1
    omega_primitive five_neq0 hroots hsum.
exists first, second; split.
- move=> z.
  exact: (@RF.lazard_formula_output_two_branches_eval_factorization
    F omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 hp1 z).
- move=> k.
  exact: (@RF.lazard_formula_output_two_branches_is_root
    F omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 hp1 k).
Qed.

(** General-quintic aggregate: exact factorization, soundness, and
    completeness after translation, with both branch choices internal. *)
Theorem lazard_exists_general_formula_complete
    (c : GD.LazardGeneralQuinticCoefficients F)
    (ha : GD.lazard_general_a c != 0)
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots) != 0)
    (hcoeff : GD.lazard_depress_general c =
      RP.lazard_depressed_of_roots roots) :
  exists first second : Q.lazard_sign_branch,
    (forall x : F,
      GD.lazard_general_quintic_eval c x =
      GD.lazard_general_a c *
        (x - GF.lazard_general_formula_output_two_branches
          c omega roots first second o0) *
        (x - GF.lazard_general_formula_output_two_branches
          c omega roots first second o1) *
        (x - GF.lazard_general_formula_output_two_branches
          c omega roots first second o2) *
        (x - GF.lazard_general_formula_output_two_branches
          c omega roots first second o3) *
        (x - GF.lazard_general_formula_output_two_branches
          c omega roots first second o4)) /\
    (forall k : 'I_5,
      GD.lazard_general_quintic_eval c
        (GF.lazard_general_formula_output_two_branches
          c omega roots first second k) = 0) /\
    (forall x : F, GD.lazard_general_quintic_eval c x = 0 ->
      exists k : 'I_5,
        x = GF.lazard_general_formula_output_two_branches
          c omega roots first second k).
Proof.
have [first [second hp1]] :=
  FNZ.lazard_exists_two_branches_with_nonzero_P1
    omega_primitive five_neq0 hroots hsum.
exists first, second; split.
- move=> x.
  exact: (@GF.lazard_general_formula_output_eval_factorization
    F c ha omega roots first second two_neq0 five_neq0 omega_primitive
    hsum root_epsilon_neq0 E_neq0 hp1 hcoeff x).
- split.
  + move=> k.
    exact: (@GF.lazard_general_formula_output_is_root
      F c ha omega roots first second two_neq0 five_neq0 omega_primitive
      hsum root_epsilon_neq0 E_neq0 hp1 hcoeff k).
  + move=> x hx.
    exact: (@GF.lazard_general_root_is_formula_output
      F c ha omega roots first second two_neq0 five_neq0 omega_primitive
      hsum root_epsilon_neq0 E_neq0 hp1 hcoeff x hx).
Qed.

End SelectedReconstruction.

End PolynomialFormulasLazardQuinticRootBranchSelectionReconstruction.
