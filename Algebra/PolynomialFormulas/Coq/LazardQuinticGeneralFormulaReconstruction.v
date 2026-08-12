From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections LazardQuinticQuadratic
  LazardQuinticRootBranchEquivariance
  LazardQuinticRootFourierRelations
  LazardQuinticRootFormulaReconstruction
  LazardQuinticGeneralDepression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Translation of the proved depressed Lazard reconstruction back to a
    general quintic.  This is the coefficient-level composition missing
    from the original Coq chain: once the depressed coefficients agree with
    those of an ordered root tuple, the concrete P2/P3/P4 reconstruction
    gives an exact factorization and five roots of the original polynomial. *)
Module PolynomialFormulasLazardQuinticGeneralFormulaReconstruction.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticQuadratic.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module RF := PolynomialFormulasLazardQuinticRootFormulaReconstruction.
Module GD := PolynomialFormulasLazardQuinticGeneralDepression.
Local Open Scope ring_scope.

Section GeneralFormulaReconstruction.

Variable F : fieldType.

(** The concrete depressed output followed by the inverse Tschirnhaus
    translation [X = Y - b/(5a)]. *)
Definition lazard_general_formula_output_two_branches
    (c : GD.LazardGeneralQuinticCoefficients F)
    (omega : F) (roots : 5.-tuple F)
    (first second : lazard_sign_branch) (k : 'I_5) : F :=
  RF.lazard_formula_output_two_branches omega roots first second k -
    GD.lazard_depression_shift c.

(** The translated formula values are exactly the twice-reordered source
    roots, translated back to the original coordinate. *)
Theorem lazard_general_formula_output_eq_translated_reversed_roots
    (c : GD.LazardGeneralQuinticCoefficients F)
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
  lazard_general_formula_output_two_branches
      c omega roots first second k =
    RFR.lazard_reversed_root_tuple
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second) k -
      GD.lazard_depression_shift c.
Proof.
rewrite /lazard_general_formula_output_two_branches.
by rewrite (@RF.lazard_formula_output_two_branches_eq_reversed_roots
  F omega roots first second two_neq0 five_neq0 omega_primitive hsum
  root_epsilon_neq0 E_neq0 p1_neq0 k).
Qed.

(** The concrete formula gives a multiplicity-preserving factorization of
    the original general quintic. *)
Theorem lazard_general_formula_output_eval_factorization
    (c : GD.LazardGeneralQuinticCoefficients F)
    (ha : GD.lazard_general_a c != 0)
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
    (hcoeff : GD.lazard_depress_general c =
      lazard_depressed_of_roots roots)
    (x : F) :
  GD.lazard_general_quintic_eval c x =
    GD.lazard_general_a c *
      (x - lazard_general_formula_output_two_branches
        c omega roots first second o0) *
      (x - lazard_general_formula_output_two_branches
        c omega roots first second o1) *
      (x - lazard_general_formula_output_two_branches
        c omega roots first second o2) *
      (x - lazard_general_formula_output_two_branches
        c omega roots first second o3) *
      (x - lazard_general_formula_output_two_branches
        c omega roots first second o4).
Proof.
have hv := @RF.lazard_formula_output_two_branches_five_root_relations
  F omega roots first second two_neq0 five_neq0 omega_primitive hsum
  root_epsilon_neq0 E_neq0 p1_neq0.
have hv_general :
    PolynomialFormulasLazardQuinticVieta.
      lazard_depressed_five_root_relations
        (lazard_root_p (GD.lazard_depress_general c))
        (lazard_root_q (GD.lazard_depress_general c))
        (lazard_root_r (GD.lazard_depress_general c))
        (lazard_root_s (GD.lazard_depress_general c))
        (RF.lazard_formula_output_two_branches omega roots first second).
  rewrite hcoeff.
  exact: hv.
have hfactor := @GD.lazard_general_vieta_eval_factorization
  F c ha five_neq0
  (RF.lazard_formula_output_two_branches omega roots first second)
  hv_general x.
move: hfactor.
by rewrite /lazard_general_formula_output_two_branches.
Qed.

(** Every one of the five translated concrete outputs is a root of the
    original general quintic. *)
Corollary lazard_general_formula_output_is_root
    (c : GD.LazardGeneralQuinticCoefficients F)
    (ha : GD.lazard_general_a c != 0)
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
    (hcoeff : GD.lazard_depress_general c =
      lazard_depressed_of_roots roots)
    (k : 'I_5) :
  GD.lazard_general_quintic_eval c
    (lazard_general_formula_output_two_branches
      c omega roots first second k) = 0.
Proof.
have hv := @RF.lazard_formula_output_two_branches_five_root_relations
  F omega roots first second two_neq0 five_neq0 omega_primitive hsum
  root_epsilon_neq0 E_neq0 p1_neq0.
have hv_general :
    PolynomialFormulasLazardQuinticVieta.
      lazard_depressed_five_root_relations
        (lazard_root_p (GD.lazard_depress_general c))
        (lazard_root_q (GD.lazard_depress_general c))
        (lazard_root_r (GD.lazard_depress_general c))
        (lazard_root_s (GD.lazard_depress_general c))
        (RF.lazard_formula_output_two_branches omega roots first second).
  rewrite hcoeff.
  exact: hv.
exact: (@GD.lazard_general_vieta_output_root
  F c ha five_neq0
  (RF.lazard_formula_output_two_branches omega roots first second)
  hv_general k).
Qed.

(** Conversely, every root of the original nondegenerate quintic is one of
    the five translated concrete Lazard outputs.  This is the root-set form
    of the multiplicity-preserving factorization above. *)
Corollary lazard_general_root_is_formula_output
    (c : GD.LazardGeneralQuinticCoefficients F)
    (ha : GD.lazard_general_a c != 0)
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
    (hcoeff : GD.lazard_depress_general c =
      lazard_depressed_of_roots roots)
    (x : F) :
  GD.lazard_general_quintic_eval c x = 0 ->
  exists k : 'I_5,
    x = lazard_general_formula_output_two_branches
      c omega roots first second k.
Proof.
move=> hx.
have hfactor :=
  @lazard_general_formula_output_eval_factorization
    F c ha omega roots first second two_neq0 five_neq0 omega_primitive
    hsum root_epsilon_neq0 E_neq0 p1_neq0 hcoeff x.
rewrite !mulrA in hfactor.
have hproduct :
    (x - lazard_general_formula_output_two_branches
      c omega roots first second o0) *
    (x - lazard_general_formula_output_two_branches
      c omega roots first second o1) *
    (x - lazard_general_formula_output_two_branches
      c omega roots first second o2) *
    (x - lazard_general_formula_output_two_branches
      c omega roots first second o3) *
    (x - lazard_general_formula_output_two_branches
      c omega roots first second o4) = 0.
  apply: (mulfI ha).
  by rewrite mulr0 !mulrA -hfactor hx.
exact: (@GD.lazard_five_linear_factors_zero_exists F x
  (lazard_general_formula_output_two_branches
    c omega roots first second) hproduct).
Qed.

End GeneralFormulaReconstruction.

End PolynomialFormulasLazardQuinticGeneralFormulaReconstruction.
