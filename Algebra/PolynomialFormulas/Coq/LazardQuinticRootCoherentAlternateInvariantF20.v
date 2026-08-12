From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues LazardQuinticFourier
  LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticRootBranchEquivariance
  LazardQuinticRootAlternateRecovery
  LazardQuinticRootCoherentAlternateEquivariance
  LazardQuinticRootInvariantENonzeroF20
  LazardQuinticRootMembershipDescent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Full [F20]-invariance of the convention-safe alternate projection.

    The earlier branch theorem covers the powers of multiplication by two.
    This file supplies the missing five-cycle calculation and then invokes
    the certified decomposition

      [standard_F20 = <five_cycle> <*> <multiplier_two>].

    Thus the corrected fourth projection is an actual metacyclic invariant
    value, rather than merely a quantity stable under four selected tuples. *)
Module PolynomialFormulasLazardQuinticRootCoherentAlternateInvariantF20.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module TV := PolynomialFormulasQuinticThetaValues.
Module LF := PolynomialFormulasLazardQuinticFourier.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RA := PolynomialFormulasLazardQuinticRootAlternateRecovery.
Module CE :=
  PolynomialFormulasLazardQuinticRootCoherentAlternateEquivariance.
Module ENZ := PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.
Module C := PolynomialFormulasLazardQuinticCoherentAlternateProjection.
Module CB :=
  PolynomialFormulasLazardQuinticCoherentAlternateProjectionBridge.
Module MD := PolynomialFormulasLazardQuinticRootMembershipDescent.

Section Invariance.

Variable F : fieldType.
Variable omega : F.
Hypothesis omega_primitive : 5.-primitive_root omega.

(** Scalar-extension identities for the omega-dependent root expressions. *)
Lemma lazard_fifth_root_A_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) :
  h (RR.lazard_fifth_root_A z) = RR.lazard_fifth_root_A (h z).
Proof. by rewrite /RR.lazard_fifth_root_A rmorphB rmorphXn. Qed.

Lemma lazard_fifth_root_B_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) :
  h (RR.lazard_fifth_root_B z) = RR.lazard_fifth_root_B (h z).
Proof. by rewrite /RR.lazard_fifth_root_B rmorphB !rmorphXn. Qed.

Lemma lazard_fifth_root_discriminant_factor_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) :
  h (RR.lazard_fifth_root_discriminant_factor z) =
    RR.lazard_fifth_root_discriminant_factor (h z).
Proof.
by rewrite /RR.lazard_fifth_root_discriminant_factor
  !rmorphD !rmorphB !rmorphXn.
Qed.

Lemma lazard_root_epsilon_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) :
  h (RR.lazard_root_epsilon z roots) =
    RR.lazard_root_epsilon (h z) (map_tuple h roots).
Proof.
by rewrite /RR.lazard_root_epsilon rmorphM
  lazard_fifth_root_discriminant_factor_map
  MD.lazard_epsilon_product_map.
Qed.

Lemma lazard_root_T_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) :
  h (RR.lazard_root_T z roots) =
    RR.lazard_root_T (h z) (map_tuple h roots).
Proof.
by rewrite /RR.lazard_root_T rmorphD !rmorphM
  lazard_fifth_root_A_map lazard_fifth_root_B_map
  ENZ.lazard_root_T_prime_map ENZ.lazard_root_U_prime_map.
Qed.

Lemma lazard_root_formula_U_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) :
  h (RR.lazard_root_formula_U z roots) =
    RR.lazard_root_formula_U (h z) (map_tuple h roots).
Proof.
by rewrite /RR.lazard_root_formula_U /RR.lazard_root_printed_U
  rmorphN rmorphB !rmorphM
  lazard_fifth_root_A_map lazard_fifth_root_B_map
  ENZ.lazard_root_T_prime_map ENZ.lazard_root_U_prime_map.
Qed.

Lemma lazard_root_fourier_P1_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) :
  h (RP.lazard_root_fourier_P1 z roots) =
    RP.lazard_root_fourier_P1 (h z) (map_tuple h roots).
Proof.
by rewrite /RP.lazard_root_fourier_P1
  !rmorphD !rmorphM !rmorphXn !tnth_map.
Qed.

Lemma lazard_root_fourier_P2_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) :
  h (RP.lazard_root_fourier_P2 z roots) =
    RP.lazard_root_fourier_P2 (h z) (map_tuple h roots).
Proof.
by rewrite /RP.lazard_root_fourier_P2
  !rmorphD !rmorphM !rmorphXn !tnth_map.
Qed.

Lemma lazard_root_fourier_P3_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) :
  h (RP.lazard_root_fourier_P3 z roots) =
    RP.lazard_root_fourier_P3 (h z) (map_tuple h roots).
Proof.
by rewrite /RP.lazard_root_fourier_P3
  !rmorphD !rmorphM !rmorphXn !tnth_map.
Qed.

Lemma lazard_root_fourier_P4_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) :
  h (RP.lazard_root_fourier_P4 z roots) =
    RP.lazard_root_fourier_P4 (h z) (map_tuple h roots).
Proof.
by rewrite /RP.lazard_root_fourier_P4
  !rmorphD !rmorphM !rmorphXn !tnth_map.
Qed.

Lemma lazard_root_fourier_fifth_orbit_map (E : fieldType)
    (h : {rmorphism F -> E}) (z : F) (roots : 5.-tuple F) (i : 'I_4) :
  h (RP.lazard_root_fourier_fifth_orbit z roots i) =
    RP.lazard_root_fourier_fifth_orbit (h z) (map_tuple h roots) i.
Proof.
case: i=> [[|[|[|[|i]]]] hi] //=;
by rewrite /RP.lazard_root_fourier_fifth_orbit rmorphXn
  lazard_root_fourier_P1_map lazard_root_fourier_P2_map
  lazard_root_fourier_P3_map lazard_root_fourier_P4_map.
Qed.

(** The complete corrected projection value commutes with scalar extension. *)
Lemma lazard_root_coherent_alternate_projection_values_map
    (E : fieldType) (h : {rmorphism F -> E})
    (z : F) (roots : 5.-tuple F) (i : 'I_4) :
  h (RA.lazard_root_coherent_alternate_projection_values z roots i) =
    RA.lazard_root_coherent_alternate_projection_values
      (h z) (map_tuple h roots) i.
Proof.
rewrite /RA.lazard_root_coherent_alternate_projection_values
  C.lazard_coherent_alternate_projections_map
  lazard_root_epsilon_map lazard_root_T_map lazard_root_formula_U_map.
rewrite /C.lazard_coherent_alternate_projections.
apply: eq_bigr=> j _.
by rewrite lazard_root_fourier_fifth_orbit_map.
Qed.

(** Every automorphism sends a primitive fifth root to one of its four
    primitive powers.  This is derived from [prim_rootP], rather than added
    as a descent certificate. *)
Lemma primitive_fifth_rmorphism_image_cases
    (h : {rmorphism F -> F}) :
  h omega = omega \/ h omega = omega ^+ 2 \/
  h omega = omega ^+ 3 \/ h omega = omega ^+ 4.
Proof.
have himage_power : (h omega) ^+ 5 = 1.
  by rewrite -rmorphXn (prim_expr_order omega_primitive) rmorph1.
have [j hj] := prim_rootP omega_primitive himage_power.
have himage_primitive : 5.-primitive_root (h omega).
  by rewrite fmorph_primitive_root.
case: j hj=> [[|[|[|[|[|j]]]]] hjlt] //= hj.
- have hbad : (5 %| 1)%N.
    by rewrite (prim_order_dvd himage_primitive) hj expr0.
  by move: hbad.
- left. by rewrite hj expr1.
- by right; left.
- by right; right; left.
- by right; right; right.
Qed.

(** The two libraries use definitionally identical tuples for the cyclic
    substitution. *)
Lemma permute_five_cycle_is_cyclic_shift (roots : 5.-tuple F) :
  TV.permute_quintic_roots five_cycle roots =
    LF.lazard_cyclic_shift roots.
Proof. by []. Qed.

(** Multiplication by two is the explicit [rotate] branch. *)
Lemma permute_multiplier_two_is_rotate_branch (roots : 5.-tuple F) :
  TV.permute_quintic_roots multiplier_two roots =
    BE.lazard_roots_for_branch roots Q.LazardBranchRotate.
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|[|i]]]]] hi] //=;
by rewrite TV.tnth_permute_quintic_roots
  multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
  multiplier_two_o3 multiplier_two_o4.
Qed.

Lemma lazard_root_epsilon_five_cycle (roots : 5.-tuple F) :
  RR.lazard_root_epsilon omega
      (TV.permute_quintic_roots five_cycle roots) =
    RR.lazard_root_epsilon omega roots.
Proof.
by rewrite /RR.lazard_root_epsilon
  MD.lazard_epsilon_product_five_cycle.
Qed.

Lemma lazard_root_T_five_cycle (roots : 5.-tuple F) :
  RR.lazard_root_T omega
      (TV.permute_quintic_roots five_cycle roots) =
    RR.lazard_root_T omega roots.
Proof.
by rewrite /RR.lazard_root_T
  ENZ.lazard_root_T_prime_five_cycle
  ENZ.lazard_root_U_prime_five_cycle.
Qed.

Lemma lazard_root_formula_U_five_cycle (roots : 5.-tuple F) :
  RR.lazard_root_formula_U omega
      (TV.permute_quintic_roots five_cycle roots) =
    RR.lazard_root_formula_U omega roots.
Proof.
by rewrite /RR.lazard_root_formula_U /RR.lazard_root_printed_U
  ENZ.lazard_root_T_prime_five_cycle
  ENZ.lazard_root_U_prime_five_cycle.
Qed.

(** Raising a Fourier eigenvector to the fifth power kills its five-cycle
    character. *)
Lemma lazard_root_fourier_fifth_orbit_five_cycle
    (roots : 5.-tuple F) (i : 'I_4) :
  RP.lazard_root_fourier_fifth_orbit omega
      (TV.permute_quintic_roots five_cycle roots) i =
    RP.lazard_root_fourier_fifth_orbit omega roots i.
Proof.
case: i=> [[|[|[|[|i]]]] hi] //=.
- rewrite /RP.lazard_root_fourier_fifth_orbit !RP.lazard_root_fourier_P1E.
  rewrite permute_five_cycle_is_cyclic_shift
    (LF.lazard_fourier_sum_cyclic_shift omega_primitive).
  by rewrite exprMn exprAC (prim_expr_order omega_primitive) expr1n mul1r.
- rewrite /RP.lazard_root_fourier_fifth_orbit
    !RP.lazard_root_fourier_P2E //.
  rewrite permute_five_cycle_is_cyclic_shift
    (LF.lazard_fourier_sum_cyclic_shift omega_primitive).
  by rewrite exprMn exprAC (prim_expr_order omega_primitive) expr1n mul1r.
- rewrite /RP.lazard_root_fourier_fifth_orbit
    !RP.lazard_root_fourier_P4E //.
  rewrite permute_five_cycle_is_cyclic_shift
    (LF.lazard_fourier_sum_cyclic_shift omega_primitive).
  by rewrite exprMn exprAC (prim_expr_order omega_primitive) expr1n mul1r.
- rewrite /RP.lazard_root_fourier_fifth_orbit
    !RP.lazard_root_fourier_P3E //.
  rewrite permute_five_cycle_is_cyclic_shift
    (LF.lazard_fourier_sum_cyclic_shift omega_primitive).
  by rewrite exprMn exprAC (prim_expr_order omega_primitive) expr1n mul1r.
Qed.

Lemma lazard_root_coherent_alternate_projection_values_five_cycle
    (roots : 5.-tuple F) (i : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values omega
      (TV.permute_quintic_roots five_cycle roots) i =
    RA.lazard_root_coherent_alternate_projection_values omega roots i.
Proof.
by rewrite /RA.lazard_root_coherent_alternate_projection_values
  lazard_root_epsilon_five_cycle lazard_root_T_five_cycle
  lazard_root_formula_U_five_cycle
  lazard_root_fourier_fifth_orbit_five_cycle.
Qed.

Lemma lazard_root_coherent_alternate_projection_values_multiplier_two
    (roots : 5.-tuple F) (i : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values omega
      (TV.permute_quintic_roots multiplier_two roots) i =
    RA.lazard_root_coherent_alternate_projection_values omega roots i.
Proof.
rewrite permute_multiplier_two_is_rotate_branch.
exact: CE.lazard_root_coherent_alternate_projection_values_roots_for_branch.
Qed.

(** The other symmetry needed for coefficient-field descent is the change
    of primitive fifth-root generator [omega -> omega^2]. *)
Lemma lazard_fifth_root_A_squared :
  RR.lazard_fifth_root_A (omega ^+ 2) =
    RR.lazard_fifth_root_B omega.
Proof.
rewrite /RR.lazard_fifth_root_A /RR.lazard_fifth_root_B
  -(@exprM F omega 2 4)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_fifth_root_B_squared :
  RR.lazard_fifth_root_B (omega ^+ 2) =
    - RR.lazard_fifth_root_A omega.
Proof.
rewrite /RR.lazard_fifth_root_A /RR.lazard_fifth_root_B
  -(@exprM F omega 2 2) -(@exprM F omega 2 3)
  (RP.lazard_primitive_fifth_power6 omega_primitive).
by rewrite opprB.
Qed.

Lemma lazard_fifth_root_discriminant_factor_squared :
  RR.lazard_fifth_root_discriminant_factor (omega ^+ 2) =
    - RR.lazard_fifth_root_discriminant_factor omega.
Proof.
rewrite /RR.lazard_fifth_root_discriminant_factor
  -(@exprM F omega 2 4) -(@exprM F omega 2 2)
  -(@exprM F omega 2 3)
  (RP.lazard_primitive_fifth_power8 omega_primitive)
  (RP.lazard_primitive_fifth_power6 omega_primitive).
RR.finish_lazard_ring.
Qed.

Lemma lazard_root_epsilon_squared (roots : 5.-tuple F) :
  RR.lazard_root_epsilon (omega ^+ 2) roots =
    - RR.lazard_root_epsilon omega roots.
Proof.
rewrite /RR.lazard_root_epsilon
  lazard_fifth_root_discriminant_factor_squared.
RR.finish_lazard_ring.
Qed.

Lemma lazard_root_T_squared (roots : 5.-tuple F) :
  RR.lazard_root_T (omega ^+ 2) roots =
    - RR.lazard_root_formula_U omega roots.
Proof.
rewrite /RR.lazard_root_T /RR.lazard_root_formula_U
  /RR.lazard_root_printed_U
  lazard_fifth_root_A_squared lazard_fifth_root_B_squared.
RR.finish_lazard_ring.
Qed.

Lemma lazard_root_formula_U_squared (roots : 5.-tuple F) :
  RR.lazard_root_formula_U (omega ^+ 2) roots =
    RR.lazard_root_T omega roots.
Proof.
rewrite /RR.lazard_root_T /RR.lazard_root_formula_U
  /RR.lazard_root_printed_U
  lazard_fifth_root_A_squared lazard_fifth_root_B_squared.
RR.finish_lazard_ring.
Qed.

Lemma lazard_root_quadratic_triple_squared (roots : 5.-tuple F) :
  BE.lazard_root_quadratic_triple (omega ^+ 2) roots =
    Q.lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
      Q.LazardBranchRotateNegate.
Proof.
apply: BE.lazard_quadratic_triple_ext.
- exact: lazard_root_epsilon_squared.
- exact: lazard_root_T_squared.
- exact: lazard_root_formula_U_squared.
Qed.

Lemma lazard_root_fourier_P1_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P1 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P2 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P1 /RP.lazard_root_fourier_P2
  -(@exprM F omega 2 2) -(@exprM F omega 2 3)
  -(@exprM F omega 2 4)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_root_fourier_P2_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P2 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P4 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P2 /RP.lazard_root_fourier_P4
  -(@exprM F omega 2 2) -(@exprM F omega 2 4)
  -(@exprM F omega 2 3)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_root_fourier_P4_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P4 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P3 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P4 /RP.lazard_root_fourier_P3
  -(@exprM F omega 2 4) -(@exprM F omega 2 3)
  -(@exprM F omega 2 2)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_root_fourier_P3_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P3 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P1 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P3 /RP.lazard_root_fourier_P1
  -(@exprM F omega 2 3) -(@exprM F omega 2 4)
  -(@exprM F omega 2 2)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_root_fourier_fifth_orbit_squared
    (roots : 5.-tuple F) (i : 'I_4) :
  RP.lazard_root_fourier_fifth_orbit (omega ^+ 2) roots i =
    CB.lazard_coherent_source_for_branch
      (RP.lazard_root_fourier_fifth_orbit omega roots)
      Q.LazardBranchRotateNegate i.
Proof.
case: i=> [[|[|[|[|i]]]] hi] //=;
by rewrite /RP.lazard_root_fourier_fifth_orbit
  /CB.lazard_coherent_source_for_branch
  /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_rotate_negate_source
  lazard_root_fourier_P1_squared lazard_root_fourier_P2_squared
  lazard_root_fourier_P3_squared lazard_root_fourier_P4_squared.
Qed.

(** The corrected projection is independent of the cyclic Galois-generator
    change [omega -> omega^2]. *)
Theorem lazard_root_coherent_alternate_projection_values_squared
    (roots : 5.-tuple F) (i : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values (omega ^+ 2) roots i =
    RA.lazard_root_coherent_alternate_projection_values omega roots i.
Proof.
change
  C.lazard_coherent_alternate_projections
    (Q.lazard_epsilon (BE.lazard_root_quadratic_triple (omega ^+ 2) roots))
    (Q.lazard_t (BE.lazard_root_quadratic_triple (omega ^+ 2) roots))
    (Q.lazard_u (BE.lazard_root_quadratic_triple (omega ^+ 2) roots))
    (RP.lazard_root_fourier_fifth_orbit (omega ^+ 2) roots) i = _.
rewrite lazard_root_quadratic_triple_squared
  lazard_root_fourier_fifth_orbit_squared.
exact: CB.lazard_coherent_alternate_projections_branch.
Qed.

Lemma lazard_root_coherent_alternate_projection_values_fourth
    (roots : 5.-tuple F) (i : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values (omega ^+ 4) roots i =
    RA.lazard_root_coherent_alternate_projection_values omega roots i.
Proof.
have omega2_primitive : 5.-primitive_root (omega ^+ 2).
  by rewrite (prim_root_exp_coprime 2 omega_primitive).
rewrite (@exprM F omega 2 2).
transitivity
  (RA.lazard_root_coherent_alternate_projection_values
    (omega ^+ 2) roots i).
- exact: (@lazard_root_coherent_alternate_projection_values_squared
    F (omega ^+ 2) omega2_primitive roots i).
- exact: lazard_root_coherent_alternate_projection_values_squared.
Qed.

Lemma lazard_root_coherent_alternate_projection_values_cubed
    (roots : 5.-tuple F) (i : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values (omega ^+ 3) roots i =
    RA.lazard_root_coherent_alternate_projection_values omega roots i.
Proof.
have omega4_primitive : 5.-primitive_root (omega ^+ 4).
  by rewrite (prim_root_exp_coprime 4 omega_primitive).
rewrite -(RP.lazard_primitive_fifth_power8 omega_primitive)
  (@exprM F omega 4 2).
transitivity
  (RA.lazard_root_coherent_alternate_projection_values
    (omega ^+ 4) roots i).
- exact: (@lazard_root_coherent_alternate_projection_values_squared
    F (omega ^+ 4) omega4_primitive roots i).
- exact: lazard_root_coherent_alternate_projection_values_fourth.
Qed.

(** Every corrected coordinate is fixed by every element of the standard
    Frobenius group. *)
Theorem lazard_root_coherent_alternate_projection_values_standard_F20
    (roots : 5.-tuple F) (g : S5) (i : 'I_4) :
  g \in standard_F20 ->
  RA.lazard_root_coherent_alternate_projection_values omega
      (TV.permute_quintic_roots g roots) i =
    RA.lazard_root_coherent_alternate_projection_values omega roots i.
Proof.
exact: MD.lazard_root_function_standard_F20
  (lazard_root_coherent_alternate_projection_values_five_cycle (i := i))
  (lazard_root_coherent_alternate_projection_values_multiplier_two (i := i)).
Qed.

End Invariance.

Section GaloisDescent.

Variables (F0 : fieldType) (L : fieldExtType F0).
Variable B : {subfield L}.
Variable omega : L.
Variable roots : 5.-tuple L.
Hypothesis omega_primitive : 5.-primitive_root omega.
Hypothesis galois_BL : galois B {:L}.

(** This is the remaining root-action datum required for descent.  The
    corresponding action on [omega] is derived automatically from its
    primitivity. *)
Hypothesis coherent_galois_root_action :
  forall g : gal_of {:L},
    g \in 'Gal({:L} / B)%G ->
    exists s : S5,
      s \in standard_F20 /\
      map_tuple g roots = TV.permute_quintic_roots s roots.

(** Under the honest combined Galois-action hypotheses, every corrected
    alternate coordinate belongs to the coefficient field. *)
Theorem lazard_root_coherent_alternate_projection_value_mem_base
    (i : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values omega roots i \in B.
Proof.
rewrite -(galois_fixedField galois_BL).
apply/fixedFieldP; first exact: memvf.
move=> g hg.
rewrite lazard_root_coherent_alternate_projection_values_map.
have [s [hs hroots]] := coherent_galois_root_action hg.
have homega := primitive_fifth_rmorphism_image_cases omega_primitive g.
rewrite hroots.
have homega_value :
    RA.lazard_root_coherent_alternate_projection_values
        (g omega) (TV.permute_quintic_roots s roots) i =
      RA.lazard_root_coherent_alternate_projection_values
        omega (TV.permute_quintic_roots s roots) i.
  case: homega=> [->|[->|[->|->]]].
  - reflexivity.
  - exact: lazard_root_coherent_alternate_projection_values_squared.
  - exact: lazard_root_coherent_alternate_projection_values_cubed.
  - exact: lazard_root_coherent_alternate_projection_values_fourth.
rewrite homega_value.
exact: lazard_root_coherent_alternate_projection_values_standard_F20.
Qed.

End GaloisDescent.

Print Assumptions lazard_root_fourier_fifth_orbit_five_cycle.
Print Assumptions lazard_root_coherent_alternate_projection_values_map.
Print Assumptions lazard_root_coherent_alternate_projection_values_squared.
Print Assumptions
  lazard_root_coherent_alternate_projection_value_mem_base.
Print Assumptions
  lazard_root_coherent_alternate_projection_values_standard_F20.

End PolynomialFormulasLazardQuinticRootCoherentAlternateInvariantF20.
