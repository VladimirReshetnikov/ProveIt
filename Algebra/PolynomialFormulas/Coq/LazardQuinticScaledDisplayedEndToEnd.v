From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field falgebra fieldext.
From Abel Require Import char0.
From PolynomialFormulas Require Import
  QuinticCanonicalDecision LazardQuinticInvariantDescentF20
  LazardQuinticCanonicalEpsilonNonzero LazardQuinticRootCentering
  LazardQuinticRootMembershipDescent LazardQuinticRootExtensionTransport
  LazardQuinticDisplayedRadicalCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A general coefficient-to-displayed-radical-tower wrapper.

    Earlier public theorems separately supplied

      scaled resolvent root -> selected canonical ordering,
      selected ordering -> bottom-field membership data,
      selected ordering -> nonvanishing, and
      root data -> displayed radical tower.

    The theorem below composes these results for every irreducible depressed
    monic integer quintic.  It deliberately retains both the rational
    resolvent witness and its selected [F20]-orbit index, and states that the
    roots used by the final certificate are the image of that very same
    centered selected ordering.  The target is an arbitrary rational field
    extension containing a chosen primitive fifth root, so no unjustified
    assumption that the canonical quintic splitting field itself contains
    such a root is made. *)
Module PolynomialFormulasLazardQuinticScaledDisplayedEndToEnd.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Local Open Scope ring_scope.

Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module ENZ := PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.
Module RC := PolynomialFormulasLazardQuinticRootCentering.
Module RM := PolynomialFormulasLazardQuinticRootMembershipDescent.
Module RT := PolynomialFormulasLazardQuinticRootExtensionTransport.
Module DRC := PolynomialFormulasLazardQuinticDisplayedRadicalCertificate.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module V := PolynomialFormulasLazardQuinticVieta.
Module LO := PolynomialFormulasLazardOptimality.
Module T4 := PolynomialFormulasLazardOptimalityTheoremFourDegree.

Section ScaledDisplayedTower.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let canonical_roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

Variable E : fieldExtType rat.
Variable iota : 'AHom(L, E).
Variable omega : E.

(** All conclusions supplied by the displayed root-origin tower, bundled so
    the selected index and ordering can be retained in the outer record. *)
Definition canonical_scaled_displayed_tower_properties
    (roots : 5.-tuple E) (first second : Q.lazard_sign_branch)
    (d : DRC.lazard_displayed_root_radical_certificate roots) : Prop :=
  CRT.lazard_certificate_p1 d != 0 /\
  @T4.square_roots_and_fifth_root_presentation rat E
    (1%AS : {subfield E})
    (CRT.lazard_certificate_generated_field
      (1%AS : {subfield E}) d) 2 /\
  @LO.radical_extension rat E (1%AS : {subfield E})
    (DRC.lazard_displayed_root_certificate_field
      (1%AS : {subfield E}) omega roots d) /\
  (forall k : 'I_5,
    DRC.lazard_displayed_root_certificate_output omega roots d k \in
      DRC.lazard_displayed_root_certificate_field
        (1%AS : {subfield E}) omega roots d) /\
  (forall k : 'I_5,
    DRC.lazard_displayed_root_certificate_output omega roots d k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch roots first) second) k) /\
  (forall z : E,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
      (z - DRC.lazard_displayed_root_certificate_output omega roots d o0) *
      (z - DRC.lazard_displayed_root_certificate_output omega roots d o1) *
      (z - DRC.lazard_displayed_root_certificate_output omega roots d o2) *
      (z - DRC.lazard_displayed_root_certificate_output omega roots d o3) *
      (z - DRC.lazard_displayed_root_certificate_output omega roots d o4)) /\
  (forall k : 'I_5,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
        (DRC.lazard_displayed_root_certificate_output omega roots d k) = 0) /\
  (forall z : E,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0 ->
    exists k : 'I_5,
      z = DRC.lazard_displayed_root_certificate_output omega roots d k).

(** Public result package.  The equality [canonical_scaled_tower_rootsE]
    is the preservation guarantee missing from the earlier aggregate
    wrapper: no second choice of ordering or index occurs downstream. *)
Record canonical_scaled_displayed_radical_tower :=
  CanonicalScaledDisplayedRadicalTower {
    canonical_scaled_rational_witness : rat;
    canonical_scaled_selected_index : 'I_6;
    canonical_scaled_selected_thetaE :
      TV.quintic_theta_value canonical_roots
          canonical_scaled_selected_index =
        ratrL canonical_scaled_rational_witness;
    canonical_scaled_tower_roots : 5.-tuple E;
    canonical_scaled_tower_rootsE :
      canonical_scaled_tower_roots =
        map_tuple iota
          (RC.lazard_centered_roots
            (ID.lazard_selected_roots canonical_scaled_selected_index));
    canonical_scaled_first_branch : Q.lazard_sign_branch;
    canonical_scaled_second_branch : Q.lazard_sign_branch;
    canonical_scaled_displayed_certificate :
      DRC.lazard_displayed_root_radical_certificate
        canonical_scaled_tower_roots;
    canonical_scaled_displayed_properties :
      canonical_scaled_displayed_tower_properties
        canonical_scaled_tower_roots canonical_scaled_first_branch
        canonical_scaled_second_branch
        canonical_scaled_displayed_certificate
  }.

(** The coefficient-to-formula package retains the exact formula-side
    radical count, not merely the weaker fact that its generated field is
    radical. *)
Lemma canonical_scaled_displayed_formula_presentation
    (w : canonical_scaled_displayed_radical_tower) :
  @T4.square_roots_and_fifth_root_presentation rat E
    (1%AS : {subfield E})
    (CRT.lazard_certificate_generated_field
      (1%AS : {subfield E})
      (canonical_scaled_displayed_certificate w)) 2.
Proof.
exact: (proj1 (proj2 (canonical_scaled_displayed_properties w))).
Qed.

Lemma rational_extension_two_neq0 : (2%:R : E) != 0.
Proof.
by rewrite -[2%:R](rmorph_nat (in_alg E) 2) fmorph_eq0.
Qed.

Lemma rational_extension_five_neq0 : (5%:R : E) != 0.
Proof.
by rewrite -[5%:R](rmorph_nat (in_alg E) 5) fmorph_eq0.
Qed.

(** The complete composition from the executable scaled resolvent. *)
Theorem exists_canonical_scaled_displayed_radical_tower
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f)
    (hq : RRS.has_rational_root (QPS.quintic_scaled_resolvent f))
    (omega_primitive : 5.-primitive_root omega) :
  canonical_scaled_displayed_radical_tower.
Proof.
have hsemantic :=
  (proj1 (@CD.quintic_scaled_resolvent_has_rational_root_correct
    L ratrL canonical_roots f
    (@CD.canonical_quintic_padded_vieta f)
    (@CD.canonical_quintic_resolvent_scale_nonzero f p_irr))) hq.
case: hsemantic=> q hqscalar.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff
    canonical_roots (ratrL q))) hqscalar.
pose rootsL :=
  RC.lazard_centered_roots (ID.lazard_selected_roots i).
pose rootsE := map_tuple iota rootsL.
have hrootsL : injective (tnth rootsL) :=
  RC.lazard_centered_selected_roots_injective p_irr i.
have hsumL : RP.lazard_root_esymm1 rootsL = 0 :=
  RC.lazard_centered_roots_sum_zero
    (ID.lazard_selected_roots i) (by rewrite pnatr_eq0).
have hepsilon_productL : RP.lazard_root_epsilon_product rootsL != 0.
  rewrite /rootsL RC.lazard_root_projection_epsilon_product_centered.
  change (RR.lazard_epsilon_product (ID.lazard_selected_roots i) != 0).
  exact: CE.lazard_selected_epsilon_product_neq0
    p_irr hdepressed i.
have hrootEL : Q.lazard_root_E rootsL != 0.
  rewrite /rootsL RC.lazard_root_E_centered.
  exact: ENZ.lazard_selected_root_E_neq0 p_irr hi.
have hcL := RM.lazard_centered_selected_depressed_coefficients_in
  (1%AS : {subfield L}) p_irr hi.
have hinvL := RM.lazard_centered_selected_invariant_coordinates_in
  (1%AS : {subfield L}) p_irr hi.
have [hdataL _] := RM.lazard_centered_selected_root_membership_data_bot
  p_irr hi.
have [hdataE hnumE] := RT.lazard_root_membership_data_map_bot
  iota hcL hinvL hdataL.
have [hrootsE hsumE hepsilonE hEE] :=
  RT.lazard_root_extension_hypotheses iota
    rational_extension_five_neq0 hrootsL hsumL
    hepsilon_productL hrootEL omega_primitive.
have hdisplayE :=
  DRC.lazard_displayed_root_radical_invariant_data_of_root
    hsumE hdataE.
have [first [second [d
    [hp1 [hradical [hmem [hreconstruct
      [hfactor [hroot hcomplete]]]]]]]]]] :=
  DRC.lazard_exists_displayed_root_radical_tower_complete
    rational_extension_two_neq0 rational_extension_five_neq0
    omega_primitive hrootsE hsumE hepsilonE hEE hdisplayE hnumE.
have hpresentation :=
  CRT.lazard_certificate_generated_field_has_two_square_fifth_presentation
    d hdisplayE.
refine
  {| canonical_scaled_rational_witness := q;
     canonical_scaled_selected_index := i;
     canonical_scaled_selected_thetaE := hi;
     canonical_scaled_tower_roots := rootsE;
     canonical_scaled_tower_rootsE := erefl;
     canonical_scaled_first_branch := first;
     canonical_scaled_second_branch := second;
     canonical_scaled_displayed_certificate := d;
     canonical_scaled_displayed_properties := _ |}.
repeat split.
- exact: hp1.
- exact: hpresentation.
- exact: hradical.
- exact: hmem.
- exact: hreconstruct.
- exact: hfactor.
- exact: hroot.
- exact: hcomplete.
Qed.

End ScaledDisplayedTower.

End PolynomialFormulasLazardQuinticScaledDisplayedEndToEnd.
