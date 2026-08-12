From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticCoherentAlternateCompositumDescent
  LazardQuinticRootCompleteAlternateTower
  LazardQuinticRootExtensionTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The common-overfield descent theorem composed with the robust alternate
    radical tower.

    The root-complete tower is deliberately reusable: it accepts membership
    of the four corrected projection values in an arbitrary base subfield.
    In the actual resolvent application those memberships are not extra
    certificates.  A rational theta value puts the ordered Galois action in
    [F20], cyclotomic equivariance fixes the corrected values, and Galois
    descent puts them in the embedded coefficient field.  This file performs
    exactly that final composition. *)
Module PolynomialFormulasLazardQuinticCoherentAlternateCompositumTower.

Import GRing.Theory.
Local Open Scope ring_scope.

Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module GE := PolynomialFormulasLazardGeneralResolventExplicit.
Module CD :=
  PolynomialFormulasLazardQuinticCoherentAlternateCompositumDescent.
Module RCT := PolynomialFormulasLazardQuinticRootCompleteAlternateTower.
Module RT := PolynomialFormulasLazardQuinticRootExtensionTransport.
Module RM := PolynomialFormulasLazardQuinticRootMembershipDescent.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.
Module ACT :=
  PolynomialFormulasLazardQuinticAlternateCertificateRadicalTower.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module V := PolynomialFormulasLazardQuinticVieta.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module O := PolynomialFormulasLazardOptimality.

Section CommonGaloisOverfieldTower.

Variables (F : fieldType) (L : splittingFieldType F).
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Variable basePolynomial : {poly subvs_of K}.
Variable roots : 5.-tuple (subvs_of E).
Hypothesis root_presentation :
  @GE.lazard_ordered_root_presentation
    F L K E galois_K_E 5 basePolynomial roots.

Local Notation base_embed :=
  (@GC.lazard_base_embedding F L K E galois_K_E).

Variables (i : 'I_6) (q : subvs_of K).
Hypothesis selected_theta_base :
  PolynomialFormulasQuinticThetaValues.quintic_theta_value roots i =
    base_embed q.
Hypothesis theta_values_injective :
  injective
    (PolynomialFormulasQuinticThetaValues.quintic_theta_value roots).

Variable omega : subvs_of E.
Hypothesis omega_primitive : 5.-primitive_root omega.

Let selected_roots : 5.-tuple (subvs_of E) :=
  CD.lazard_compositum_selected_roots roots i.

(** Complete denominator-safe radical reconstruction in the common Galois
    overfield.  The projection-membership premise of the reusable tower has
    disappeared: it is proved from the resolvent-selected [F20] action and
    fixed-field descent. *)
Theorem lazard_compositum_coherent_alternate_radical_tower
    (B : {subfield (subvs_of E)})
    (base_embedding_mem : forall a : subvs_of K, base_embed a \in B)
    (two_neq0 : (2%:R : subvs_of E) != 0)
    (five_neq0 : (5%:R : subvs_of E) != 0)
    (hroots : injective (tnth selected_roots))
    (root_epsilon_neq0 :
      RP.lazard_root_epsilon omega selected_roots != 0)
    (hsum : RP.lazard_root_esymm1 selected_roots = 0)
    (hdata : ACT.lazard_alternate_radical_invariant_data_in B
      (RP.lazard_depressed_of_roots selected_roots)
      (RP.lazard_root_invariants selected_roots)
      (Q.lazard_root_D selected_roots)
      (Q.lazard_root_F selected_roots)
      (Q.lazard_root_G selected_roots)) :
  @O.radical_extension F (subvs_of E) B
      (RCT.lazard_root_complete_alternate_field
        B omega selected_roots) /\
    (forall k : 'I_5,
      RCT.lazard_root_complete_alternate_output omega selected_roots k \in
        RCT.lazard_root_complete_alternate_field B omega selected_roots) /\
    (forall k : 'I_5,
      RCT.lazard_root_complete_alternate_output omega selected_roots k =
        RFR.lazard_reversed_root_tuple selected_roots k).
Proof.
have hprojections : ACT.lazard_alternate_projection_data_in B
    (RCT.lazard_root_complete_alternate_projections
      omega selected_roots).
  move=> j.
  change
    PolynomialFormulasLazardQuinticRootAlternateRecovery.
      lazard_root_coherent_alternate_projection_values
        omega selected_roots j \in B.
  exact: (@CD.lazard_compositum_coherent_alternate_projection_data_in
    F L K E galois_K_E basePolynomial roots root_presentation
    i q selected_theta_base theta_values_injective omega omega_primitive
    B base_embedding_mem j).
exact: (@RCT.lazard_root_complete_alternate_all_roots_in_radical_extension
  F (subvs_of E) B omega selected_roots
  two_neq0 five_neq0 omega_primitive hroots root_epsilon_neq0
  hsum hdata hprojections).
Qed.

(** Focused composition with the existing canonical-membership transport.
    The source tuple may, in particular, be the centered selected tuple in
    the canonical number field.  Its complete root-membership package is
    transported through [h], identified with the representative-selected
    common-overfield tuple, and projected internally to the four fields used
    by the alternate tower.  Thus the caller no longer supplies [hdata]. *)
Theorem
    lazard_compositum_coherent_alternate_radical_tower_of_mapped_root_data
    (S : fieldExtType F) (h : 'AHom(S, subvs_of E))
    (source_roots : 5.-tuple S)
    (hselected : map_tuple h source_roots = selected_roots)
    (hc : @RM.lazard_depressed_coefficients_in F S
      (1%AS : {subfield S})
      (RP.lazard_depressed_of_roots source_roots))
    (hinvariants : @RM.lazard_invariant_coordinates_in F S
      (1%AS : {subfield S})
      (RP.lazard_root_invariants source_roots))
    (hsource_data : @RRC.lazard_root_radical_invariant_data_in F S
      (1%AS : {subfield S}) source_roots)
    (base_embedding_mem : forall a : subvs_of K,
      base_embed a \in (1%AS : {subfield (subvs_of E)}))
    (two_neq0 : (2%:R : subvs_of E) != 0)
    (five_neq0 : (5%:R : subvs_of E) != 0)
    (hroots : injective (tnth selected_roots))
    (root_epsilon_neq0 :
      RP.lazard_root_epsilon omega selected_roots != 0)
    (hsum : RP.lazard_root_esymm1 selected_roots = 0) :
  @O.radical_extension F (subvs_of E)
      (1%AS : {subfield (subvs_of E)})
      (RCT.lazard_root_complete_alternate_field
        (1%AS : {subfield (subvs_of E)}) omega selected_roots) /\
    (forall k : 'I_5,
      RCT.lazard_root_complete_alternate_output omega selected_roots k \in
        RCT.lazard_root_complete_alternate_field
          (1%AS : {subfield (subvs_of E)}) omega selected_roots) /\
    (forall k : 'I_5,
      RCT.lazard_root_complete_alternate_output omega selected_roots k =
        RFR.lazard_reversed_root_tuple selected_roots k).
Proof.
have [htarget_data _] :=
  @RT.lazard_root_membership_data_map_bot
    F S (subvs_of E) h source_roots hc hinvariants hsource_data.
have hselected_data :
    @RRC.lazard_root_radical_invariant_data_in F (subvs_of E)
      (1%AS : {subfield (subvs_of E)}) selected_roots.
  rewrite -hselected.
  exact: htarget_data.
have hprojections : ACT.lazard_alternate_projection_data_in
    (1%AS : {subfield (subvs_of E)})
    (RCT.lazard_root_complete_alternate_projections
      omega selected_roots).
  move=> j.
  change
    PolynomialFormulasLazardQuinticRootAlternateRecovery.
      lazard_root_coherent_alternate_projection_values
        omega selected_roots j \in
          (1%AS : {subfield (subvs_of E)}).
  exact: (@CD.lazard_compositum_coherent_alternate_projection_data_in
    F L K E galois_K_E basePolynomial roots root_presentation
    i q selected_theta_base theta_values_injective omega omega_primitive
    (1%AS : {subfield (subvs_of E)}) base_embedding_mem j).
exact:
  (@RCT.lazard_root_complete_alternate_all_roots_in_radical_extension_of_root_data
    F (subvs_of E) (1%AS : {subfield (subvs_of E)})
    omega selected_roots two_neq0 five_neq0 omega_primitive hroots
    root_epsilon_neq0 hsum hselected_data hprojections).
Qed.

(** The matching multiplicity-preserving factorization is independent of
    the radical-membership argument and follows from the root-derived Vieta
    identities. *)
Theorem lazard_compositum_coherent_alternate_eval_factorization
    (five_neq0 : (5%:R : subvs_of E) != 0)
    (hsum : RP.lazard_root_esymm1 selected_roots = 0)
    (z : subvs_of E) :
  V.lazard_depressed_quintic_eval
      (RP.lazard_root_p (RP.lazard_depressed_of_roots selected_roots))
      (RP.lazard_root_q (RP.lazard_depressed_of_roots selected_roots))
      (RP.lazard_root_r (RP.lazard_depressed_of_roots selected_roots))
      (RP.lazard_root_s (RP.lazard_depressed_of_roots selected_roots)) z =
    (z - RCT.lazard_root_complete_alternate_output
      omega selected_roots o0) *
    (z - RCT.lazard_root_complete_alternate_output
      omega selected_roots o1) *
    (z - RCT.lazard_root_complete_alternate_output
      omega selected_roots o2) *
    (z - RCT.lazard_root_complete_alternate_output
      omega selected_roots o3) *
    (z - RCT.lazard_root_complete_alternate_output
      omega selected_roots o4).
Proof.
exact: (@RCT.lazard_root_complete_alternate_eval_factorization
  F (subvs_of E) omega selected_roots
  five_neq0 omega_primitive hsum z).
Qed.

(** The factorization premise used for descent also gives the two
    extensional correctness statements expected of a root-producing
    formula.  They are stated separately from the radical-membership theorem
    because no branch or membership certificate is needed: the alternate
    output is the fixed reversal of the representative-selected complete
    root tuple. *)
Lemma lazard_compositum_presented_roots_sound
    (k : 'I_5) :
  root (map_poly base_embed basePolynomial) (tnth roots k).
Proof.
have hfactor := root_presentation.2.
rewrite (eqp_root hfactor) root_prod_XsubC.
exact: mem_tnth.
Qed.

Lemma lazard_compositum_presented_roots_complete
    (z : subvs_of E) :
  root (map_poly base_embed basePolynomial) z ->
  exists k : 'I_5, z = tnth roots k.
Proof.
have hfactor := root_presentation.2.
rewrite (eqp_root hfactor) root_prod_XsubC.
move=> /tnthP [k hk].
by exists k.
Qed.

Lemma lazard_compositum_selected_roots_sound
    (k : 'I_5) :
  root (map_poly base_embed basePolynomial) (tnth selected_roots k).
Proof.
rewrite /selected_roots
  /CD.lazard_compositum_selected_roots
  PolynomialFormulasQuinticThetaValues.tnth_permute_quintic_roots.
exact: lazard_compositum_presented_roots_sound.
Qed.

Lemma lazard_compositum_selected_roots_complete
    (z : subvs_of E) :
  root (map_poly base_embed basePolynomial) z ->
  exists k : 'I_5, z = tnth selected_roots k.
Proof.
move=> hz.
have [k hk] := lazard_compositum_presented_roots_complete hz.
exists (representative i k).
rewrite /selected_roots
  /CD.lazard_compositum_selected_roots
  PolynomialFormulasQuinticThetaValues.tnth_permute_quintic_roots
  permK.
exact: hk.
Qed.

Lemma lazard_compositum_reversed_selected_roots_sound
    (k : 'I_5) :
  root (map_poly base_embed basePolynomial)
    (RFR.lazard_reversed_root_tuple selected_roots k).
Proof.
case: k=> [[|[|[|[|[|k]]]]] hk];
  rewrite /RFR.lazard_reversed_root_tuple /=;
  exact: lazard_compositum_selected_roots_sound.
Qed.

Lemma lazard_compositum_reversed_selected_roots_complete
    (z : subvs_of E) :
  root (map_poly base_embed basePolynomial) z ->
  exists k : 'I_5,
    z = RFR.lazard_reversed_root_tuple selected_roots k.
Proof.
move=> hz.
have [k hk] := lazard_compositum_selected_roots_complete hz.
case: k hk=> [[|[|[|[|[|k]]]]] hk hzk.
- exists o0.
  by rewrite /RFR.lazard_reversed_root_tuple /=.
- exists o4.
  by rewrite /RFR.lazard_reversed_root_tuple /=.
- exists o3.
  by rewrite /RFR.lazard_reversed_root_tuple /=.
- exists o2.
  by rewrite /RFR.lazard_reversed_root_tuple /=.
- exists o1.
  by rewrite /RFR.lazard_reversed_root_tuple /=.
Qed.

Theorem lazard_compositum_coherent_alternate_output_correct
    (five_neq0 : (5%:R : subvs_of E) != 0)
    (hsum : RP.lazard_root_esymm1 selected_roots = 0) :
  (forall k : 'I_5,
    root (map_poly base_embed basePolynomial)
      (RCT.lazard_root_complete_alternate_output
        omega selected_roots k)) /\
  (forall z : subvs_of E,
    root (map_poly base_embed basePolynomial) z ->
    exists k : 'I_5,
      z = RCT.lazard_root_complete_alternate_output
        omega selected_roots k).
Proof.
have houtput : forall k : 'I_5,
    RCT.lazard_root_complete_alternate_output omega selected_roots k =
      RFR.lazard_reversed_root_tuple selected_roots k.
  move=> k.
  exact: RCT.lazard_root_complete_alternate_outputE
    five_neq0 omega_primitive hsum.
split.
- move=> k; rewrite houtput.
  exact: lazard_compositum_reversed_selected_roots_sound.
- move=> z hz.
  have [k hk] := lazard_compositum_reversed_selected_roots_complete hz.
  exists k.
  by rewrite houtput.
Qed.

End CommonGaloisOverfieldTower.

Print Assumptions lazard_compositum_coherent_alternate_radical_tower.
Print Assumptions
  lazard_compositum_coherent_alternate_radical_tower_of_mapped_root_data.
Print Assumptions lazard_compositum_coherent_alternate_eval_factorization.
Print Assumptions lazard_compositum_coherent_alternate_output_correct.

End PolynomialFormulasLazardQuinticCoherentAlternateCompositumTower.
