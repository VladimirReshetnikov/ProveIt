From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootInvariantE LazardQuinticRootInvariantENonzeroF20
  LazardQuinticRootMembershipDescent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Transport the nonvanishing hypotheses of the root-origin Lazard
    certificate along an arbitrary field embedding.

    Canonical root ordering and invariant descent are naturally proved in
    MathComp's canonical splitting field [numfield p].  The actual radical
    formulas must usually be evaluated in a larger field which also contains
    a primitive fifth root of unity.  This file supplies the honest bridge:
    map the ordered roots through a field morphism, preserve injectivity and
    depression, and derive both nonzero denominators in the target field. *)
Module PolynomialFormulasLazardQuinticRootExtensionTransport.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.

Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module RIE := PolynomialFormulasLazardQuinticRootInvariantE.
Module ENZ := PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.
Module IF20 := PolynomialFormulasLazardQuinticRootInvariantF20.
Module RM := PolynomialFormulasLazardQuinticRootMembershipDescent.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.

Section ExtensionTransport.

Variables (F E : fieldType).
Variable h : {rmorphism F -> E}.

Lemma lazard_extension_map_tuple_injective (roots : 5.-tuple F) :
  injective (tnth roots) -> injective (tnth (map_tuple h roots)).
Proof.
move=> hroots i j hij.
apply: hroots.
apply: (fmorph_inj h).
by rewrite !tnth_map.
Qed.

Lemma lazard_extension_root_esymm1_map roots :
  h (RP.lazard_root_esymm1 roots) =
    RP.lazard_root_esymm1 (map_tuple h roots).
Proof.
by rewrite /RP.lazard_root_esymm1 !rmorphD !tnth_map.
Qed.

Lemma lazard_extension_projection_epsilon_product_map roots :
  h (RP.lazard_root_epsilon_product roots) =
    RP.lazard_root_epsilon_product (map_tuple h roots).
Proof.
by rewrite /RP.lazard_root_epsilon_product
  !rmorphM !rmorphD !rmorphB !tnth_map.
Qed.

Lemma lazard_extension_root_E_map roots :
  h (Q.lazard_root_E roots) = Q.lazard_root_E (map_tuple h roots).
Proof.
by rewrite /Q.lazard_root_E rmorphN rmorphD !rmorphXn
  ENZ.lazard_root_T_prime_map ENZ.lazard_root_U_prime_map.
Qed.

(** The primitive-root coefficient multiplying the epsilon product is
    nonzero in any target field of characteristic different from five. *)
Lemma lazard_extension_fifth_root_discriminant_factor_neq0
    (five_neq0 : (5%:R : E) != 0)
    (omega : E) (omega_primitive : 5.-primitive_root omega) :
  RR.lazard_fifth_root_discriminant_factor omega != 0.
Proof.
apply/eqP=> hzero.
have hcyclo := RR.lazard_primitive_fifth_root_cyclotomic omega_primitive.
have hsquare :=
  RR.lazard_fifth_root_discriminant_factor_sq_of_cyclotomic hcyclo.
rewrite hzero expr2 mul0r in hsquare.
by move: five_neq0; rewrite -hsquare eqxx.
Qed.

Lemma lazard_extension_mapped_root_epsilon_neq0
    (five_neq0 : (5%:R : E) != 0)
    (roots : 5.-tuple F)
    (epsilon_product_neq0 : RP.lazard_root_epsilon_product roots != 0)
    (omega : E) (omega_primitive : 5.-primitive_root omega) :
  RP.lazard_root_epsilon omega (map_tuple h roots) != 0.
Proof.
rewrite /RP.lazard_root_epsilon.
apply: mulf_neq0.
- change (RR.lazard_fifth_root_discriminant_factor omega != 0).
  exact: lazard_extension_fifth_root_discriminant_factor_neq0
    five_neq0 omega_primitive.
- rewrite -lazard_extension_projection_epsilon_product_map.
  by rewrite fmorph_eq0.
Qed.

Lemma lazard_extension_mapped_root_E_neq0 (roots : 5.-tuple F) :
  Q.lazard_root_E roots != 0 ->
  Q.lazard_root_E (map_tuple h roots) != 0.
Proof.
move=> hE.
rewrite -lazard_extension_root_E_map.
by rewrite fmorph_eq0.
Qed.

(** Aggregate target-field hypotheses consumed by
    [lazard_exists_root_radical_certificate]. *)
Theorem lazard_root_extension_hypotheses
    (five_neq0 : (5%:R : E) != 0)
    (roots : 5.-tuple F)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (epsilon_product_neq0 : RP.lazard_root_epsilon_product roots != 0)
    (root_E_neq0 : Q.lazard_root_E roots != 0)
    (omega : E) (omega_primitive : 5.-primitive_root omega) :
  [/
    injective (tnth (map_tuple h roots)),
    RP.lazard_root_esymm1 (map_tuple h roots) = 0,
    RP.lazard_root_epsilon omega (map_tuple h roots) != 0
  & FN.lazard_invariant_E
      (RP.lazard_depressed_of_roots (map_tuple h roots))
      (RP.lazard_root_invariants (map_tuple h roots)) != 0].
Proof.
have hroots_map := lazard_extension_map_tuple_injective h hroots.
have hsum_map : RP.lazard_root_esymm1 (map_tuple h roots) = 0.
  by rewrite -lazard_extension_root_esymm1_map hsum rmorph0.
have hepsilon := lazard_extension_mapped_root_epsilon_neq0 h
  five_neq0 epsilon_product_neq0 omega_primitive.
have hEroot := lazard_extension_mapped_root_E_neq0 h root_E_neq0.
have hE : FN.lazard_invariant_E
    (RP.lazard_depressed_of_roots (map_tuple h roots))
    (RP.lazard_root_invariants (map_tuple h roots)) != 0.
  rewrite (RIE.lazard_root_invariant_E_eq hsum_map).
  exact: hEroot.
by split.
Qed.

End ExtensionTransport.

Section MembershipTransport.

Variable K : fieldType.
Variables (F E : fieldExtType K).
Variable h : 'AHom(F, E).

(** An algebra homomorphism over the common ground field maps its ground
    field line onto the corresponding ground field line. *)
Lemma lazard_map_bottom_mem (x : F) :
  x \in (1%AS : {subfield F}) ->
  h x \in (1%AS : {subfield E}).
Proof.
move=> hx.
rewrite -(aimg1 h).
exact: memv_img h hx.
Qed.

Lemma lazard_depressed_p_map (roots : 5.-tuple F) :
  h (RP.lazard_root_p (RP.lazard_depressed_of_roots roots)) =
    RP.lazard_root_p
      (RP.lazard_depressed_of_roots (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_p
  (RM.lazard_depressed_of_roots_map h roots).
Qed.

Lemma lazard_depressed_q_map (roots : 5.-tuple F) :
  h (RP.lazard_root_q (RP.lazard_depressed_of_roots roots)) =
    RP.lazard_root_q
      (RP.lazard_depressed_of_roots (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_q
  (RM.lazard_depressed_of_roots_map h roots).
Qed.

Lemma lazard_depressed_r_map (roots : 5.-tuple F) :
  h (RP.lazard_root_r (RP.lazard_depressed_of_roots roots)) =
    RP.lazard_root_r
      (RP.lazard_depressed_of_roots (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_r
  (RM.lazard_depressed_of_roots_map h roots).
Qed.

Lemma lazard_depressed_s_map (roots : 5.-tuple F) :
  h (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) =
    RP.lazard_root_s
      (RP.lazard_depressed_of_roots (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_s
  (RM.lazard_depressed_of_roots_map h roots).
Qed.

Lemma lazard_invariant_i4_map (roots : 5.-tuple F) :
  h (RP.lazard_root_i4 (RP.lazard_root_invariants roots)) =
    RP.lazard_root_i4 (RP.lazard_root_invariants (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_i4
  (IF20.lazard_root_invariants_mapE h roots).
Qed.

Lemma lazard_invariant_i5_map (roots : 5.-tuple F) :
  h (RP.lazard_root_i5 (RP.lazard_root_invariants roots)) =
    RP.lazard_root_i5 (RP.lazard_root_invariants (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_i5
  (IF20.lazard_root_invariants_mapE h roots).
Qed.

Lemma lazard_invariant_i6_map (roots : 5.-tuple F) :
  h (RP.lazard_root_i6 (RP.lazard_root_invariants roots)) =
    RP.lazard_root_i6 (RP.lazard_root_invariants (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_i6
  (IF20.lazard_root_invariants_mapE h roots).
Qed.

Lemma lazard_invariant_i7_map (roots : 5.-tuple F) :
  h (RP.lazard_root_i7 (RP.lazard_root_invariants roots)) =
    RP.lazard_root_i7 (RP.lazard_root_invariants (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_i7
  (IF20.lazard_root_invariants_mapE h roots).
Qed.

Lemma lazard_invariant_i8_map (roots : 5.-tuple F) :
  h (RP.lazard_root_i8 (RP.lazard_root_invariants roots)) =
    RP.lazard_root_i8 (RP.lazard_root_invariants (map_tuple h roots)).
Proof.
exact: congr1 RP.lazard_root_i8
  (IF20.lazard_root_invariants_mapE h roots).
Qed.

Lemma lazard_depressed_coefficients_in_map_bot (roots : 5.-tuple F) :
  @RM.lazard_depressed_coefficients_in K F
      (1%AS : {subfield F}) (RP.lazard_depressed_of_roots roots) ->
  @RM.lazard_depressed_coefficients_in K E
      (1%AS : {subfield E})
      (RP.lazard_depressed_of_roots (map_tuple h roots)).
Proof.
case=> hp hq hr hs; constructor.
- rewrite -lazard_depressed_p_map.
  exact: lazard_map_bottom_mem hp.
- rewrite -lazard_depressed_q_map.
  exact: lazard_map_bottom_mem hq.
- rewrite -lazard_depressed_r_map.
  exact: lazard_map_bottom_mem hr.
- rewrite -lazard_depressed_s_map.
  exact: lazard_map_bottom_mem hs.
Qed.

Lemma lazard_invariant_coordinates_in_map_bot (roots : 5.-tuple F) :
  @RM.lazard_invariant_coordinates_in K F
      (1%AS : {subfield F}) (RP.lazard_root_invariants roots) ->
  @RM.lazard_invariant_coordinates_in K E
      (1%AS : {subfield E})
      (RP.lazard_root_invariants (map_tuple h roots)).
Proof.
case=> hi4 hi5 hi6 hi7 hi8; constructor.
- rewrite -lazard_invariant_i4_map.
  exact: lazard_map_bottom_mem hi4.
- rewrite -lazard_invariant_i5_map.
  exact: lazard_map_bottom_mem hi5.
- rewrite -lazard_invariant_i6_map.
  exact: lazard_map_bottom_mem hi6.
- rewrite -lazard_invariant_i7_map.
  exact: lazard_map_bottom_mem hi7.
- rewrite -lazard_invariant_i8_map.
  exact: lazard_map_bottom_mem hi8.
Qed.

(** Transport the two complete membership packages without reproving any of
    the large coefficient formulas.  Only D/F/G are taken from the source
    radical record; H/I/J/K and all ten Fourier numerators are regenerated
    in the target from the transported nine base coordinates. *)
Theorem lazard_root_membership_data_map_bot (roots : 5.-tuple F)
    (hc : @RM.lazard_depressed_coefficients_in K F
      (1%AS : {subfield F}) (RP.lazard_depressed_of_roots roots))
    (hi : @RM.lazard_invariant_coordinates_in K F
      (1%AS : {subfield F}) (RP.lazard_root_invariants roots))
    (hdata : @RRC.lazard_root_radical_invariant_data_in K F
      (1%AS : {subfield F}) roots) :
  @RRC.lazard_root_radical_invariant_data_in K E
      (1%AS : {subfield E}) (map_tuple h roots) /\
  @RRC.lazard_root_fourier_numerator_data_in K E
      (1%AS : {subfield E}) (map_tuple h roots).
Proof.
case: hdata=> hD _ hF hG _ _ _ _.
have hcE := lazard_depressed_coefficients_in_map_bot h hc.
have hiE := lazard_invariant_coordinates_in_map_bot h hi.
have hDE : Q.lazard_root_D (map_tuple h roots) \in
    (1%AS : {subfield E}).
  rewrite -RM.lazard_root_D_map.
  exact: lazard_map_bottom_mem hD.
have hFE : Q.lazard_root_F (map_tuple h roots) \in
    (1%AS : {subfield E}).
  rewrite -RM.lazard_root_F_map.
  exact: lazard_map_bottom_mem hF.
have hGE : Q.lazard_root_G (map_tuple h roots) \in
    (1%AS : {subfield E}).
  rewrite -RM.lazard_root_G_map.
  exact: lazard_map_bottom_mem hG.
split.
- exact: RM.lazard_radical_invariant_data_in_of_coordinates
    hDE hFE hGE hcE hiE.
- exact: RM.lazard_fourier_numerator_data_in_of_coordinates hcE hiE.
Qed.

End MembershipTransport.

End PolynomialFormulasLazardQuinticRootExtensionTransport.
