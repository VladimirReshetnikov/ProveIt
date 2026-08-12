From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra falgebra fieldext.
From PolynomialFormulas Require Import
  LazardQuinticProjection LazardQuinticRootRadicals
  LazardQuinticRootProjections
  LazardQuinticRootInvariantE LazardQuinticRootBranchEquivariance
  LazardQuinticRootCoherentAlternateEquivariance
  LazardQuinticRootAlternateRecovery
  LazardQuinticRootFourierRelations LazardQuinticVieta
  LazardQuinticRootRadicalCertificate
  LazardQuinticAlternateCertificateRadicalTower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A complete denominator-safe root formula.

    When [E = -(T^2+U^2)] vanishes, the printed formulas for P1 through P4
    cannot be used: not only the standard P1 projection, but also the
    printed P2/P3/P4 numerator formulas divide by [E].  The correct fallback
    developed here does not use any of those quotients.

    We adjoin epsilon, T and U as three separate square roots.  The corrected
    alternate matrix then recovers all four fifth powers by applying its
    zeroth inverse row to the four coherent sign branches.  Adjoining one
    fifth root for each Fourier component gives the actual P1,P2,P4,P3
    orbit.  Direct Fourier inversion recovers all five ordered roots.  Thus
    the fallback is a larger, but honest, radical tower: three square steps
    and four fifth steps, followed by the independently radical primitive
    fifth root. *)
Module PolynomialFormulasLazardQuinticRootCompleteAlternateTower.

Import GRing.Theory.
Local Open Scope ring_scope.

Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module RIE := PolynomialFormulasLazardQuinticRootInvariantE.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RCAE :=
  PolynomialFormulasLazardQuinticRootCoherentAlternateEquivariance.
Module RA := PolynomialFormulasLazardQuinticRootAlternateRecovery.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module V := PolynomialFormulasLazardQuinticVieta.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module P := PolynomialFormulasLazardQuinticProjection.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module C := PolynomialFormulasLazardQuinticCoherentAlternateProjection.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.
Module ACT :=
  PolynomialFormulasLazardQuinticAlternateCertificateRadicalTower.
Module O := PolynomialFormulasLazardOptimality.

Section RootCompleteAlternateTower.

Variables (F0 : fieldType) (L : fieldExtType F0).

(** The ordinary root-origin membership package is strictly stronger than
    the package used by the denominator-safe alternate tower: its first four
    fields are precisely membership of [D], [E], [F], and [G].  Keeping this
    projection at the root-complete boundary lets canonical descent and
    scalar-extension transport be reused without manufacturing a second
    caller certificate. *)
Lemma lazard_alternate_radical_invariant_data_of_root
    (B : {subfield L}) (roots : 5.-tuple L)
    (hdata : RRC.lazard_root_radical_invariant_data_in B roots) :
  ACT.lazard_alternate_radical_invariant_data_in B
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
    (Q.lazard_root_D roots) (Q.lazard_root_F roots)
    (Q.lazard_root_G roots).
Proof.
rewrite /RRC.lazard_root_radical_invariant_data_in in hdata.
case: hdata=> hD hE hF hG _ _ _ _.
constructor; assumption.
Qed.

Definition lazard_root_complete_alternate_triple
    (omega : L) (roots : 5.-tuple L) : Q.lazard_quadratic_triple L :=
  BE.lazard_root_quadratic_triple omega roots.

Definition lazard_root_complete_alternate_source
    (omega : L) (roots : 5.-tuple L) : 'I_4 -> L :=
  BE.lazard_root_fourier_orbit omega roots.

Definition lazard_root_complete_alternate_projections
    (omega : L) (roots : 5.-tuple L) : 'I_4 -> L :=
  RA.lazard_root_coherent_alternate_projection_values omega roots.

Definition lazard_root_complete_alternate_square_field
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L) : {subfield L} :=
  let v := lazard_root_complete_alternate_triple omega roots in
  ACT.lazard_three_square_third_field B
    (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v).

Definition lazard_root_complete_alternate_field
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L) : {subfield L} :=
  ACT.lazard_four_fifth_field_with_root
    (lazard_root_complete_alternate_square_field B omega roots)
    (lazard_root_complete_alternate_source omega roots) omega.

Definition lazard_root_complete_alternate_output
    (omega : L) (roots : 5.-tuple L) (k : 'I_5) : L :=
  let source := lazard_root_complete_alternate_source omega roots in
  V.lazard_inverse_fourier_output omega
    (source P.p0) (source P.p1) (source P.p3) (source P.p2) k.

(** The robust output is definitionally the inverse Fourier transform of
    the actual root Fourier orbit. *)
Lemma lazard_root_complete_alternate_outputE
    (omega : L) (roots : 5.-tuple L)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) (k : 'I_5) :
  lazard_root_complete_alternate_output omega roots k =
    RFR.lazard_reversed_root_tuple roots k.
Proof.
rewrite /lazard_root_complete_alternate_output
  /lazard_root_complete_alternate_source
  /BE.lazard_root_fourier_orbit
  /P.p0 /P.p1 /P.p2 /P.p3 /=.
exact: (@RFR.lazard_inverse_fourier_root_fourier_coordinate
  L omega omega_primitive five_neq0 roots k hsum).
Qed.

(** The root-defined corrected projections are literally the abstract
    coherent projection of the fifth-power Fourier orbit. *)
Lemma lazard_root_complete_alternate_projectionsE
    (omega : L) (roots : 5.-tuple L) :
  lazard_root_complete_alternate_projections omega roots =
    C.lazard_coherent_alternate_projections
      (Q.lazard_epsilon
        (lazard_root_complete_alternate_triple omega roots))
      (Q.lazard_t
        (lazard_root_complete_alternate_triple omega roots))
      (Q.lazard_u
        (lazard_root_complete_alternate_triple omega roots))
      (RP.lazard_root_fourier_fifth_orbit omega roots).
Proof.
apply/funext=> j.
rewrite /lazard_root_complete_alternate_projections
  /RA.lazard_root_coherent_alternate_projection_values
  /lazard_root_complete_alternate_triple
  /BE.lazard_root_quadratic_triple.
reflexivity.
Qed.

(** Each actual Fourier component has its fifth power equal to the branch
    inverse of the one descended projection vector. *)
Theorem lazard_root_complete_alternate_component_fifth
    (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (j : 'I_4) :
  lazard_root_complete_alternate_source omega roots j ^+ 5 =
    C.lazard_coherent_alternate_recover
      (Q.lazard_epsilon
        (Q.lazard_branch_triple
          (lazard_root_complete_alternate_triple omega roots)
          (ACT.lazard_branch_for_orbit_index j)))
      (Q.lazard_t
        (Q.lazard_branch_triple
          (lazard_root_complete_alternate_triple omega roots)
          (ACT.lazard_branch_for_orbit_index j)))
      (Q.lazard_u
        (Q.lazard_branch_triple
          (lazard_root_complete_alternate_triple omega roots)
          (ACT.lazard_branch_for_orbit_index j)))
      (lazard_root_complete_alternate_projections omega roots).
Proof.
have hcyclo := RR.lazard_primitive_fifth_root_cyclotomic omega_primitive.
have hden :
    C.lazard_coherent_alternate_denominator
      (Q.lazard_t (lazard_root_complete_alternate_triple omega roots))
      (Q.lazard_u (lazard_root_complete_alternate_triple omega roots)) != 0.
  change C.lazard_coherent_alternate_denominator
    (RR.lazard_root_T omega roots)
    (RR.lazard_root_formula_U omega roots) != 0.
  exact: RA.lazard_root_coherent_alternate_denominator_neq0
    hcyclo five_neq0 hroots.
have hepsilon : Q.lazard_epsilon
    (lazard_root_complete_alternate_triple omega roots) != 0.
  exact root_epsilon_neq0.
have hrecover :=
  ACT.lazard_coherent_alternate_recover_orbit_coordinate
    (v := lazard_root_complete_alternate_triple omega roots)
    (source := RP.lazard_root_fourier_fifth_orbit omega roots)
    j two_neq0 hepsilon hden.
rewrite -lazard_root_complete_alternate_projectionsE in hrecover.
rewrite hrecover.
exact: esym (RCAE.lazard_root_fourier_fifth_orbitE omega roots j).
Qed.

(** The three quadratic generators form an honest radical extension.  In
    contrast with the standard certificate, U is adjoined through its own
    square equation, so no division by T is needed. *)
Theorem lazard_root_complete_alternate_square_field_is_radical
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (hdata : ACT.lazard_alternate_radical_invariant_data_in B
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
      (Q.lazard_root_D roots) (Q.lazard_root_F roots)
      (Q.lazard_root_G roots)) :
  @O.radical_extension F0 L B
    (lazard_root_complete_alternate_square_field B omega roots).
Proof.
pose v := lazard_root_complete_alternate_triple omega roots.
have root_epsilon_neq0_RR : RR.lazard_root_epsilon omega roots != 0.
  move: root_epsilon_neq0.
  by rewrite /v /lazard_root_complete_alternate_triple
    /BE.lazard_root_quadratic_triple
    /RP.lazard_root_epsilon /RR.lazard_root_epsilon
    /RP.lazard_root_discriminant_factor
    /RR.lazard_fifth_root_discriminant_factor
    /RP.lazard_root_epsilon_product /RR.lazard_epsilon_product.
have hrelations := @Q.lazard_root_quadratic_relations_primitive
  L omega roots two_neq0 omega_primitive root_epsilon_neq0_RR.
have hE := @RIE.lazard_root_invariant_E_eq L roots hsum.
have hepsilon : Q.lazard_epsilon v ^+ 2 \in B.
  rewrite /v /lazard_root_complete_alternate_triple
    /BE.lazard_root_quadratic_triple.
  rewrite (Q.lazard_epsilon_square hrelations).
  exact: rpredM (CRT.lazard_natr_mem B 5)
    (ACT.lazard_alternate_D_in_base hdata).
have ht : Q.lazard_t v ^+ 2 \in
    ACT.lazard_two_square_first_field B (Q.lazard_epsilon v).
  rewrite /v /lazard_root_complete_alternate_triple
    /BE.lazard_root_quadratic_triple.
  rewrite (Q.lazard_t_square hrelations) -hE.
  apply: rpredM.
  - exact: rpred_div (CRT.lazard_natr_mem _ 5)
      (CRT.lazard_natr_mem _ 2).
  - apply: rpredD.
    + exact: subvP_adjoin (ACT.lazard_alternate_E_in_base hdata).
    + exact: rpred_div
        (subvP_adjoin (ACT.lazard_alternate_F_in_base hdata)) memv_adjoin.
have hu : Q.lazard_u v ^+ 2 \in
    ACT.lazard_two_square_second_field B
      (Q.lazard_epsilon v) (Q.lazard_t v).
  rewrite /v /lazard_root_complete_alternate_triple
    /BE.lazard_root_quadratic_triple.
  rewrite (Q.lazard_u_square hrelations) -hE.
  apply: rpredM.
  - exact: rpred_div (CRT.lazard_natr_mem _ 5)
      (CRT.lazard_natr_mem _ 2).
  - apply: rpredB.
    + exact: subvP_adjoin (subvP_adjoin
        (ACT.lazard_alternate_E_in_base hdata)).
    + exact: rpred_div
        (subvP_adjoin (subvP_adjoin
          (ACT.lazard_alternate_F_in_base hdata)))
        (subvP_adjoin memv_adjoin).
change @O.radical_extension F0 L B
  (ACT.lazard_three_square_third_field B
    (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v)).
exact: ACT.lazard_three_square_third_field_is_radical hepsilon ht hu.
Qed.

(** All four root-defined Fourier fifth powers lie in the three-square
    field, using only descended corrected projection values. *)
Theorem lazard_root_complete_alternate_fourier_fifths_mem_square_field
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (hprojections : ACT.lazard_alternate_projection_data_in B
      (lazard_root_complete_alternate_projections omega roots))
    (j : 'I_4) :
  lazard_root_complete_alternate_source omega roots j ^+ 5 \in
    lazard_root_complete_alternate_square_field B omega roots.
Proof.
rewrite (lazard_root_complete_alternate_component_fifth
  two_neq0 five_neq0 omega_primitive hroots root_epsilon_neq0 j).
pose v := lazard_root_complete_alternate_triple omega roots.
pose B3 := lazard_root_complete_alternate_square_field B omega roots.
change C.lazard_coherent_alternate_recover
    (Q.lazard_epsilon
      (Q.lazard_branch_triple v (ACT.lazard_branch_for_orbit_index j)))
    (Q.lazard_t
      (Q.lazard_branch_triple v (ACT.lazard_branch_for_orbit_index j)))
    (Q.lazard_u
      (Q.lazard_branch_triple v (ACT.lazard_branch_for_orbit_index j)))
    (lazard_root_complete_alternate_projections omega roots) \in B3.
have hv : CRT.lazard_quadratic_triple_in B3 v.
  constructor.
  - exact: ACT.lazard_three_square_epsilon_mem_third B
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v).
  - exact: ACT.lazard_three_square_t_mem_third B
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v).
  - exact: ACT.lazard_three_square_u_mem_third B
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v).
have hvbranch := CRT.lazard_quadratic_triple_in_branch
  (ACT.lazard_branch_for_orbit_index j) hv.
apply: ACT.lazard_coherent_alternate_recover_mem hvbranch.
move=> k.
exact: ACT.lazard_three_square_base_mem_third
  (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v)
  (hprojections k).
Qed.

(** Complete robust alternate tower and exact reconstruction of all five
    roots.  No E-nonzero premise and no standard numerator formula occurs. *)
Theorem lazard_root_complete_alternate_all_roots_in_radical_extension
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (hdata : ACT.lazard_alternate_radical_invariant_data_in B
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
      (Q.lazard_root_D roots) (Q.lazard_root_F roots)
      (Q.lazard_root_G roots))
    (hprojections : ACT.lazard_alternate_projection_data_in B
      (lazard_root_complete_alternate_projections omega roots)) :
  @O.radical_extension F0 L B
      (lazard_root_complete_alternate_field B omega roots) /\
    (forall k : 'I_5,
      lazard_root_complete_alternate_output omega roots k \in
        lazard_root_complete_alternate_field B omega roots) /\
    (forall k : 'I_5,
      lazard_root_complete_alternate_output omega roots k =
        RFR.lazard_reversed_root_tuple roots k).
Proof.
have hsquare := lazard_root_complete_alternate_square_field_is_radical
  two_neq0 omega_primitive root_epsilon_neq0 hsum hdata.
have hpowers j :=
  lazard_root_complete_alternate_fourier_fifths_mem_square_field
    two_neq0 five_neq0 omega_primitive hroots root_epsilon_neq0
    hprojections j.
split.
- rewrite /lazard_root_complete_alternate_field.
  exact: ACT.lazard_four_fifth_field_with_primitive_root_is_radical
    hsquare hpowers omega_primitive.
- split.
  + move=> k.
    rewrite /lazard_root_complete_alternate_output
      /lazard_root_complete_alternate_field.
    exact: ACT.lazard_four_fifth_inverse_fourier_output_mem.
  + move=> k.
    exact: lazard_root_complete_alternate_outputE
      five_neq0 omega_primitive hsum.
Qed.

(** Convenience form for the actual root-origin application.  Canonical
    root membership and its extension-transport theorem produce
    [lazard_root_radical_invariant_data_in]; the smaller alternate record is
    now derived internally. *)
Theorem
    lazard_root_complete_alternate_all_roots_in_radical_extension_of_root_data
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (hdata : RRC.lazard_root_radical_invariant_data_in B roots)
    (hprojections : ACT.lazard_alternate_projection_data_in B
      (lazard_root_complete_alternate_projections omega roots)) :
  @O.radical_extension F0 L B
      (lazard_root_complete_alternate_field B omega roots) /\
    (forall k : 'I_5,
      lazard_root_complete_alternate_output omega roots k \in
        lazard_root_complete_alternate_field B omega roots) /\
    (forall k : 'I_5,
      lazard_root_complete_alternate_output omega roots k =
        RFR.lazard_reversed_root_tuple roots k).
Proof.
exact: (@lazard_root_complete_alternate_all_roots_in_radical_extension
  F0 L B omega roots two_neq0 five_neq0 omega_primitive hroots
  root_epsilon_neq0 hsum
  (lazard_alternate_radical_invariant_data_of_root hdata) hprojections).
Qed.

(** Exact Vieta data for the five denominator-safe outputs.  It is derived
    from the actual root tuple and Fourier inversion; no Vieta or
    correctness certificate is a premise. *)
Theorem lazard_root_complete_alternate_relations
    (omega : L) (roots : 5.-tuple L)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  V.lazard_depressed_five_root_relations
    (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
    (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
    (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
    (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
    (lazard_root_complete_alternate_output omega roots).
Proof.
have houtput :
    lazard_root_complete_alternate_output omega roots =
      RFR.lazard_reversed_root_tuple roots.
  apply/funext=> k.
  exact: lazard_root_complete_alternate_outputE
    five_neq0 omega_primitive hsum.
rewrite houtput.
exact: (@RFR.lazard_reversed_root_relations L roots hsum).
Qed.

(** Multiplicity-preserving factorization of the original depressed
    quintic by the five robust alternate outputs. *)
Theorem lazard_root_complete_alternate_eval_factorization
    (omega : L) (roots : 5.-tuple L)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) (z : L) :
  V.lazard_depressed_quintic_eval
      (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
    (z - lazard_root_complete_alternate_output omega roots o0) *
    (z - lazard_root_complete_alternate_output omega roots o1) *
    (z - lazard_root_complete_alternate_output omega roots o2) *
    (z - lazard_root_complete_alternate_output omega roots o3) *
    (z - lazard_root_complete_alternate_output omega roots o4).
Proof.
exact: V.lazard_depressed_vieta_eval_factorization
  (lazard_root_complete_alternate_relations
    five_neq0 omega_primitive hsum) z.
Qed.

(** Every denominator-safe output is an actual root. *)
Theorem lazard_root_complete_alternate_output_root
    (omega : L) (roots : 5.-tuple L)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) (k : 'I_5) :
  V.lazard_depressed_quintic_eval
      (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
      (lazard_root_complete_alternate_output omega roots k) = 0.
Proof.
exact: V.lazard_depressed_vieta_root
  (lazard_root_complete_alternate_relations
    five_neq0 omega_primitive hsum) k.
Qed.

(** Every root of the original depressed quintic occurs among the five
    denominator-safe outputs. *)
Theorem lazard_root_complete_alternate_output_complete
    (omega : L) (roots : 5.-tuple L)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) (z : L)
    (hz : V.lazard_depressed_quintic_eval
      (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0) :
  exists k : 'I_5,
    z = lazard_root_complete_alternate_output omega roots k.
Proof.
exact: V.lazard_depressed_vieta_complete
  (lazard_root_complete_alternate_relations
    five_neq0 omega_primitive hsum) hz.
Qed.

(** Root-set form of the exact alternate factorization. *)
Theorem lazard_root_complete_alternate_output_root_iff
    (omega : L) (roots : 5.-tuple L)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) (z : L) :
  V.lazard_depressed_quintic_eval
      (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0 <->
    exists k : 'I_5,
      z = lazard_root_complete_alternate_output omega roots k.
Proof.
exact: V.lazard_depressed_vieta_root_iff
  (lazard_root_complete_alternate_relations
    five_neq0 omega_primitive hsum) z.
Qed.

End RootCompleteAlternateTower.

Print Assumptions lazard_root_complete_alternate_component_fifth.
Print Assumptions
  lazard_root_complete_alternate_square_field_is_radical.
Print Assumptions
  lazard_root_complete_alternate_fourier_fifths_mem_square_field.
Print Assumptions
  lazard_root_complete_alternate_all_roots_in_radical_extension.
Print Assumptions
  lazard_root_complete_alternate_all_roots_in_radical_extension_of_root_data.
Print Assumptions lazard_root_complete_alternate_relations.
Print Assumptions lazard_root_complete_alternate_eval_factorization.
Print Assumptions lazard_root_complete_alternate_output_root.
Print Assumptions lazard_root_complete_alternate_output_complete.
Print Assumptions lazard_root_complete_alternate_output_root_iff.

End PolynomialFormulasLazardQuinticRootCompleteAlternateTower.
