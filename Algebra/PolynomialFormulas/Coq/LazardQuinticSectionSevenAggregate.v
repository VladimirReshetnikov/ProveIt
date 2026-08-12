From mathcomp Require Import all_ssreflect all_fingroup all_algebra fieldext.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticVieta LazardQuinticRootInvariantRelationFifth
  LazardQuinticRootInvariantDFG LazardQuinticRootInvariantE
  LazardQuinticQuadratic LazardQuinticRootQ1Bridge
  LazardQuinticRootFourierNumeratorRelations
  LazardQuinticRootFourierRelations LazardQuinticRootFormulaReconstruction
  LazardQuinticRootRadicalCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** One public composition boundary for the printed, nondegenerate Section 7
    calculation.  Every field below is derived from the same ordered tuple
    of actual roots.  No Fourier relation, Vieta relation, or output
    correctness certificate is a premise. *)
Module PolynomialFormulasLazardQuinticSectionSevenAggregate.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.

Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module IR5 := PolynomialFormulasLazardQuinticRootInvariantRelationFifth.
Module DFG := PolynomialFormulasLazardQuinticRootInvariantDFG.
Module RIE := PolynomialFormulasLazardQuinticRootInvariantE.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module RJK := PolynomialFormulasLazardQuinticRootProjectionJKCommon.
Module RQ := PolynomialFormulasLazardQuinticRootQ1Bridge.
Module Q1 := PolynomialFormulasLazardQuinticQ1Branches.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRelations.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module V := PolynomialFormulasLazardQuinticVieta.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module RF := PolynomialFormulasLazardQuinticRootFormulaReconstruction.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.

Section SectionSevenAggregate.

Variables (F0 : fieldType) (F : fieldExtType F0).

(** The literal root-origin identities before the finite nonzero-P1 branch is
    selected.  The quotient field is universally quantified over branches
    and states its genuine denominator premise explicitly. *)
Record lazard_section_seven_root_claims
    (omega : F) (roots : 5.-tuple F) : Prop :=
  LazardSectionSevenRootClaims {
  lazard_section7_figure3 :
    IR5.lazard_invariant_relations
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots);
  lazard_section7_invariant_D :
    DFG.lazard_invariant_D (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) = Q.lazard_root_D roots;
  lazard_section7_invariant_E :
    FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) = Q.lazard_root_E roots;
  lazard_section7_invariant_F :
    DFG.lazard_invariant_F (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) = Q.lazard_root_F roots;
  lazard_section7_invariant_G :
    DFG.lazard_invariant_G (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) = Q.lazard_root_G roots;
  lazard_section7_quadratic :
    Q.lazard_quadratic_relations
      (Q.lazard_root_D roots) (Q.lazard_root_E roots)
      (Q.lazard_root_F roots) (Q.lazard_root_G roots)
      (Q.LazardQuadraticTriple
        (RR.lazard_root_epsilon omega roots)
        (RR.lazard_root_T omega roots)
        (RR.lazard_root_formula_U omega roots));
  lazard_section7_H :
    RQ.lazard_root_section7_H omega roots =
      RP.lazard_root_invariant_H (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots);
  lazard_section7_I :
    RQ.lazard_root_section7_I omega roots =
      RP.lazard_root_invariant_I (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots);
  lazard_section7_J :
    RQ.lazard_root_section7_J omega roots =
      RJK.lazard_root_invariant_J (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots);
  lazard_section7_K :
    RQ.lazard_root_section7_K omega roots =
      RJK.lazard_root_invariant_K (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots);
  lazard_section7_Q1 : forall branch : Q.lazard_sign_branch,
    RQ.lazard_root_q1_formula omega roots branch =
      RQ.lazard_root_q1_target omega roots branch;
  lazard_section7_corrected_Pij : forall first second : Q.lazard_sign_branch,
    let v := Q.lazard_branch_triple
      (Q.lazard_branch_triple
        (BE.lazard_root_quadratic_triple omega roots) first) second in
    let source := BE.lazard_source_for_branch
      (BE.lazard_source_for_branch
        (BE.lazard_root_fourier_orbit omega roots) first) second in
    NR.lazard_fourier_numerator_relations
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
      v (source p0) (source p1) (source p3) (source p2);
  lazard_section7_quotient_branches :
    forall first second : Q.lazard_sign_branch,
    let v := Q.lazard_branch_triple
      (Q.lazard_branch_triple
        (BE.lazard_root_quadratic_triple omega roots) first) second in
    let source := BE.lazard_source_for_branch
      (BE.lazard_source_for_branch
        (BE.lazard_root_fourier_orbit omega roots) first) second in
    source p0 != 0 ->
    NR.lazard_fourier_formula_components
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
      v (source p0) (source p1) (source p3) (source p2);
  lazard_section7_compatible_fourier_choices :
    forall (first second : Q.lazard_sign_branch) (j : 'I_4),
      BE.lazard_source_for_branch
          (BE.lazard_source_for_branch
            (BE.lazard_root_fourier_orbit omega roots) first) second j ^+ 5 =
        BE.lazard_root_fourier_orbit omega
          (BE.lazard_roots_for_branch
            (BE.lazard_roots_for_branch roots first) second) j ^+ 5;
  lazard_section7_inverse_fourier : forall k : 'I_5,
    V.lazard_inverse_fourier_output omega
        (RP.lazard_root_fourier_P1 omega roots)
        (RP.lazard_root_fourier_P2 omega roots)
        (RP.lazard_root_fourier_P3 omega roots)
        (RP.lazard_root_fourier_P4 omega roots) k =
      RFR.lazard_reversed_root_tuple roots k
  }.

(** The selected radical record and the exact five-root conclusion.  Its
    P1 power equation is a field of a root-constructed certificate, not a
    caller-supplied radical choice. *)
Record lazard_section_seven_selected_claims
    (omega : F) (roots : 5.-tuple F)
    (first second : Q.lazard_sign_branch)
    (d : RRC.lazard_root_radical_certificate roots) : Prop :=
  LazardSectionSevenSelectedClaims {
  lazard_section7_selected_initial :
    CRT.lazard_certificate_initial d =
      Q.lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
        first;
  lazard_section7_selected_t_nonzero :
    Q.lazard_t (CRT.lazard_certificate_initial d) != 0;
  lazard_section7_selected_branch :
    CRT.lazard_certificate_branch d = second;
  lazard_section7_selected_P1 :
    CRT.lazard_certificate_p1 d =
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0;
  lazard_section7_selected_P1_nonzero :
    CRT.lazard_certificate_p1 d != 0;
  lazard_section7_selected_chosen :
    CRT.lazard_certificate_chosen d =
      Q.lazard_branch_triple
        (Q.lazard_branch_triple
          (BE.lazard_root_quadratic_triple omega roots) first) second;
  lazard_section7_selected_P1_fifth_Q1 :
    CRT.lazard_certificate_p1 d ^+ 5 =
      Q1.lazard_q1
        (RRC.lazard_root_H roots) (RRC.lazard_root_I roots)
        (RRC.lazard_root_J roots) (RRC.lazard_root_K roots)
        (FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
          (RP.lazard_root_invariants roots))
        (Q.lazard_branch_triple (CRT.lazard_certificate_initial d)
          (CRT.lazard_certificate_branch d));
  lazard_section7_selected_P1_actual_fifth :
    CRT.lazard_certificate_p1 d ^+ 5 =
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 ^+ 5;
  lazard_section7_selected_reconstruction : forall k : 'I_5,
    RRC.lazard_root_certificate_output omega roots d k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch roots first) second) k;
  lazard_section7_selected_vieta :
    V.lazard_depressed_five_root_relations
      (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
      (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
      (RRC.lazard_root_certificate_output omega roots d);
  lazard_section7_selected_polynomial_factorization :
    V.lazard_depressed_quintic_polynomial
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) =
      \prod_(k : 'I_5)
        ('X - (RRC.lazard_root_certificate_output omega roots d k)%:P);
  lazard_section7_selected_factorization : forall z : F,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
      (z - RRC.lazard_root_certificate_output omega roots d o0) *
      (z - RRC.lazard_root_certificate_output omega roots d o1) *
      (z - RRC.lazard_root_certificate_output omega roots d o2) *
      (z - RRC.lazard_root_certificate_output omega roots d o3) *
      (z - RRC.lazard_root_certificate_output omega roots d o4);
  lazard_section7_selected_sound : forall k : 'I_5,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
        (RRC.lazard_root_certificate_output omega roots d k) = 0;
  lazard_section7_selected_complete : forall z : F,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0 ->
      exists k : 'I_5,
        z = RRC.lazard_root_certificate_output omega roots d k
  }.

Definition lazard_section_seven_aggregate
    (omega : F) (roots : 5.-tuple F) : Prop :=
  lazard_section_seven_root_claims omega roots /\
  exists first : Q.lazard_sign_branch,
  exists second : Q.lazard_sign_branch,
  exists d : RRC.lazard_root_radical_certificate roots,
    lazard_section_seven_selected_claims omega roots first second d.

(** Construct all pre-selection identities directly from actual roots. *)
Theorem lazard_section_seven_root_claims_of_roots
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 :
      FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) != 0) :
  lazard_section_seven_root_claims omega roots.
Proof.
have root_epsilon_neq0_RR : RR.lazard_root_epsilon omega roots != 0.
  rewrite -(@RRC.lazard_root_epsilon_definitionsE F omega roots).
  exact root_epsilon_neq0.
have root_E_neq0 : Q.lazard_root_E roots != 0.
  rewrite -(@RIE.lazard_root_invariant_E_eq F roots hsum).
  exact E_neq0.
constructor.
- exact: (@IR5.lazard_root_invariant_relations F roots two_neq0 hsum).
- exact: (@DFG.lazard_root_invariant_D_eq F roots hsum).
- exact: (@RIE.lazard_root_invariant_E_eq F roots hsum).
- exact: (@DFG.lazard_root_invariant_F_eq F roots hsum).
- exact: (@DFG.lazard_root_invariant_G_eq F roots hsum).
- exact: (@Q.lazard_root_quadratic_relations_primitive
    F omega roots two_neq0 omega_primitive root_epsilon_neq0_RR).
- exact: (@RQ.lazard_root_section7_H_eq
    F omega roots five_neq0 omega_primitive hsum).
- exact: (@RQ.lazard_root_section7_I_eq
    F omega roots five_neq0 omega_primitive hsum).
- exact: (@RQ.lazard_root_section7_J_eq
    F omega roots five_neq0 omega_primitive hsum).
- exact: (@RQ.lazard_root_section7_K_eq
    F omega roots five_neq0 omega_primitive hsum).
- move=> branch.
  exact: (@RQ.lazard_root_q1_formula_correct F omega roots branch
    two_neq0 five_neq0 omega_primitive hsum root_epsilon_neq0
    root_E_neq0).
- move=> first second.
  exact: (@NR.lazard_root_fourier_numerator_relations_two_branches
    F omega roots first second omega_primitive five_neq0 hsum).
- move=> first second p1_neq0.
  have he0 :
      Q.lazard_epsilon (BE.lazard_root_quadratic_triple omega roots) != 0.
    exact root_epsilon_neq0.
  have he1 := BE.lazard_branch_epsilon_neq0 first he0.
  have he2 := BE.lazard_branch_epsilon_neq0 second he1.
  exact: (@NR.lazard_root_fourier_formula_components_two_branches
    F omega roots first second two_neq0 five_neq0 omega_primitive hsum
    he2 E_neq0 p1_neq0).
- move=> first second j.
  by rewrite BE.lazard_root_fourier_orbit_roots_for_two_branches.
- move=> k.
  exact: (@RFR.lazard_inverse_fourier_root_fourier_coordinate
    F omega omega_primitive five_neq0 roots k hsum).
Qed.

(** The complete Section 7 package.  Injectivity is used only to select a
    nonzero Fourier coordinate; all correctness identities are then derived
    from that same root tuple and the selected root-origin certificate. *)
Theorem lazard_section_seven_aggregate_of_roots
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 :
      FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) != 0) :
  lazard_section_seven_aggregate omega roots.
Proof.
split.
- exact: lazard_section_seven_root_claims_of_roots
    two_neq0 five_neq0 omega_primitive hsum root_epsilon_neq0 E_neq0.
- have [first [second [d
      [hinitial [ht [hbranch [hp1 [hp1_neq0 [hchosen
        [hreversed [hfactor [hsound hcomplete]]]]]]]]]]]] :=
    RRC.lazard_exists_root_radical_certificate_complete
      two_neq0 five_neq0 omega_primitive hroots hsum
      root_epsilon_neq0 E_neq0.
  have houtput :
      RRC.lazard_root_certificate_output omega roots d =
        RF.lazard_formula_output_two_branches omega roots first second.
    exact: RRC.lazard_root_certificate_outputE hp1 hchosen.
  have hvieta :
      V.lazard_depressed_five_root_relations
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
        (RRC.lazard_root_certificate_output omega roots d).
    rewrite houtput.
    exact: (@RF.lazard_formula_output_two_branches_five_root_relations
      F omega roots first second two_neq0 five_neq0 omega_primitive hsum
      root_epsilon_neq0 E_neq0 hp1_neq0).
  exists first, second, d.
  constructor.
  + exact hinitial.
  + exact ht.
  + exact hbranch.
  + exact hp1.
  + exact hp1_neq0.
  + exact hchosen.
  + exact: CRT.lazard_certificate_p1_fifth.
  + by rewrite hp1.
  + exact hreversed.
  + exact hvieta.
  + exact: V.lazard_depressed_vieta_polynomial_factorization hvieta.
  + exact hfactor.
  + exact hsound.
  + exact hcomplete.
Qed.

Print Assumptions lazard_section_seven_root_claims_of_roots.
Print Assumptions lazard_section_seven_aggregate_of_roots.
Print Assumptions lazard_section7_selected_vieta.
Print Assumptions lazard_section7_selected_polynomial_factorization.

End SectionSevenAggregate.

End PolynomialFormulasLazardQuinticSectionSevenAggregate.
