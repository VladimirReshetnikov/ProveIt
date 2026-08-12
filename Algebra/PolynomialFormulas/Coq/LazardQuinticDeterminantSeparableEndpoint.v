From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0.
From PolynomialFormulas Require Import
  QuinticRecursiveFactor
  QuinticCanonicalDecision
  QuinticGaloisAction
  QuinticScalarResolventSeparable
  QuinticThetaValues
  LazardCriticalCommonDivisor
  LazardCriticalPolynomialCommonDivisor
  LazardQuinticRootProjections
  LazardQuinticResolventPolynomial
  LazardQuinticCriticalElimination
  LazardQuinticCriticalPolynomialElimination
  LazardQuinticInvariantSystem
  LazardQuinticDeterminantCertificateMatrix
  LazardQuinticDeterminantCriticalCertificate
  LazardQuinticCanonicalEpsilonNonzero
  LazardQuinticResolventCanonicalBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The exact endpoint of the Figure-3 determinant calculation.

    A zero determinant first forces the compact determinant numerator to
    vanish.  The independently checked critical certificate then makes the
    explicit thirteen-term cubic--quadratic scalar zero.  Its complete
    three-case elimination supplies a nonconstant common divisor of the
    critical polynomials [A] and [B], and the three polynomial identities
    propagate that divisor to the Lazard sextic and its derivative.  Thus a
    separable Lazard sextic forces the displayed determinant to be nonzero;
    no determinant-nonzero hypothesis is assumed in this chain.  A separate
    bridge identifies the scalar unconditionally with the fixed formal
    Sylvester determinant, and with MathComp's trimmed-size [resultant] under
    the corresponding leading-coefficient hypotheses.  This endpoint keeps
    the stronger direct all-cases zero-implies-common-divisor consequence. *)
Module PolynomialFormulasLazardQuinticDeterminantSeparableEndpoint.

Import GRing.Theory.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module QGA := PolynomialFormulasQuinticGaloisAction.
Module QS := PolynomialFormulasQuinticScalarResolventSeparable.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module LR := PolynomialFormulasLazardQuinticResolventPolynomial.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Module PC := PolynomialFormulasLazardCriticalPolynomialCommonDivisor.
Module PE := PolynomialFormulasLazardQuinticCriticalPolynomialElimination.
Module CCD := PolynomialFormulasLazardCriticalCommonDivisor.
Module IS := PolynomialFormulasLazardQuinticInvariantSystem.
Module DM := PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.
Module DC := PolynomialFormulasLazardQuinticDeterminantCriticalCertificate.
Module CB := PolynomialFormulasLazardQuinticResolventCanonicalBridge.
Module CEN := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module F5 := PolynomialFormulasLazardQuinticRootInvariantRelationFifth.
Module TV := PolynomialFormulasQuinticThetaValues.

Local Open Scope ring_scope.

Section GeneralEndpoint.

Variable F : fieldType.

(** Local bridge for the syntactic equality between the Horner-form cubic
    used by the elimination and the power-basis cubic used by the displayed
    resolvent. *)
Add Ring lazard_determinant_endpoint_poly_ring :
  (@PC.lazard_poly_ring_theory F).
Opaque PC.lazard_poly_ring_zero PC.lazard_poly_ring_one
  PC.lazard_poly_ring_add PC.lazard_poly_ring_mul
  PC.lazard_poly_ring_sub PC.lazard_poly_ring_opp
  PC.lazard_poly_ring_eq.

Ltac finish_lazard_determinant_endpoint_poly_ring :=
  repeat first
    [ rewrite polyC_exp | rewrite polyCB | rewrite polyCN
    | rewrite polyCM | rewrite polyCD | rewrite polyC_natr ];
  repeat first
    [ rewrite PC.lazard_poly_ring_addE
    | rewrite PC.lazard_poly_ring_mulE
    | rewrite PC.lazard_poly_ring_subE
    | rewrite PC.lazard_poly_ring_oppE
    | rewrite PC.lazard_poly_ring_zeroE
    | rewrite PC.lazard_poly_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (PC.lazard_poly_ring_eq lhs rhs)
  end;
  ring.

(** The generic square-minus-linear polynomial instantiated with Lazard's
    five coefficients is literally the displayed Lazard sextic. *)
Lemma lazard_critical_f_polyE
    (c : RP.LazardDepressedRootCoefficients F) :
  PE.lazard_critical_f_poly
      (CE.lazard_critical_a c) (CE.lazard_critical_b c)
      (CE.lazard_critical_g c) (CE.lazard_critical_d c)
      (CE.lazard_critical_e c) =
    LR.lazard_resolvent_polynomial c.
Proof.
rewrite /PE.lazard_critical_f_poly /PE.lazard_critical_h_poly
  /PE.lazard_critical_ell_poly
  /CE.lazard_critical_a /CE.lazard_critical_b
  /CE.lazard_critical_g /CE.lazard_critical_d
  /CE.lazard_critical_e
  /LR.lazard_resolvent_polynomial /LR.lazard_resolvent_cubic
  /LR.lazard_resolvent_line -mul_polyC.
finish_lazard_determinant_endpoint_poly_ring.
Qed.

(** A zero value of the explicit critical scalar is an inseparability
    certificate.  The leading coefficient of [A] is [-5], so characteristic
    five is the only exclusion needed for this purely algebraic implication. *)
Theorem lazard_critical_resultant_zero_not_separable
    (c : RP.LazardDepressedRootCoefficients F)
    (five_neq0 : (5%:R : F) != 0)
    (hresultant : CE.lazard_critical_resultant_value c = 0) :
  ~~ separable_poly (LR.lazard_resolvent_polynomial c).
Proof.
have minus_five_neq0 : (- 5%:R : F) != 0.
  by rewrite oppr_eq0.
rewrite /CE.lazard_critical_resultant_value in hresultant.
have hcommon :=
  PC.lazard_resultant_zero_nonconstant_common_divisor
    minus_five_neq0 hresultant.
case: hcommon=> u [usize [huA huB]].
change
  (u %| PE.lazard_critical_A_poly
    (CE.lazard_critical_a c) (CE.lazard_critical_b c)
    (CE.lazard_critical_g c) (CE.lazard_critical_e c)) in huA.
change
  (u %| PE.lazard_critical_B_poly
    (CE.lazard_critical_a c) (CE.lazard_critical_b c)
    (CE.lazard_critical_g c) (CE.lazard_critical_d c)
    (CE.lazard_critical_e c)) in huB.
have hnot :
    ~~ separable_poly
      (PE.lazard_critical_f_poly
        (CE.lazard_critical_a c) (CE.lazard_critical_b c)
        (CE.lazard_critical_g c) (CE.lazard_critical_d c)
        (CE.lazard_critical_e c)).
  apply: (CCD.not_separable_of_critical_common_divisor
    (Q := PE.lazard_critical_Q_poly
      (CE.lazard_critical_a c) (CE.lazard_critical_b c)
      (CE.lazard_critical_g c) (CE.lazard_critical_d c)
      (CE.lazard_critical_e c))
    (q := PE.lazard_critical_q_poly
      (CE.lazard_critical_a c) (CE.lazard_critical_b c)
      (CE.lazard_critical_e c))
    (h1 := (2%:R : F)%:P *
      PE.lazard_critical_hprime_poly
        (CE.lazard_critical_a c) (CE.lazard_critical_b c))
    (ell := PE.lazard_critical_ell_poly (CE.lazard_critical_e c))
    (h := PE.lazard_critical_h_poly
      (CE.lazard_critical_a c) (CE.lazard_critical_b c)
      (CE.lazard_critical_g c))
    (u := u)).
  - exact: PE.lazard_critical_division_polynomial five_neq0.
  - exact: PE.lazard_critical_eliminate_derivative_polynomial.
  - exact: PE.lazard_critical_eliminate_f_polynomial.
  - exact: usize.
  - exact: huA.
  - exact: huB.
by rewrite lazard_critical_f_polyE in hnot.
Qed.

(** The matrix formula and the square certificate are used in the forward
    direction here.  In particular this theorem does not smuggle in the
    desired determinant nonvanishing as a premise. *)
Theorem lazard_invariant_system_matrix_det_neq0_of_resolvent_separable
    (c : RP.LazardDepressedRootCoefficients F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (hseparable : separable_poly (LR.lazard_resolvent_polynomial c)) :
  \det (IS.lazard_invariant_system_matrix c) != 0.
Proof.
apply/eqP=> hdet.
have hnumerator_div :
    DM.lazard_det_certificate_compact_numerator c / 2%:R = 0.
  by rewrite -(DM.lazard_invariant_system_matrix_det_formula c two_neq0)
    hdet.
have hnumerator :
    DM.lazard_det_certificate_compact_numerator c = 0.
  have hmul := congr1 (fun z : F => z * 2%:R) hnumerator_div.
  move: hmul.
  by rewrite divfK // mul0r.
have hresultant : CE.lazard_critical_resultant_value c = 0.
  rewrite (DC.lazard_critical_resultant_value_certificate
    c two_neq0 five_neq0) hnumerator expr2 mul0r oppr0 div0r.
  reflexivity.
have hnot := lazard_critical_resultant_zero_not_separable
  five_neq0 hresultant.
by move: hnot; rewrite hseparable.
Qed.

End GeneralEndpoint.

Section CanonicalEndpoint.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let roots : 5.-tuple L := @QGA.quintic_root_tuple p p_size.

(** Canonical irreducible depressed quintics satisfy the determinant
    nonvanishing conclusion: the canonical bridge identifies the Lazard
    sextic with the product of six pairwise distinct theta factors. *)
Theorem canonical_lazard_invariant_system_matrix_det_neq0
    (p_irr : irreducible_poly p)
    (hdepressed : CEN.lazard_canonical_quintic_depressed f) :
  \det (IS.lazard_invariant_system_matrix
    (RP.lazard_depressed_of_roots roots)) != 0.
Proof.
apply: lazard_invariant_system_matrix_det_neq0_of_resolvent_separable.
- by rewrite pnatr_eq0.
- by rewrite pnatr_eq0.
- rewrite (CB.canonical_lazard_resolvent_eq_scalar p_irr hdepressed).
  exact: QS.canonical_quintic_scalar_resolvent_separable p_irr.
Qed.

(** Canonical root-origin uniqueness with no determinant certificate supplied
    by the caller.  Irreducibility makes the scalar resolvent separable, the
    determinant chain above proves nonsingularity, and the actual ordered
    roots supply the four Figure-3 relations.  The statement covers every one
    of the six selected Lazard orderings. *)
Theorem canonical_lazard_selected_root_invariants_unique_from_i4
    (p_irr : irreducible_poly p)
    (hdepressed : CEN.lazard_canonical_quintic_depressed f)
    (i : 'I_6) (j : RP.LazardRootInvariants L)
    (hj : F5.lazard_invariant_relations
      (RP.lazard_depressed_of_roots (ID.lazard_selected_roots f i)) j)
    (hi4 : RP.lazard_root_i4
        (RP.lazard_root_invariants (ID.lazard_selected_roots f i)) =
      RP.lazard_root_i4 j) :
  RP.lazard_root_invariants (ID.lazard_selected_roots f i) = j.
Proof.
apply: IS.lazard_root_invariants_unique_from_i4.
- by rewrite pnatr_eq0.
- exact: CEN.lazard_selected_root_esymm1_zero hdepressed i.
- exact: hj.
- exact: hi4.
- rewrite /ID.lazard_selected_roots
    (@CB.lazard_representative_depressed_coefficientsE L roots i).
  exact: canonical_lazard_invariant_system_matrix_det_neq0
    p_irr hdepressed.
Qed.

(** Fully root-origin specialization.  When both records are the invariants
    of actual selected root orderings, the second Figure-3 package is also
    constructed internally.  Thus the caller supplies only irreducibility,
    depression, the two orderings, and equality of their [i4] values. *)
Theorem canonical_lazard_selected_root_invariants_eq_of_i4_eq
    (p_irr : irreducible_poly p)
    (hdepressed : CEN.lazard_canonical_quintic_depressed f)
    (i k : 'I_6)
    (hi4 : RP.lazard_root_i4
        (RP.lazard_root_invariants (ID.lazard_selected_roots f i)) =
      RP.lazard_root_i4
        (RP.lazard_root_invariants (ID.lazard_selected_roots f k))) :
  RP.lazard_root_invariants (ID.lazard_selected_roots f i) =
    RP.lazard_root_invariants (ID.lazard_selected_roots f k).
Proof.
apply: canonical_lazard_selected_root_invariants_unique_from_i4.
- exact: p_irr.
- exact: hdepressed.
- apply: F5.lazard_root_invariant_relations.
  + by rewrite pnatr_eq0.
  + exact: CEN.lazard_selected_root_esymm1_zero hdepressed k.
- exact: hi4.
Qed.

End CanonicalEndpoint.

Print Assumptions lazard_critical_resultant_zero_not_separable.
Print Assumptions
  lazard_invariant_system_matrix_det_neq0_of_resolvent_separable.
Print Assumptions canonical_lazard_invariant_system_matrix_det_neq0.
Print Assumptions
  canonical_lazard_selected_root_invariants_unique_from_i4.
Print Assumptions
  canonical_lazard_selected_root_invariants_eq_of_i4_eq.

End PolynomialFormulasLazardQuinticDeterminantSeparableEndpoint.
