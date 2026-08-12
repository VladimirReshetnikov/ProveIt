From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  QuinticRecursiveFactor QuinticCanonicalDecision
  QuinticPaddedSymmetrization SexticNewtonPowerSums
  SexticComputedResolvents
  LazardQuinticRootProjections LazardQuinticRootBranchEquivariance
  LazardQuinticRootInvariantRelationFifthData
  LazardQuinticRootInvariantRelationFifth
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticInvariantSystem
  LazardQuinticInvariantDescentF20
  LazardQuinticCanonicalEpsilonNonzero
  LazardQuinticDeterminantSeparableEndpoint
  LazardQuinticRationalScalingAdapter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Arbitrary-rational transport for the Section-7 determinant.

    The canonical Coq endpoint is stated for the integer-coded monic
    quintic used by the executable pipeline.  This file closes the scope
    gap without assuming separability or determinant nonvanishing for the
    original polynomial.

    If the roots and the depressed coefficients are dilated by [d], their
    weights are respectively

      roots: 1,       (p,q,r,s): (2,3,4,5).

    The four rows of Lazard's Figure-3 matrix have weights
    (8,12,16,20), while its four unknowns have weights (5,6,7,8).
    Factoring row weights (0,4,8,12) and column weights (3,2,1,0)
    therefore shows that the determinant has weight 30.  The nonzero
    determinant for the integer dilation consequently implies the nonzero
    determinant for the original rational quintic.

    Irreducibility is retained: it is what proves separability of the six
    canonical theta values.  With no such hypothesis the conclusion is
    false (the parallel Lean invariant-system development contains an
    explicit singular coefficient example).  No separability or determinant
    certificate is accepted by any theorem below. *)
Module PolynomialFormulasLazardQuinticRationalDeterminantTransport.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Module F20 := PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module SNP := PolynomialFormulasSexticNewtonPowerSums.
Module SCV := PolynomialFormulasSexticComputedResolvents.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module F5 := PolynomialFormulasLazardQuinticRootInvariantRelationFifth.
Module FD := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module IS := PolynomialFormulasLazardQuinticInvariantSystem.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module DE := PolynomialFormulasLazardQuinticDeterminantSeparableEndpoint.
Module RSA := PolynomialFormulasLazardQuinticRationalScalingAdapter.

Local Open Scope ring_scope.

Section HomogeneousTransport.

Variable F : fieldType.

Add Ring lazard_rational_determinant_transport_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_rational_determinant_transport_ring :=
  lazard_numerator_prepare;
  repeat first [rewrite exprS | rewrite expr0];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Dilation of the coefficient record of
    [X^5 + p X^3 + q X^2 + r X + s]. *)
Definition lazard_scale_depressed_coefficients
    (d : F) (c : RP.LazardDepressedRootCoefficients F) :
    RP.LazardDepressedRootCoefficients F :=
  {| RP.lazard_root_p := d ^+ 2 * RP.lazard_root_p c;
     RP.lazard_root_q := d ^+ 3 * RP.lazard_root_q c;
     RP.lazard_root_r := d ^+ 4 * RP.lazard_root_r c;
     RP.lazard_root_s := d ^+ 5 * RP.lazard_root_s c |}.

(** Coordinatewise scalar extension of a depressed coefficient record. *)
Definition lazard_depressed_coefficients_map
    (E : fieldType) (phi : {rmorphism F -> E})
    (c : RP.LazardDepressedRootCoefficients F) :
    RP.LazardDepressedRootCoefficients E :=
  {| RP.lazard_root_p := phi (RP.lazard_root_p c);
     RP.lazard_root_q := phi (RP.lazard_root_q c);
     RP.lazard_root_r := phi (RP.lazard_root_r c);
     RP.lazard_root_s := phi (RP.lazard_root_s c) |}.

Lemma lazard_scale_depressed_coefficients_injective d (hd : d != 0) :
  injective (lazard_scale_depressed_coefficients d).
Proof.
move=> c1 c2 hscale.
apply: BE.lazard_depressed_coefficients_ext.
- apply: (mulfI (expf_neq0 2 hd)).
  exact: congr1 RP.lazard_root_p hscale.
- apply: (mulfI (expf_neq0 3 hd)).
  exact: congr1 RP.lazard_root_q hscale.
- apply: (mulfI (expf_neq0 4 hd)).
  exact: congr1 RP.lazard_root_r hscale.
- apply: (mulfI (expf_neq0 5 hd)).
  exact: congr1 RP.lazard_root_s hscale.
Qed.

Lemma lazard_root_esymm1_scale d (roots : 5.-tuple F) :
  RP.lazard_root_esymm1 (RSA.lazard_scale_quintic_roots d roots) =
    d * RP.lazard_root_esymm1 roots.
Proof.
rewrite /RP.lazard_root_esymm1 /RSA.lazard_scale_quintic_roots
  !tnth_mktuple.
finish_lazard_rational_determinant_transport_ring.
Qed.

Lemma lazard_root_esymm2_scale d (roots : 5.-tuple F) :
  RP.lazard_root_esymm2 (RSA.lazard_scale_quintic_roots d roots) =
    d ^+ 2 * RP.lazard_root_esymm2 roots.
Proof.
rewrite /RP.lazard_root_esymm2 /RSA.lazard_scale_quintic_roots
  !tnth_mktuple.
finish_lazard_rational_determinant_transport_ring.
Qed.

Lemma lazard_root_esymm3_scale d (roots : 5.-tuple F) :
  RP.lazard_root_esymm3 (RSA.lazard_scale_quintic_roots d roots) =
    d ^+ 3 * RP.lazard_root_esymm3 roots.
Proof.
rewrite /RP.lazard_root_esymm3 /RSA.lazard_scale_quintic_roots
  !tnth_mktuple.
finish_lazard_rational_determinant_transport_ring.
Qed.

Lemma lazard_root_esymm4_scale d (roots : 5.-tuple F) :
  RP.lazard_root_esymm4 (RSA.lazard_scale_quintic_roots d roots) =
    d ^+ 4 * RP.lazard_root_esymm4 roots.
Proof.
rewrite /RP.lazard_root_esymm4 /RSA.lazard_scale_quintic_roots
  !tnth_mktuple.
finish_lazard_rational_determinant_transport_ring.
Qed.

Lemma lazard_root_esymm5_scale d (roots : 5.-tuple F) :
  RP.lazard_root_esymm5 (RSA.lazard_scale_quintic_roots d roots) =
    d ^+ 5 * RP.lazard_root_esymm5 roots.
Proof.
rewrite /RP.lazard_root_esymm5 /RSA.lazard_scale_quintic_roots
  !tnth_mktuple.
finish_lazard_rational_determinant_transport_ring.
Qed.

(** The fourth and fifth elementary coordinates of the zero-padded
    canonical tuple.  The second and third coordinates are already exposed
    by [LazardQuinticCanonicalEpsilonNonzero]; these two complete the
    coefficient comparison needed below. *)
Lemma lazard_root_esymm_pad_quintic_ord3 (roots : 5.-tuple F) :
  SNP.root_esymm (QPS.pad_quintic_roots roots) (inord 3) =
    RP.lazard_root_esymm4 roots.
Proof.
rewrite /SNP.root_esymm SNP.six_indicesE /=.
have h0 : (inord 0 : 'I_6) = widen_ord (leqnSn 5) o0.
  apply: val_inj; exact: (@inordK 5 0 isT).
have h1 : (inord 1 : 'I_6) = widen_ord (leqnSn 5) o1.
  apply: val_inj; exact: (@inordK 5 1 isT).
have h2 : (inord 2 : 'I_6) = widen_ord (leqnSn 5) o2.
  apply: val_inj; exact: (@inordK 5 2 isT).
have h3 : (inord 3 : 'I_6) = widen_ord (leqnSn 5) o3.
  apply: val_inj; exact: (@inordK 5 3 isT).
have h4 : (inord 4 : 'I_6) = widen_ord (leqnSn 5) o4.
  apply: val_inj; exact: (@inordK 5 4 isT).
have h5 : (inord 5 : 'I_6) = ord_max.
  apply: val_inj; exact: (@inordK 5 5 isT).
rewrite h0 h1 h2 h3 h4 h5
  !QPS.tnth_pad_quintic_roots_in
  QPS.tnth_pad_quintic_roots_last
  /RP.lazard_root_esymm4.
have hinord3 : nat_of_ord (inord 3 : 'I_6) = 3%N.
  exact: (@inordK 5 3 isT).
rewrite -h3 hinord3 /=.
finish_lazard_rational_determinant_transport_ring.
Qed.

Lemma lazard_root_esymm_pad_quintic_ord4 (roots : 5.-tuple F) :
  SNP.root_esymm (QPS.pad_quintic_roots roots) (inord 4) =
    RP.lazard_root_esymm5 roots.
Proof.
rewrite /SNP.root_esymm SNP.six_indicesE /=.
have h0 : (inord 0 : 'I_6) = widen_ord (leqnSn 5) o0.
  apply: val_inj; exact: (@inordK 5 0 isT).
have h1 : (inord 1 : 'I_6) = widen_ord (leqnSn 5) o1.
  apply: val_inj; exact: (@inordK 5 1 isT).
have h2 : (inord 2 : 'I_6) = widen_ord (leqnSn 5) o2.
  apply: val_inj; exact: (@inordK 5 2 isT).
have h3 : (inord 3 : 'I_6) = widen_ord (leqnSn 5) o3.
  apply: val_inj; exact: (@inordK 5 3 isT).
have h4 : (inord 4 : 'I_6) = widen_ord (leqnSn 5) o4.
  apply: val_inj; exact: (@inordK 5 4 isT).
have h5 : (inord 5 : 'I_6) = ord_max.
  apply: val_inj; exact: (@inordK 5 5 isT).
rewrite h0 h1 h2 h3 h4 h5
  !QPS.tnth_pad_quintic_roots_in
  QPS.tnth_pad_quintic_roots_last
  /RP.lazard_root_esymm5.
have hinord4 : nat_of_ord (inord 4 : 'I_6) = 4%N.
  exact: (@inordK 5 4 isT).
rewrite -h4 hinord4 /=.
finish_lazard_rational_determinant_transport_ring.
Qed.

(** Root dilation and coefficient dilation agree exactly. *)
Theorem lazard_depressed_of_roots_scale d (roots : 5.-tuple F) :
  RP.lazard_depressed_of_roots
      (RSA.lazard_scale_quintic_roots d roots) =
    lazard_scale_depressed_coefficients d
      (RP.lazard_depressed_of_roots roots).
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=.
- exact: lazard_root_esymm2_scale.
- rewrite lazard_root_esymm3_scale.
  finish_lazard_rational_determinant_transport_ring.
- exact: lazard_root_esymm4_scale.
- rewrite lazard_root_esymm5_scale.
  finish_lazard_rational_determinant_transport_ring.
Qed.

(** Row and column factors whose total determinant weight is 30. *)
Definition lazard_invariant_row_scale (d : F) : 'rV[F]_4 :=
  \row_i nth 1 [:: 1; d ^+ 4; d ^+ 8; d ^+ 12] i.

Definition lazard_invariant_column_scale (d : F) : 'rV[F]_4 :=
  \row_i nth 1 [:: d ^+ 3; d ^+ 2; d; 1] i.

Lemma lazard_invariant_system_matrix_scale_entry
    d (c : RP.LazardDepressedRootCoefficients F) row column :
  IS.lazard_invariant_system_matrix
      (lazard_scale_depressed_coefficients d c) row column =
    lazard_invariant_row_scale d 0 row *
      IS.lazard_invariant_system_matrix c row column *
      lazard_invariant_column_scale d 0 column.
Proof.
case: row=> [[|[|[|[|row]]]] hrow] //=;
case: column=> [[|[|[|[|column]]]] hcolumn] //=;
rewrite /IS.lazard_invariant_system_matrix
  /lazard_scale_depressed_coefficients
  /lazard_invariant_row_scale /lazard_invariant_column_scale
  !mxE /=
  /FD.lazard_fifth_printed_i5 /FD.lazard_fifth_printed_i6
  /FD.lazard_fifth_printed_i7 /FD.lazard_fifth_printed_i8;
finish_lazard_rational_determinant_transport_ring.
Qed.

(** Matrix-level homogeneous factorization. *)
Theorem lazard_invariant_system_matrix_scale
    d (c : RP.LazardDepressedRootCoefficients F) :
  IS.lazard_invariant_system_matrix
      (lazard_scale_depressed_coefficients d c) =
    diag_mx (lazard_invariant_row_scale d) *m
      IS.lazard_invariant_system_matrix c *m
      diag_mx (lazard_invariant_column_scale d).
Proof.
rewrite mul_diag_mx mul_mx_diag.
apply/matrixP=> row column.
rewrite !mxE.
exact: lazard_invariant_system_matrix_scale_entry.
Qed.

(** The literal Figure-3 determinant is homogeneous of total weight 30. *)
Theorem lazard_invariant_system_matrix_det_scale
    d (c : RP.LazardDepressedRootCoefficients F) :
  \det (IS.lazard_invariant_system_matrix
      (lazard_scale_depressed_coefficients d c)) =
    d ^+ 30 * \det (IS.lazard_invariant_system_matrix c).
Proof.
rewrite lazard_invariant_system_matrix_scale !det_mulmx !det_diag
  /lazard_invariant_row_scale /lazard_invariant_column_scale
  !big_ord_recl !big_ord0 !mxE /=.
finish_lazard_rational_determinant_transport_ring.
Qed.

(** Nonvanishing descends through every dilation.  Notice that this
    implication itself does not require [d != 0]: if the scaled determinant
    is nonzero, the weight-30 identity already forces the original one to be
    nonzero. *)
Corollary lazard_invariant_system_matrix_det_neq0_of_scaled
    d (c : RP.LazardDepressedRootCoefficients F)
    (hscaled : \det (IS.lazard_invariant_system_matrix
      (lazard_scale_depressed_coefficients d c)) != 0) :
  \det (IS.lazard_invariant_system_matrix c) != 0.
Proof.
apply/eqP=> hzero.
move: hscaled.
by rewrite lazard_invariant_system_matrix_det_scale hzero mulr0 eqxx.
Qed.

End HomogeneousTransport.

Section ScalarExtensionTransport.

Variables F E : fieldType.
Variable phi : {rmorphism F -> E}.

Add Ring lazard_rational_determinant_extension_ring :
  (@NR.lazard_numerator_ring_theory E).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_rational_determinant_extension_ring :=
  lazard_numerator_prepare;
  repeat first [rewrite exprS | rewrite expr0];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_depressed_coefficients_map_scale d
    (c : RP.LazardDepressedRootCoefficients F) :
  lazard_depressed_coefficients_map phi
      (lazard_scale_depressed_coefficients d c) =
    lazard_scale_depressed_coefficients (phi d)
      (lazard_depressed_coefficients_map phi c).
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=;
by rewrite rmorphM rmorphXn.
Qed.

(** The literal Figure-3 matrix commutes with scalar extension. *)
Theorem lazard_invariant_system_matrix_map
    (c : RP.LazardDepressedRootCoefficients F) :
  IS.lazard_invariant_system_matrix
      (lazard_depressed_coefficients_map phi c) =
    map_mx phi (IS.lazard_invariant_system_matrix c).
Proof.
apply/matrixP=> row column.
case: row=> [[|[|[|[|row]]]] hrow] //=;
case: column=> [[|[|[|[|column]]]] hcolumn] //=;
rewrite /IS.lazard_invariant_system_matrix
  /lazard_depressed_coefficients_map !mxE /=
  /FD.lazard_fifth_printed_i5 /FD.lazard_fifth_printed_i6
  /FD.lazard_fifth_printed_i7 /FD.lazard_fifth_printed_i8;
repeat first
  [ rewrite rmorphD | rewrite rmorphB | rewrite rmorphM
  | rewrite rmorphN | rewrite rmorphXn | rewrite rmorph_nat
  | rewrite rmorph0 | rewrite rmorph1 | rewrite fmorph_div ];
finish_lazard_rational_determinant_extension_ring.
Qed.

(** Determinants commute with the same extension. *)
Corollary lazard_invariant_system_det_map
    (c : RP.LazardDepressedRootCoefficients F) :
  \det (IS.lazard_invariant_system_matrix
      (lazard_depressed_coefficients_map phi c)) =
    phi (\det (IS.lazard_invariant_system_matrix c)).
Proof.
rewrite lazard_invariant_system_matrix_map det_map_mx.
reflexivity.
Qed.

End ScalarExtensionTransport.

Section ArbitraryRationalDepressedQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_monic : p \is monic.

Let f : QRF.monic_quintic := RSA.lazard_quintic_integer_data p.
Let pD : {poly rat} := RSA.lazard_quintic_scaled_polynomial p.
Let pD_size : size pD = 6%N := CD.size_rational_monic_quintic f.
Let D : rat := (RSA.lazard_quintic_common_denominator p)%:~R.
Let L : splittingFieldType rat := numfield pD.
Let rootsD : 5.-tuple L := @GA.quintic_root_tuple pD pD_size.

(** A complete root tuple for [p] in the splitting field of its integral
    dilation.  This is definitionally the tuple constructed by the rational
    scaling adapter. *)
Definition lazard_rational_original_roots : 5.-tuple L :=
  RSA.lazard_scale_quintic_roots ((in_alg L D)^-1) rootsD.

(** The literal four lower coefficients of the original depressed monic
    quintic.  The [X^4] coefficient is omitted because depression proves it
    is zero. *)
Definition lazard_rational_polynomial_depressed_coefficients :
    RP.LazardDepressedRootCoefficients rat :=
  {| RP.lazard_root_p := p`_3;
     RP.lazard_root_q := p`_2;
     RP.lazard_root_r := p`_1;
     RP.lazard_root_s := p`_0 |}.

(** The integral tuple used by the executable quintic is exactly the image
    of the lower coefficients of [pD]. *)
Lemma lazard_rational_scaled_coefficient_map (i : 'I_5) :
  in_alg L (pD`_i) = ((tnth f i)%:~R : L).
Proof.
rewrite /pD RSA.lazard_quintic_scaled_polynomial_coef_lower.
rewrite /f RSA.lazard_quintic_integer_dataE.
by rewrite rmorph_int.
Qed.

(** Four coordinate forms of canonical Vieta, stated directly against the
    coefficients of the scaled polynomial. *)
Lemma lazard_canonical_root_esymm2_coefE :
  RP.lazard_root_esymm2 rootsD = in_alg L (pD`_3).
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values (inord 1))
  (@CD.canonical_quintic_padded_vieta f).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values CE.lazard_root_esymm_pad_quintic_ord1 in hv.
have hcoef := lazard_rational_scaled_coefficient_map (inord 3).
rewrite (@inordK 4 3 isT) in hcoef.
rewrite -hv hcoef /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  f (i := 4%N) isT) /=.
by rewrite -(tnth_nth 0).
Qed.

Lemma lazard_canonical_root_neg_esymm3_coefE :
  - RP.lazard_root_esymm3 rootsD = in_alg L (pD`_2).
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values (inord 2))
  (@CD.canonical_quintic_padded_vieta f).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values CE.lazard_root_esymm_pad_quintic_ord2 in hv.
have hcoef := lazard_rational_scaled_coefficient_map (inord 2).
rewrite (@inordK 4 2 isT) in hcoef.
rewrite -hv hcoef /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  f (i := 3%N) isT) /= rmorphN opprK.
by rewrite -(tnth_nth 0).
Qed.

Lemma lazard_canonical_root_esymm4_coefE :
  RP.lazard_root_esymm4 rootsD = in_alg L (pD`_1).
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values (inord 3))
  (@CD.canonical_quintic_padded_vieta f).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_root_esymm_pad_quintic_ord3 in hv.
have hcoef := lazard_rational_scaled_coefficient_map (inord 1).
rewrite (@inordK 4 1 isT) in hcoef.
rewrite -hv hcoef /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  f (i := 2%N) isT) /=.
by rewrite -(tnth_nth 0).
Qed.

Lemma lazard_canonical_root_neg_esymm5_coefE :
  - RP.lazard_root_esymm5 rootsD = in_alg L (pD`_0).
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values (inord 4))
  (@CD.canonical_quintic_padded_vieta f).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_root_esymm_pad_quintic_ord4 in hv.
have hcoef := lazard_rational_scaled_coefficient_map (inord 0).
rewrite (@inordK 4 0 isT) in hcoef.
rewrite -hv hcoef /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  f (i := 1%N) isT) /= rmorphN opprK.
by rewrite -(tnth_nth 0).
Qed.

Lemma lazard_rational_original_roots_sound k :
  root (map_poly (in_alg L) p)
    (tnth lazard_rational_original_roots k).
Proof.
exact: (@RSA.lazard_quintic_rescaled_canonical_roots_sound
  p p_size p_monic k).
Qed.

Lemma lazard_rational_original_roots_complete z :
  root (map_poly (in_alg L) p) z ->
  exists k : 'I_5, z = tnth lazard_rational_original_roots k.
Proof.
exact: (@RSA.lazard_quintic_rescaled_canonical_roots_complete
  p p_size p_monic z).
Qed.

Lemma lazard_rational_scale_original_rootsE :
  RSA.lazard_scale_quintic_roots (in_alg L D)
      lazard_rational_original_roots = rootsD.
Proof.
have hD : in_alg L D != 0.
  by rewrite fmorph_eq0
    RSA.lazard_quintic_common_denominator_cast_neq0.
apply: eq_from_tnth=> i.
rewrite /lazard_rational_original_roots
  /RSA.lazard_scale_quintic_roots !tnth_mktuple
  mulrA mulfV // mul1r.
by [].
Qed.

(** Canonical Vieta and the coefficient-scaling identity identify the
    root-derived record for [pD] with the weightwise dilation of the literal
    coefficient record of [p]. *)
Lemma lazard_canonical_depressed_coefficientsE :
  RP.lazard_depressed_of_roots rootsD =
    lazard_scale_depressed_coefficients (in_alg L D)
      (lazard_depressed_coefficients_map (in_alg L)
        lazard_rational_polynomial_depressed_coefficients).
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=.
- rewrite lazard_canonical_root_esymm2_coefE.
  have hcoef := @RSA.lazard_quintic_scaled_coefficient_identity
    p p_size p_monic (inord 3).
  rewrite (@inordK 5 3 isT) in hcoef.
  rewrite hcoef rmorphM rmorphXn /=.
  by rewrite mulrC.
- rewrite lazard_canonical_root_neg_esymm3_coefE.
  have hcoef := @RSA.lazard_quintic_scaled_coefficient_identity
    p p_size p_monic (inord 2).
  rewrite (@inordK 5 2 isT) in hcoef.
  rewrite hcoef rmorphM rmorphXn /=.
  by rewrite mulrC.
- rewrite lazard_canonical_root_esymm4_coefE.
  have hcoef := @RSA.lazard_quintic_scaled_coefficient_identity
    p p_size p_monic (inord 1).
  rewrite (@inordK 5 1 isT) in hcoef.
  rewrite hcoef rmorphM rmorphXn /=.
  by rewrite mulrC.
- rewrite lazard_canonical_root_neg_esymm5_coefE.
  have hcoef := @RSA.lazard_quintic_scaled_coefficient_identity
    p p_size p_monic (inord 0).
  rewrite (@inordK 5 0 isT) in hcoef.
  rewrite hcoef rmorphM rmorphXn /=.
  by rewrite mulrC.
Qed.

(** Exact base-coefficient bridge.  Thus the determinant below is not only
    attached to a complete root tuple: it is the determinant of the four
    coefficients appearing literally in the caller's rational polynomial. *)
Theorem lazard_rational_original_coefficients_mapE :
  lazard_depressed_coefficients_map (in_alg L)
      lazard_rational_polynomial_depressed_coefficients =
    RP.lazard_depressed_of_roots lazard_rational_original_roots.
Proof.
have hD : in_alg L D != 0.
  by rewrite fmorph_eq0
    RSA.lazard_quintic_common_denominator_cast_neq0.
apply: (lazard_scale_depressed_coefficients_injective hD).
rewrite -lazard_canonical_depressed_coefficientsE.
rewrite -lazard_depressed_of_roots_scale
  lazard_rational_scale_original_rootsE.
reflexivity.
Qed.

Lemma lazard_canonical_selected_roots_ord0E :
  @ID.lazard_selected_roots f ord0 = rootsD.
Proof.
by rewrite /ID.lazard_selected_roots
  /F20.representative /F20.representative_table /=
  invg1 TV.permute_quintic_roots_one.
Qed.

(** Depression of [p] supplies the zero-sum relation for the original,
    rescaled root tuple; it is not an interface certificate. *)
Theorem lazard_rational_original_roots_esymm1_zero
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  RP.lazard_root_esymm1 lazard_rational_original_roots = 0.
Proof.
have hcanonical_depressed : @CE.lazard_canonical_quintic_depressed f :=
  @RSA.lazard_quintic_integer_data_canonical_depressed
    p p_size p_monic p_depressed.
have hsumD : RP.lazard_root_esymm1 rootsD = 0.
  rewrite -lazard_canonical_selected_roots_ord0E.
  exact: CE.lazard_selected_root_esymm1_zero
    hcanonical_depressed ord0.
have hscale := @lazard_root_esymm1_scale L (in_alg L D)
  lazard_rational_original_roots.
rewrite lazard_rational_scale_original_rootsE hsumD in hscale.
have hproduct :
    in_alg L D *
      RP.lazard_root_esymm1 lazard_rational_original_roots = 0 :=
  esym hscale.
have hD : in_alg L D != 0.
  by rewrite fmorph_eq0
    RSA.lazard_quintic_common_denominator_cast_neq0.
apply/eqP.
move/eqP: hproduct.
by rewrite mulf_eq0 (negPf hD) orFb.
Qed.

(** Arbitrary-rational version of the canonical determinant endpoint.
    The only mathematical hypotheses are degree five, monicity,
    irreducibility, and depression.  In particular there is no supplied
    resolvent-separability or determinant premise. *)
Theorem lazard_rational_monic_depressed_invariant_system_det_neq0
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  \det (IS.lazard_invariant_system_matrix
    (RP.lazard_depressed_of_roots lazard_rational_original_roots)) != 0.
Proof.
have hpDirr : irreducible_poly pD.
  exact: (proj2 (@RSA.lazard_quintic_scaled_irreducible_iff
    p p_size p_monic)) p_irr.
have hcanonical_depressed : @CE.lazard_canonical_quintic_depressed f :=
  @RSA.lazard_quintic_integer_data_canonical_depressed
    p p_size p_monic p_depressed.
have hdetD := @DE.canonical_lazard_invariant_system_matrix_det_neq0
  f hpDirr hcanonical_depressed.
rewrite -lazard_rational_scale_original_rootsE
  lazard_depressed_of_roots_scale in hdetD.
exact: lazard_invariant_system_matrix_det_neq0_of_scaled hdetD.
Qed.

(** Coefficient-level arbitrary-rational endpoint.  Scalar extension
    commutes with the literal matrix and its determinant, so nonvanishing in
    [L] reflects to the determinant over [rat]. *)
Theorem lazard_rational_monic_depressed_base_invariant_system_det_neq0
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  \det (IS.lazard_invariant_system_matrix
    lazard_rational_polynomial_depressed_coefficients) != 0.
Proof.
have hdet := lazard_rational_monic_depressed_invariant_system_det_neq0
  p_irr p_depressed.
rewrite -lazard_rational_original_coefficients_mapE in hdet.
rewrite lazard_invariant_system_det_map in hdet.
by move: hdet; rewrite fmorph_eq0.
Qed.

(** The same uniqueness statement entirely over the caller's rational
    coefficient field. *)
Theorem lazard_rational_monic_depressed_base_invariants_unique_from_i4
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p)
    (i j : RP.LazardRootInvariants rat)
    (hi : F5.lazard_invariant_relations
      lazard_rational_polynomial_depressed_coefficients i)
    (hj : F5.lazard_invariant_relations
      lazard_rational_polynomial_depressed_coefficients j)
    (hi4 : RP.lazard_root_i4 i = RP.lazard_root_i4 j) :
  i = j.
Proof.
exact: IS.lazard_invariant_relations_eq_of_i4_eq_of_det_neq0
  hi hj hi4
  (lazard_rational_monic_depressed_base_invariant_system_det_neq0
    p_irr p_depressed).
Qed.

(** Root-origin Figure-3 uniqueness for an arbitrary rational monic
    depressed irreducible quintic.  The relation package for the actual
    roots, their zero sum, and determinant nonvanishing are all derived
    internally. *)
Theorem lazard_rational_monic_depressed_root_invariants_unique_from_i4
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p)
    (j : RP.LazardRootInvariants L)
    (hj : F5.lazard_invariant_relations
      (RP.lazard_depressed_of_roots lazard_rational_original_roots) j)
    (hi4 : RP.lazard_root_i4
        (RP.lazard_root_invariants lazard_rational_original_roots) =
      RP.lazard_root_i4 j) :
  RP.lazard_root_invariants lazard_rational_original_roots = j.
Proof.
apply: IS.lazard_root_invariants_unique_from_i4.
- by rewrite pnatr_eq0.
- exact: lazard_rational_original_roots_esymm1_zero p_depressed.
- exact: hj.
- exact: hi4.
- exact: lazard_rational_monic_depressed_invariant_system_det_neq0
    p_irr p_depressed.
Qed.

(** Fully root-origin version: a second ordering with the same depressed
    coefficient record is forced to have the same complete invariant tuple
    once its [i4] agrees. *)
Theorem lazard_rational_monic_depressed_root_invariants_eq_of_i4_eq
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p)
    (other : 5.-tuple L)
    (hother_sum : RP.lazard_root_esymm1 other = 0)
    (hother_coefficients :
      RP.lazard_depressed_of_roots other =
        RP.lazard_depressed_of_roots lazard_rational_original_roots)
    (hi4 : RP.lazard_root_i4
        (RP.lazard_root_invariants lazard_rational_original_roots) =
      RP.lazard_root_i4 (RP.lazard_root_invariants other)) :
  RP.lazard_root_invariants lazard_rational_original_roots =
    RP.lazard_root_invariants other.
Proof.
apply: lazard_rational_monic_depressed_root_invariants_unique_from_i4
  p_irr p_depressed.
- rewrite -hother_coefficients.
  exact: F5.lazard_root_invariant_relations
    (by rewrite pnatr_eq0) hother_sum.
- exact: hi4.
Qed.

(** A single public package exposing both conclusions. *)
Theorem lazard_rational_monic_depressed_section_seven_determinant_and_uniqueness
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  \det (IS.lazard_invariant_system_matrix
      (RP.lazard_depressed_of_roots lazard_rational_original_roots)) != 0 /\
    forall j : RP.LazardRootInvariants L,
      F5.lazard_invariant_relations
          (RP.lazard_depressed_of_roots lazard_rational_original_roots) j ->
      RP.lazard_root_i4
          (RP.lazard_root_invariants lazard_rational_original_roots) =
        RP.lazard_root_i4 j ->
      RP.lazard_root_invariants lazard_rational_original_roots = j.
Proof.
split.
- exact: lazard_rational_monic_depressed_invariant_system_det_neq0
    p_irr p_depressed.
- move=> j hj hi4.
  exact: lazard_rational_monic_depressed_root_invariants_unique_from_i4
    p_irr p_depressed hj hi4.
Qed.

(** Coefficient-level public package matching the arbitrary-rational scope
    of the input polynomial. *)
Theorem
    lazard_rational_monic_depressed_base_section_seven_determinant_and_uniqueness
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  \det (IS.lazard_invariant_system_matrix
      lazard_rational_polynomial_depressed_coefficients) != 0 /\
    forall i j : RP.LazardRootInvariants rat,
      F5.lazard_invariant_relations
          lazard_rational_polynomial_depressed_coefficients i ->
      F5.lazard_invariant_relations
          lazard_rational_polynomial_depressed_coefficients j ->
      RP.lazard_root_i4 i = RP.lazard_root_i4 j ->
      i = j.
Proof.
split.
- exact: lazard_rational_monic_depressed_base_invariant_system_det_neq0
    p_irr p_depressed.
- move=> i j hi hj hi4.
  exact: lazard_rational_monic_depressed_base_invariants_unique_from_i4
    p_irr p_depressed hi hj hi4.
Qed.

End ArbitraryRationalDepressedQuintic.

Print Assumptions lazard_depressed_of_roots_scale.
Print Assumptions lazard_invariant_system_matrix_det_scale.
Print Assumptions lazard_invariant_system_matrix_map.
Print Assumptions lazard_invariant_system_det_map.
Print Assumptions
  lazard_rational_monic_depressed_invariant_system_det_neq0.
Print Assumptions lazard_rational_original_coefficients_mapE.
Print Assumptions
  lazard_rational_monic_depressed_base_invariant_system_det_neq0.
Print Assumptions
  lazard_rational_monic_depressed_base_invariants_unique_from_i4.
Print Assumptions
  lazard_rational_monic_depressed_root_invariants_unique_from_i4.
Print Assumptions
  lazard_rational_monic_depressed_section_seven_determinant_and_uniqueness.
Print Assumptions
  lazard_rational_monic_depressed_base_section_seven_determinant_and_uniqueness.

End PolynomialFormulasLazardQuinticRationalDeterminantTransport.
