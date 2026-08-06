From Stdlib Require Import Arith Lia List Vector ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.MuRec.Util Require Import recalg recomp ra_recomp.
From PolynomialFormulas Require Import
  SexticMuRecComputability SexticRecursiveCore
  SexticArithmeticFactorSearch QuinticRecursiveFactor
  QuinticArithmeticFactorSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecFactorDecision.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SAF := PolynomialFormulasSexticArithmeticFactorSearch.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QAF := PolynomialFormulasQuinticArithmeticFactorSearch.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(** The common MathComp interpretation of subtraction in the signed
    expression language. *)
Lemma eval_mathcomp_signed_minus {arity}
    (left right : signed_expression arity) values :
  eval_mathcomp_signed_expression (signed_minus left right) values =
  eval_mathcomp_signed_expression left values -
    eval_mathcomp_signed_expression right values.
Proof.
rewrite /signed_minus eval_mathcomp_signed_plus
  eval_mathcomp_signed_negate.
reflexivity.
Qed.

Lemma eval_signed_zero_indicator_mathcomp_iff {arity}
    (expression : signed_expression arity) values :
  eval_nat_expression (signed_zero_indicator_expression expression) values
      <> 0 <->
  eval_mathcomp_signed_expression expression values = 0.
Proof.
rewrite eval_signed_zero_indicator_nonzero_iff.
exact: signed_zero_mathcomp_iff.
Qed.

(** Ascending lower coefficients of a monic sextic, encoded independently
    by the proved zigzag coding. *)
Definition encode_monic_sextic_coefficients
    (f : SRC.monic_sextic) : Vector.t nat 6 :=
  mathcomp_zigzag_encode f`_0 ##
  mathcomp_zigzag_encode f`_1 ##
  mathcomp_zigzag_encode f`_2 ##
  mathcomp_zigzag_encode f`_3 ##
  mathcomp_zigzag_encode f`_4 ##
  mathcomp_zigzag_encode f`_5 ## vec_nil.

Lemma encoded_monic_sextic_height_mathcomp
    (f : SRC.monic_sextic) :
  encoded_monic_sextic_height (encode_monic_sextic_coefficients f) =
    SRC.height f.
Proof.
rewrite /encoded_monic_sextic_height /SRC.height
  /encode_monic_sextic_coefficients.
rewrite !mathcomp_zigzag_magnitude_encode.
reflexivity.
Qed.

Lemma encoded_monic_sextic_root_bound_mathcomp
    (f : SRC.monic_sextic) :
  encoded_monic_sextic_root_bound
      (encode_monic_sextic_coefficients f) = SRC.root_bound f.
Proof.
by rewrite /encoded_monic_sextic_root_bound /SRC.root_bound
  encoded_monic_sextic_height_mathcomp.
Qed.

Lemma eval_mathcomp_monic_linear_candidate index (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_linear_candidate_expression
    (index ## encode_monic_sextic_coefficients f) =
  (index%:Z - (SRC.root_bound f)%:Z : int).
Proof.
rewrite /encoded_monic_linear_candidate_expression
  eval_mathcomp_signed_minus !eval_mathcomp_signed_of_nat_expression.
rewrite eval_encoded_monic_linear_body_root_bound_expression
  encoded_monic_sextic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_linear_q4 index (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_linear_q4_expression
    (index ## encode_monic_sextic_coefficients f) =
  SRC.linear_q4 f (index%:Z - (SRC.root_bound f)%:Z).
Proof.
rewrite /encoded_monic_linear_q4_expression /SRC.linear_q4
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_monic_linear_candidate.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_linear_q3 index (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_linear_q3_expression
    (index ## encode_monic_sextic_coefficients f) =
  SRC.linear_q3 f (index%:Z - (SRC.root_bound f)%:Z).
Proof.
rewrite /encoded_monic_linear_q3_expression /SRC.linear_q3
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_linear_candidate
  eval_mathcomp_monic_linear_q4.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_linear_q2 index (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_linear_q2_expression
    (index ## encode_monic_sextic_coefficients f) =
  SRC.linear_q2 f (index%:Z - (SRC.root_bound f)%:Z).
Proof.
rewrite /encoded_monic_linear_q2_expression /SRC.linear_q2
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_linear_candidate
  eval_mathcomp_monic_linear_q3.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_linear_q1 index (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_linear_q1_expression
    (index ## encode_monic_sextic_coefficients f) =
  SRC.linear_q1 f (index%:Z - (SRC.root_bound f)%:Z).
Proof.
rewrite /encoded_monic_linear_q1_expression /SRC.linear_q1
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_linear_candidate
  eval_mathcomp_monic_linear_q2.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_linear_q0 index (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_linear_q0_expression
    (index ## encode_monic_sextic_coefficients f) =
  SRC.linear_q0 f (index%:Z - (SRC.root_bound f)%:Z).
Proof.
rewrite /encoded_monic_linear_q0_expression /SRC.linear_q0
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_linear_candidate
  eval_mathcomp_monic_linear_q1.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_linear_remainder index (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_linear_remainder_expression
    (index ## encode_monic_sextic_coefficients f) =
  f`_0 - (index%:Z - (SRC.root_bound f)%:Z) *
    SRC.linear_q0 f (index%:Z - (SRC.root_bound f)%:Z).
Proof.
rewrite /encoded_monic_linear_remainder_expression
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_linear_candidate
  eval_mathcomp_monic_linear_q0.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_encoded_monic_linear_zero_mathcomp index
    (f : SRC.monic_sextic) :
  eval_nat_expression encoded_monic_linear_remainder_zero_expression
      (index ## encode_monic_sextic_coefficients f) <> 0 <->
  SRC.linear_remainder_zerob f
      (index%:Z - (SRC.root_bound f)%:Z) = true.
Proof.
rewrite /encoded_monic_linear_remainder_zero_expression
  eval_signed_zero_indicator_mathcomp_iff
  eval_mathcomp_monic_linear_remainder.
rewrite /SRC.linear_remainder_zerob.
split.
- move=> h.
  have hz :
      f`_0 - (index%:Z - (SRC.root_bound f)%:Z) *
          SRC.linear_q0 f (index%:Z - (SRC.root_bound f)%:Z) == 0.
    exact/eqP.
  by move: hz; rewrite subr_eq0.
- move=> h.
  have hz :
      f`_0 - (index%:Z - (SRC.root_bound f)%:Z) *
          SRC.linear_q0 f (index%:Z - (SRC.root_bound f)%:Z) == 0.
    by rewrite subr_eq0.
  exact/eqP.
Qed.

Lemma encoded_monic_linear_remainder_mathcomp_iff index
    (f : SRC.monic_sextic) :
  encoded_monic_linear_remainder
      (encode_monic_sextic_coefficients f) index = Z0 <->
  SRC.linear_remainder_zerob f
      (index%:Z - (SRC.root_bound f)%:Z) = true.
Proof.
rewrite -eval_encoded_monic_linear_remainder_zero_nonzero_iff.
exact: eval_encoded_monic_linear_zero_mathcomp.
Qed.

Lemma encoded_monic_linear_factor_mathcomp_iff (f : SRC.monic_sextic) :
  encoded_monic_has_bounded_linear_factor
      (encode_monic_sextic_coefficients f) <->
  SAF.has_arithmetic_linear_factor f = true.
Proof.
rewrite /encoded_monic_has_bounded_linear_factor
  encoded_monic_sextic_root_bound_mathcomp
  /SAF.has_arithmetic_linear_factor.
split.
- move=> [index [Hindex Hzero]].
  apply/hasP.
  exists (index%:Z - (SRC.root_bound f)%:Z).
  + apply/(SRC.mem_symmetric_interval _ _).
    exists index; split=> //.
    exact/ltP.
  + exact/(encoded_monic_linear_remainder_mathcomp_iff index f).
- move/hasP=> [candidate Hcandidate Hzero].
  move/(SRC.mem_symmetric_interval _ _): Hcandidate=>
    [index [Hindex Hcandidate]].
  exists index; split.
  + exact/ltP.
  + apply/(encoded_monic_linear_remainder_mathcomp_iff index f).
    by rewrite -Hcandidate.
Qed.

(** The quadratic search enumerates [b] in radius [2R] and [c] in
    radius [R^2].  Naming these candidates keeps the semantic bridge
    independent of the implementation's de Bruijn positions. *)
Definition sextic_quadratic_b_candidate (f : SRC.monic_sextic)
    (index : nat) : int :=
  index%:Z - (2 * SRC.root_bound f)%:Z.

Definition sextic_quadratic_c_candidate (f : SRC.monic_sextic)
    (index : nat) : int :=
  index%:Z - (SRC.root_bound f * SRC.root_bound f)%:Z.

Lemma eval_mathcomp_monic_quadratic_b c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_quadratic_b_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  sextic_quadratic_b_candidate f b_index.
Proof.
rewrite /encoded_monic_quadratic_b_expression
  /encoded_monic_quadratic_b_radius_body_expression
  /signed_symmetric_candidate /sextic_quadratic_b_candidate
  eval_mathcomp_signed_minus !eval_mathcomp_signed_of_nat_expression.
cbn [eval_nat_expression].
rewrite eval_encoded_monic_quadratic_body_root_bound_expression
  encoded_monic_sextic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quadratic_c c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_quadratic_c_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  sextic_quadratic_c_candidate f c_index.
Proof.
rewrite /encoded_monic_quadratic_c_expression
  /encoded_monic_quadratic_c_radius_body_expression
  /signed_symmetric_candidate /sextic_quadratic_c_candidate
  eval_mathcomp_signed_minus !eval_mathcomp_signed_of_nat_expression.
cbn [eval_nat_expression].
rewrite !eval_encoded_monic_quadratic_body_root_bound_expression
  encoded_monic_sextic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quadratic_q3 c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_quadratic_q3_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  SRC.quadratic_q3 f (sextic_quadratic_b_candidate f b_index).
Proof.
rewrite /encoded_monic_quadratic_q3_expression /SRC.quadratic_q3
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_monic_quadratic_b.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quadratic_q2 c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_quadratic_q2_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  SRC.quadratic_q2 f (sextic_quadratic_b_candidate f b_index)
    (sextic_quadratic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_quadratic_q2_expression /SRC.quadratic_q2
  eval_mathcomp_signed_minus eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_quadratic_b
  eval_mathcomp_monic_quadratic_c eval_mathcomp_monic_quadratic_q3.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quadratic_q1 c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_quadratic_q1_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  SRC.quadratic_q1 f (sextic_quadratic_b_candidate f b_index)
    (sextic_quadratic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_quadratic_q1_expression /SRC.quadratic_q1
  eval_mathcomp_signed_minus eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient
  !eval_mathcomp_signed_mult eval_mathcomp_monic_quadratic_b
  eval_mathcomp_monic_quadratic_c eval_mathcomp_monic_quadratic_q2
  eval_mathcomp_monic_quadratic_q3.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quadratic_q0 c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_quadratic_q0_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  SRC.quadratic_q0 f (sextic_quadratic_b_candidate f b_index)
    (sextic_quadratic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_quadratic_q0_expression /SRC.quadratic_q0
  eval_mathcomp_signed_minus eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient
  !eval_mathcomp_signed_mult eval_mathcomp_monic_quadratic_b
  eval_mathcomp_monic_quadratic_c eval_mathcomp_monic_quadratic_q1
  eval_mathcomp_monic_quadratic_q2.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quadratic_remainder1 c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression
      encoded_monic_quadratic_remainder1_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  f`_1 -
    (sextic_quadratic_b_candidate f b_index *
       SRC.quadratic_q0 f (sextic_quadratic_b_candidate f b_index)
         (sextic_quadratic_c_candidate f c_index) +
     sextic_quadratic_c_candidate f c_index *
       SRC.quadratic_q1 f (sextic_quadratic_b_candidate f b_index)
         (sextic_quadratic_c_candidate f c_index)).
Proof.
rewrite /encoded_monic_quadratic_remainder1_expression
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_plus !eval_mathcomp_signed_mult
  eval_mathcomp_monic_quadratic_b eval_mathcomp_monic_quadratic_c
  eval_mathcomp_monic_quadratic_q0 eval_mathcomp_monic_quadratic_q1.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quadratic_remainder0 c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression
      encoded_monic_quadratic_remainder0_expression
      (c_index ## b_index ## encode_monic_sextic_coefficients f) =
  f`_0 - sextic_quadratic_c_candidate f c_index *
    SRC.quadratic_q0 f (sextic_quadratic_b_candidate f b_index)
      (sextic_quadratic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_quadratic_remainder0_expression
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_quadratic_c
  eval_mathcomp_monic_quadratic_q0.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma encoded_monic_quadratic_remainders_mathcomp_iff c_index b_index
    (f : SRC.monic_sextic) :
  encoded_monic_quadratic_remainder1
      (encode_monic_sextic_coefficients f) b_index c_index = Z0 /\
  encoded_monic_quadratic_remainder0
      (encode_monic_sextic_coefficients f) b_index c_index = Z0 <->
  SRC.quadratic_remainder_zerob f
    (sextic_quadratic_b_candidate f b_index)
    (sextic_quadratic_c_candidate f c_index) = true.
Proof.
rewrite -eval_encoded_monic_quadratic_remainder1_expression
  -eval_encoded_monic_quadratic_remainder0_expression
  !signed_zero_mathcomp_iff
  eval_mathcomp_monic_quadratic_remainder1
  eval_mathcomp_monic_quadratic_remainder0.
split.
- move=> [h1 h0].
  apply/SRC.quadratic_remainder_zeroP.
  split; exact: subr0_eq.
- move/SRC.quadratic_remainder_zeroP=> [h1 h0].
  split; by [rewrite h1 subrr | rewrite h0 subrr].
Qed.

Lemma sextic_quadratic_c_candidateE (f : SRC.monic_sextic) index :
  sextic_quadratic_c_candidate f index =
    index%:Z - (expn (SRC.root_bound f) 2)%:Z.
Proof.
rewrite /sextic_quadratic_c_candidate.
have -> : muln (SRC.root_bound f) (SRC.root_bound f) =
    expn (SRC.root_bound f) 2
  by rewrite expnS expn1.
reflexivity.
Qed.

Lemma encoded_monic_quadratic_factor_mathcomp_iff
    (f : SRC.monic_sextic) :
  encoded_monic_has_bounded_quadratic_factor
      (encode_monic_sextic_coefficients f) <->
  SAF.has_arithmetic_quadratic_factor f = true.
Proof.
rewrite /encoded_monic_has_bounded_quadratic_factor
  encoded_monic_sextic_root_bound_mathcomp
  /SAF.has_arithmetic_quadratic_factor.
split.
- move=> [b_index [Hb [c_index [Hc Hremainders]]]].
  apply/hasP.
  exists (sextic_quadratic_b_candidate f b_index).
  + apply/(SRC.mem_symmetric_interval _ _).
    exists b_index; split.
    * exact/ltP.
    * reflexivity.
  + apply/hasP.
    exists (sextic_quadratic_c_candidate f c_index).
    * apply/(SRC.mem_symmetric_interval _ _).
      exists c_index; split.
      -- exact/ltP.
      -- exact: sextic_quadratic_c_candidateE.
    * exact/(encoded_monic_quadratic_remainders_mathcomp_iff
        c_index b_index f).
- move/hasP=> [b Hbmem Hinner].
  move/hasP: Hinner=> [c Hcmem Hremainders].
  have [b_index [Hb Hbeq]] :=
    (proj1 (SRC.mem_symmetric_interval _ b)) Hbmem.
  have [c_index [Hc Hceq]] :=
    (proj1 (SRC.mem_symmetric_interval _ c)) Hcmem.
  exists b_index; split.
  + exact/ltP.
  + exists c_index; split.
    * exact/ltP.
    * apply/(encoded_monic_quadratic_remainders_mathcomp_iff
        c_index b_index f).
      rewrite /sextic_quadratic_b_candidate
        sextic_quadratic_c_candidateE -Hbeq -Hceq.
      exact Hremainders.
Qed.

(** Cubic candidates use the coefficient bounds [3R], [3R^2], and
    [R^3] from the semantic factor search. *)
Definition sextic_cubic_b_candidate (f : SRC.monic_sextic)
    (index : nat) : int :=
  index%:Z - (3 * SRC.root_bound f)%:Z.

Definition sextic_cubic_c_candidate (f : SRC.monic_sextic)
    (index : nat) : int :=
  index%:Z -
    (3 * SRC.root_bound f * SRC.root_bound f)%:Z.

Definition sextic_cubic_d_candidate (f : SRC.monic_sextic)
    (index : nat) : int :=
  index%:Z -
    (SRC.root_bound f * SRC.root_bound f * SRC.root_bound f)%:Z.

Lemma eval_mathcomp_monic_cubic_b d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_b_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  sextic_cubic_b_candidate f b_index.
Proof.
rewrite /encoded_monic_cubic_b_expression
  /encoded_monic_cubic_b_radius_body_expression
  /signed_symmetric_candidate /sextic_cubic_b_candidate
  eval_mathcomp_signed_minus !eval_mathcomp_signed_of_nat_expression.
cbn [eval_nat_expression].
rewrite eval_encoded_monic_cubic_body_root_bound_expression
  encoded_monic_sextic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_c d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_c_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  sextic_cubic_c_candidate f c_index.
Proof.
rewrite /encoded_monic_cubic_c_expression
  /encoded_monic_cubic_c_radius_body_expression
  /signed_symmetric_candidate /sextic_cubic_c_candidate
  eval_mathcomp_signed_minus !eval_mathcomp_signed_of_nat_expression.
cbn [eval_nat_expression].
rewrite !eval_encoded_monic_cubic_body_root_bound_expression
  encoded_monic_sextic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_d d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_d_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  sextic_cubic_d_candidate f d_index.
Proof.
rewrite /encoded_monic_cubic_d_expression
  /encoded_monic_cubic_d_radius_body_expression
  /signed_symmetric_candidate /sextic_cubic_d_candidate
  eval_mathcomp_signed_minus !eval_mathcomp_signed_of_nat_expression.
cbn [eval_nat_expression].
rewrite !eval_encoded_monic_cubic_body_root_bound_expression
  encoded_monic_sextic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_q2 d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_q2_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  SRC.cubic_q2 f (sextic_cubic_b_candidate f b_index).
Proof.
rewrite /encoded_monic_cubic_q2_expression /SRC.cubic_q2
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_monic_cubic_b.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_q1 d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_q1_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  SRC.cubic_q1 f (sextic_cubic_b_candidate f b_index)
    (sextic_cubic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_cubic_q1_expression /SRC.cubic_q1
  eval_mathcomp_signed_minus eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient eval_mathcomp_signed_mult
  eval_mathcomp_monic_cubic_b eval_mathcomp_monic_cubic_c
  eval_mathcomp_monic_cubic_q2.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_q0 d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_q0_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  SRC.cubic_q0 f (sextic_cubic_b_candidate f b_index)
    (sextic_cubic_c_candidate f c_index)
    (sextic_cubic_d_candidate f d_index).
Proof.
rewrite /encoded_monic_cubic_q0_expression /SRC.cubic_q0
  eval_mathcomp_signed_minus eval_mathcomp_signed_minus
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  !eval_mathcomp_signed_mult eval_mathcomp_monic_cubic_b
  eval_mathcomp_monic_cubic_c eval_mathcomp_monic_cubic_d
  eval_mathcomp_monic_cubic_q1 eval_mathcomp_monic_cubic_q2.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_remainder2 d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_remainder2_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  f`_2 -
    (sextic_cubic_b_candidate f b_index *
       SRC.cubic_q0 f (sextic_cubic_b_candidate f b_index)
         (sextic_cubic_c_candidate f c_index)
         (sextic_cubic_d_candidate f d_index) +
     sextic_cubic_c_candidate f c_index *
       SRC.cubic_q1 f (sextic_cubic_b_candidate f b_index)
         (sextic_cubic_c_candidate f c_index) +
     sextic_cubic_d_candidate f d_index *
       SRC.cubic_q2 f (sextic_cubic_b_candidate f b_index)).
Proof.
rewrite /encoded_monic_cubic_remainder2_expression
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_plus eval_mathcomp_signed_plus
  !eval_mathcomp_signed_mult eval_mathcomp_monic_cubic_b
  eval_mathcomp_monic_cubic_c eval_mathcomp_monic_cubic_d
  eval_mathcomp_monic_cubic_q0 eval_mathcomp_monic_cubic_q1
  eval_mathcomp_monic_cubic_q2.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_remainder1 d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_remainder1_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  f`_1 -
    (sextic_cubic_c_candidate f c_index *
       SRC.cubic_q0 f (sextic_cubic_b_candidate f b_index)
         (sextic_cubic_c_candidate f c_index)
         (sextic_cubic_d_candidate f d_index) +
     sextic_cubic_d_candidate f d_index *
       SRC.cubic_q1 f (sextic_cubic_b_candidate f b_index)
         (sextic_cubic_c_candidate f c_index)).
Proof.
rewrite /encoded_monic_cubic_remainder1_expression
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_plus !eval_mathcomp_signed_mult
  eval_mathcomp_monic_cubic_c eval_mathcomp_monic_cubic_d
  eval_mathcomp_monic_cubic_q0 eval_mathcomp_monic_cubic_q1.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_cubic_remainder0 d_index c_index b_index
    (f : SRC.monic_sextic) :
  eval_mathcomp_signed_expression encoded_monic_cubic_remainder0_expression
      (d_index ## c_index ## b_index ##
        encode_monic_sextic_coefficients f) =
  f`_0 - sextic_cubic_d_candidate f d_index *
    SRC.cubic_q0 f (sextic_cubic_b_candidate f b_index)
      (sextic_cubic_c_candidate f c_index)
      (sextic_cubic_d_candidate f d_index).
Proof.
rewrite /encoded_monic_cubic_remainder0_expression
  eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult eval_mathcomp_monic_cubic_d
  eval_mathcomp_monic_cubic_q0.
rewrite /encode_monic_sextic_coefficients
  mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma encoded_monic_cubic_remainders_mathcomp_iff
    d_index c_index b_index (f : SRC.monic_sextic) :
  encoded_monic_cubic_remainder2
      (encode_monic_sextic_coefficients f)
      b_index c_index d_index = Z0 /\
  encoded_monic_cubic_remainder1
      (encode_monic_sextic_coefficients f)
      b_index c_index d_index = Z0 /\
  encoded_monic_cubic_remainder0
      (encode_monic_sextic_coefficients f)
      b_index c_index d_index = Z0 <->
  SRC.cubic_remainder_zerob f
    (sextic_cubic_b_candidate f b_index)
    (sextic_cubic_c_candidate f c_index)
    (sextic_cubic_d_candidate f d_index) = true.
Proof.
rewrite -eval_encoded_monic_cubic_remainder2_expression
  -eval_encoded_monic_cubic_remainder1_expression
  -eval_encoded_monic_cubic_remainder0_expression
  !signed_zero_mathcomp_iff
  eval_mathcomp_monic_cubic_remainder2
  eval_mathcomp_monic_cubic_remainder1
  eval_mathcomp_monic_cubic_remainder0.
split.
- move=> [h2 [h1 h0]].
  apply/SRC.cubic_remainder_zeroP.
  split; first exact: subr0_eq.
  split; exact: subr0_eq.
- move/SRC.cubic_remainder_zeroP=> [h2 [h1 h0]].
  split; first by rewrite h2 subrr.
  split; by [rewrite h1 subrr | rewrite h0 subrr].
Qed.

Lemma sextic_cubic_c_candidateE (f : SRC.monic_sextic) index :
  sextic_cubic_c_candidate f index =
    index%:Z - (3 * expn (SRC.root_bound f) 2)%:Z.
Proof.
rewrite /sextic_cubic_c_candidate.
have -> : muln (muln 3 (SRC.root_bound f)) (SRC.root_bound f) =
    muln 3 (expn (SRC.root_bound f) 2)
  by rewrite expnS expn1 mulnA.
reflexivity.
Qed.

Lemma sextic_cubic_d_candidateE (f : SRC.monic_sextic) index :
  sextic_cubic_d_candidate f index =
    index%:Z - (expn (SRC.root_bound f) 3)%:Z.
Proof.
rewrite /sextic_cubic_d_candidate.
have -> :
    muln (muln (SRC.root_bound f) (SRC.root_bound f))
      (SRC.root_bound f) = expn (SRC.root_bound f) 3
  by rewrite !expnS expn0 muln1 mulnA.
reflexivity.
Qed.

Lemma encoded_monic_cubic_factor_mathcomp_iff
    (f : SRC.monic_sextic) :
  encoded_monic_has_bounded_cubic_factor
      (encode_monic_sextic_coefficients f) <->
  SAF.has_arithmetic_cubic_factor f = true.
Proof.
rewrite /encoded_monic_has_bounded_cubic_factor
  encoded_monic_sextic_root_bound_mathcomp
  /SAF.has_arithmetic_cubic_factor.
split.
- move=> [b_index [Hb [c_index [Hc [d_index [Hd Hremainders]]]]]].
  apply/hasP.
  exists (sextic_cubic_b_candidate f b_index).
  + apply/(SRC.mem_symmetric_interval _ _).
    exists b_index; split; first exact/ltP.
    reflexivity.
  + apply/hasP.
    exists (sextic_cubic_c_candidate f c_index).
    * apply/(SRC.mem_symmetric_interval _ _).
      exists c_index; split.
      -- apply/ltP.
         rewrite expnS expn1
           (mulnA 3 (SRC.root_bound f) (SRC.root_bound f)).
         exact Hc.
      -- exact: sextic_cubic_c_candidateE.
    * apply/hasP.
      exists (sextic_cubic_d_candidate f d_index).
      -- apply/(SRC.mem_symmetric_interval _ _).
         exists d_index; split.
         ++ apply/ltP.
            rewrite !expnS expn0 muln1
              (mulnA (SRC.root_bound f) (SRC.root_bound f)
                (SRC.root_bound f)).
            exact Hd.
         ++ exact: sextic_cubic_d_candidateE.
      -- exact/(encoded_monic_cubic_remainders_mathcomp_iff
          d_index c_index b_index f).
- move/hasP=> [b Hbmem Hmiddle].
  move/hasP: Hmiddle=> [c Hcmem Hinner].
  move/hasP: Hinner=> [d Hdmem Hremainders].
  have [b_index [Hb Hbeq]] :=
    (proj1 (SRC.mem_symmetric_interval _ b)) Hbmem.
  have [c_index [Hc Hceq]] :=
    (proj1 (SRC.mem_symmetric_interval _ c)) Hcmem.
  have [d_index [Hd Hdeq]] :=
    (proj1 (SRC.mem_symmetric_interval _ d)) Hdmem.
  exists b_index; split; first exact/ltP.
  exists c_index; split.
  + move/ltP: Hc=> Hc.
    rewrite expnS expn1
      (mulnA 3 (SRC.root_bound f) (SRC.root_bound f)) in Hc.
    exact Hc.
  + exists d_index; split.
    * move/ltP: Hd=> Hd.
      rewrite !expnS expn0 muln1
        (mulnA (SRC.root_bound f) (SRC.root_bound f)
          (SRC.root_bound f)) in Hd.
      exact Hd.
    * apply/(encoded_monic_cubic_remainders_mathcomp_iff
        d_index c_index b_index f).
      rewrite /sextic_cubic_b_candidate
        sextic_cubic_c_candidateE sextic_cubic_d_candidateE
        -Hbeq -Hceq -Hdeq.
      exact Hremainders.
Qed.

(** Main front-end theorem: the explicit recursive arithmetic Boolean is
    extensionally the original bounded proper-factor decision on every
    MathComp monic sextic. *)
Theorem encoded_monic_has_proper_factorb_mathcomp
    (f : SRC.monic_sextic) :
  encoded_monic_has_proper_factorb
      (encode_monic_sextic_coefficients f) =
  SRC.has_bounded_proper_factor f.
Proof.
apply/idP/idP.
- move/(encoded_monic_has_proper_factorb_true_iff
    (encode_monic_sextic_coefficients f))=>
    [Hlinear | [Hquadratic | Hcubic]].
  + rewrite /SRC.has_bounded_proper_factor.
    apply/orP; left.
    rewrite -SAF.has_arithmetic_linear_factorE.
    exact/(encoded_monic_linear_factor_mathcomp_iff f).
  + rewrite /SRC.has_bounded_proper_factor
      /SRC.has_bounded_nonlinear_factor.
    apply/orP; right; apply/orP; left.
    rewrite -SAF.has_arithmetic_quadratic_factorE.
    exact/(encoded_monic_quadratic_factor_mathcomp_iff f).
  + rewrite /SRC.has_bounded_proper_factor
      /SRC.has_bounded_nonlinear_factor.
    apply/orP; right; apply/orP; right.
    rewrite -SAF.has_arithmetic_cubic_factorE.
    exact/(encoded_monic_cubic_factor_mathcomp_iff f).
- rewrite /SRC.has_bounded_proper_factor
    /SRC.has_bounded_nonlinear_factor.
  move/orP=> [Hlinear | Hnonlinear].
  + apply/(encoded_monic_has_proper_factorb_true_iff
      (encode_monic_sextic_coefficients f)).
    left.
    apply/(encoded_monic_linear_factor_mathcomp_iff f).
    by rewrite SAF.has_arithmetic_linear_factorE.
  + move/orP: Hnonlinear=> [Hquadratic | Hcubic].
    * apply/(encoded_monic_has_proper_factorb_true_iff
        (encode_monic_sextic_coefficients f)).
      right; left.
      apply/(encoded_monic_quadratic_factor_mathcomp_iff f).
      by rewrite SAF.has_arithmetic_quadratic_factorE.
    * apply/(encoded_monic_has_proper_factorb_true_iff
        (encode_monic_sextic_coefficients f)).
      right; right.
      apply/(encoded_monic_cubic_factor_mathcomp_iff f).
      by rewrite SAF.has_arithmetic_cubic_factorE.
Qed.

(** Stable vector and one-code names for downstream composition.  Their
    computability is inherited from the expression compiler, while the
    two correctness lemmas below connect them to the MathComp decision. *)
Definition sextic_monic_factor_relation :=
  encoded_monic_proper_factor_relation.

Corollary sextic_monic_factor_relation_murec :
  MuRec_computable sextic_monic_factor_relation.
Proof. exact encoded_monic_proper_factor_relation_murec. Qed.

Lemma sextic_monic_factor_relation_mathcomp
    (f : SRC.monic_sextic) out :
  sextic_monic_factor_relation
      (encode_monic_sextic_coefficients f) out <->
  out = bool_to_nat (SRC.has_bounded_proper_factor f).
Proof.
rewrite /sextic_monic_factor_relation
  /encoded_monic_proper_factor_relation
  encoded_monic_has_proper_factorb_mathcomp.
reflexivity.
Qed.

Definition sextic_monic_factor_code_relation :=
  encoded_monic_proper_factor_code_relation.

Corollary sextic_monic_factor_code_relation_murec :
  MuRec_computable sextic_monic_factor_code_relation.
Proof. exact encoded_monic_proper_factor_code_relation_murec. Qed.

Lemma sextic_monic_factor_code_relation_mathcomp
    (f : SRC.monic_sextic) out :
  sextic_monic_factor_code_relation
      (inject (encode_monic_sextic_coefficients f) ## vec_nil) out <->
  out = bool_to_nat (SRC.has_bounded_proper_factor f).
Proof.
rewrite /sextic_monic_factor_code_relation
  /encoded_monic_proper_factor_code_relation.
cbn [vec_head].
rewrite project_inject encoded_monic_has_proper_factorb_mathcomp.
reflexivity.
Qed.

End PolynomialFormulasSexticMuRecFactorDecision.

Print Assumptions
  PolynomialFormulasSexticMuRecFactorDecision.encoded_monic_has_proper_factorb_mathcomp.
Print Assumptions
  PolynomialFormulasSexticMuRecFactorDecision.sextic_monic_factor_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecFactorDecision.sextic_monic_factor_code_relation_murec.
