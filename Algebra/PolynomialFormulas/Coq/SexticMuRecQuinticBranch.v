From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.
From PolynomialFormulas Require Import
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticRecursiveCore QuinticRecursiveFactor
  QuinticArithmeticFactorSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecQuinticBranch.

Module SMFD := PolynomialFormulasSexticMuRecFactorDecision.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QAF := PolynomialFormulasQuinticArithmeticFactorSearch.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Lemma quintic_polynomial_coef0E (f : QRF.monic_quintic) :
  (QRF.quintic_polynomial f)`_0 = f`_0.
Proof.
rewrite QAF.quintic_polynomial_coef0 /SRC.linear_q0 mul0r subr0.
rewrite (QRF.quintic_sextic_embedding_nthE f (i := 1%N) isT).
reflexivity.
Qed.

Lemma quintic_polynomial_coef1E (f : QRF.monic_quintic) :
  (QRF.quintic_polynomial f)`_1 = f`_1.
Proof.
rewrite QAF.quintic_polynomial_coef1 /SRC.linear_q1 mul0r subr0.
rewrite (QRF.quintic_sextic_embedding_nthE f (i := 2%N) isT).
reflexivity.
Qed.

Lemma quintic_polynomial_coef2E (f : QRF.monic_quintic) :
  (QRF.quintic_polynomial f)`_2 = f`_2.
Proof.
rewrite QAF.quintic_polynomial_coef2 /SRC.linear_q2 mul0r subr0.
rewrite (QRF.quintic_sextic_embedding_nthE f (i := 3%N) isT).
reflexivity.
Qed.

Lemma quintic_polynomial_coef3E (f : QRF.monic_quintic) :
  (QRF.quintic_polynomial f)`_3 = f`_3.
Proof.
rewrite QAF.quintic_polynomial_coef3 /SRC.linear_q3 mul0r subr0.
rewrite (QRF.quintic_sextic_embedding_nthE f (i := 4%N) isT).
reflexivity.
Qed.

Lemma quintic_polynomial_coef4E (f : QRF.monic_quintic) :
  (QRF.quintic_polynomial f)`_4 = f`_4.
Proof.
rewrite QAF.quintic_polynomial_coef4 /SRC.linear_q4 subr0.
rewrite (QRF.quintic_sextic_embedding_nthE f (i := 5%N) isT).
reflexivity.
Qed.

(** Ascending lower coefficients of a monic quintic. *)
Definition encode_monic_quintic_coefficients
    (f : QRF.monic_quintic) : Vector.t nat 5 :=
  mathcomp_zigzag_encode f`_0 ##
  mathcomp_zigzag_encode f`_1 ##
  mathcomp_zigzag_encode f`_2 ##
  mathcomp_zigzag_encode f`_3 ##
  mathcomp_zigzag_encode f`_4 ## vec_nil.

Lemma quintic_root_boundE (f : QRF.monic_quintic) :
  QRF.quintic_root_bound f =
  absz f`_0 + (absz f`_1 + (absz f`_2 +
    (absz f`_3 + absz f`_4))) + 2.
Proof.
rewrite /QRF.quintic_root_bound /SRC.root_bound /SRC.height
  QRF.quintic_sextic_embedding0.
rewrite (QRF.quintic_sextic_embedding_nthE f (i := 1%N) isT)
  (QRF.quintic_sextic_embedding_nthE f (i := 2%N) isT)
  (QRF.quintic_sextic_embedding_nthE f (i := 3%N) isT)
  (QRF.quintic_sextic_embedding_nthE f (i := 4%N) isT)
  (QRF.quintic_sextic_embedding_nthE f (i := 5%N) isT).
by rewrite absz0 add0n.
Qed.

Definition encoded_monic_quintic_height
    (coefficients : Vector.t nat 5) : nat :=
  zigzag_magnitude (vec_pos coefficients pos0) +
  (zigzag_magnitude (vec_pos coefficients pos1) +
  (zigzag_magnitude (vec_pos coefficients pos2) +
  (zigzag_magnitude (vec_pos coefficients pos3) +
   zigzag_magnitude (vec_pos coefficients pos4)))).

Definition encoded_monic_quintic_root_bound
    (coefficients : Vector.t nat 5) : nat :=
  encoded_monic_quintic_height coefficients + 2.

Definition encoded_monic_quintic_height_expression : nat_expression 5 :=
  NatPlus (signed_coefficient_magnitude_expression pos0)
    (NatPlus (signed_coefficient_magnitude_expression pos1)
      (NatPlus (signed_coefficient_magnitude_expression pos2)
        (NatPlus (signed_coefficient_magnitude_expression pos3)
          (signed_coefficient_magnitude_expression pos4)))).

Definition encoded_monic_quintic_root_bound_expression : nat_expression 5 :=
  NatPlus encoded_monic_quintic_height_expression (NatConst 2).

Lemma eval_encoded_monic_quintic_root_bound_expression coefficients :
  eval_nat_expression encoded_monic_quintic_root_bound_expression
    coefficients = encoded_monic_quintic_root_bound coefficients.
Proof. reflexivity. Qed.

Lemma encoded_monic_quintic_root_bound_mathcomp
    (f : QRF.monic_quintic) :
  encoded_monic_quintic_root_bound
      (encode_monic_quintic_coefficients f) = QRF.quintic_root_bound f.
Proof.
rewrite /encoded_monic_quintic_root_bound
  /encoded_monic_quintic_height /encode_monic_quintic_coefficients
  quintic_root_boundE !mathcomp_zigzag_magnitude_encode.
reflexivity.
Qed.

(** Linear-factor expression.  Its body receives [index,f0,...,f4]. *)
Definition encoded_monic_quintic_linear_count_expression :
    nat_expression 5 :=
  NatSucc
    (NatMult (NatConst 2) encoded_monic_quintic_root_bound_expression).

Definition encoded_monic_quintic_linear_body_height_expression :
    nat_expression 6 :=
  NatPlus (signed_coefficient_magnitude_expression pos1)
    (NatPlus (signed_coefficient_magnitude_expression pos2)
      (NatPlus (signed_coefficient_magnitude_expression pos3)
        (NatPlus (signed_coefficient_magnitude_expression pos4)
          (signed_coefficient_magnitude_expression pos5)))).

Definition encoded_monic_quintic_linear_body_root_bound_expression :
    nat_expression 6 :=
  NatPlus encoded_monic_quintic_linear_body_height_expression (NatConst 2).

Definition encoded_monic_quintic_linear_candidate_expression :
    signed_expression 6 :=
  signed_minus (signed_of_nat_expression (NatVar pos0))
    (signed_of_nat_expression
      encoded_monic_quintic_linear_body_root_bound_expression).

Definition encoded_monic_quintic_linear_q3_expression :
    signed_expression 6 :=
  signed_minus (signed_coefficient pos5)
    encoded_monic_quintic_linear_candidate_expression.

Definition encoded_monic_quintic_linear_q2_expression :
    signed_expression 6 :=
  signed_minus (signed_coefficient pos4)
    (signed_mult encoded_monic_quintic_linear_candidate_expression
      encoded_monic_quintic_linear_q3_expression).

Definition encoded_monic_quintic_linear_q1_expression :
    signed_expression 6 :=
  signed_minus (signed_coefficient pos3)
    (signed_mult encoded_monic_quintic_linear_candidate_expression
      encoded_monic_quintic_linear_q2_expression).

Definition encoded_monic_quintic_linear_q0_expression :
    signed_expression 6 :=
  signed_minus (signed_coefficient pos2)
    (signed_mult encoded_monic_quintic_linear_candidate_expression
      encoded_monic_quintic_linear_q1_expression).

Definition encoded_monic_quintic_linear_remainder_expression :
    signed_expression 6 :=
  signed_minus (signed_coefficient pos1)
    (signed_mult encoded_monic_quintic_linear_candidate_expression
      encoded_monic_quintic_linear_q0_expression).

Definition encoded_monic_quintic_linear_zero_expression :
    nat_expression 6 :=
  signed_zero_indicator_expression
    encoded_monic_quintic_linear_remainder_expression.

Definition encoded_monic_quintic_has_linear_factor_expression :
    nat_expression 5 :=
  NatBoundedExists encoded_monic_quintic_linear_count_expression
    encoded_monic_quintic_linear_zero_expression.

(** Quadratic-factor expression.  The innermost body receives
    [c index,b index,f0,...,f4]. *)
Definition encoded_monic_quintic_quadratic_b_count_expression :
    nat_expression 5 :=
  NatSucc (NatMult (NatConst 2)
    (NatMult (NatConst 2) encoded_monic_quintic_root_bound_expression)).

Definition encoded_monic_quintic_quadratic_outer_root_bound_expression :
    nat_expression 6 :=
  encoded_monic_quintic_linear_body_root_bound_expression.

Definition encoded_monic_quintic_quadratic_c_count_expression :
    nat_expression 6 :=
  NatSucc (NatMult (NatConst 2)
    (NatMult encoded_monic_quintic_quadratic_outer_root_bound_expression
      encoded_monic_quintic_quadratic_outer_root_bound_expression)).

Definition encoded_monic_quintic_quadratic_body_height_expression :
    nat_expression 7 :=
  NatPlus (signed_coefficient_magnitude_expression pos2)
    (NatPlus (signed_coefficient_magnitude_expression pos3)
      (NatPlus (signed_coefficient_magnitude_expression pos4)
        (NatPlus (signed_coefficient_magnitude_expression pos5)
          (signed_coefficient_magnitude_expression pos6)))).

Definition encoded_monic_quintic_quadratic_body_root_bound_expression :
    nat_expression 7 :=
  NatPlus encoded_monic_quintic_quadratic_body_height_expression
    (NatConst 2).

Definition encoded_monic_quintic_quadratic_b_expression :
    signed_expression 7 :=
  signed_symmetric_candidate pos1
    (NatMult (NatConst 2)
      encoded_monic_quintic_quadratic_body_root_bound_expression).

Definition encoded_monic_quintic_quadratic_c_expression :
    signed_expression 7 :=
  signed_symmetric_candidate pos0
    (NatMult encoded_monic_quintic_quadratic_body_root_bound_expression
      encoded_monic_quintic_quadratic_body_root_bound_expression).

Definition encoded_monic_quintic_quadratic_q2_expression :
    signed_expression 7 :=
  signed_minus (signed_coefficient pos6)
    encoded_monic_quintic_quadratic_b_expression.

Definition encoded_monic_quintic_quadratic_q1_expression :
    signed_expression 7 :=
  signed_minus
    (signed_minus (signed_coefficient pos5)
      encoded_monic_quintic_quadratic_c_expression)
    (signed_mult encoded_monic_quintic_quadratic_b_expression
      encoded_monic_quintic_quadratic_q2_expression).

Definition encoded_monic_quintic_quadratic_q0_expression :
    signed_expression 7 :=
  signed_minus
    (signed_minus (signed_coefficient pos4)
      (signed_mult encoded_monic_quintic_quadratic_b_expression
        encoded_monic_quintic_quadratic_q1_expression))
    (signed_mult encoded_monic_quintic_quadratic_c_expression
      encoded_monic_quintic_quadratic_q2_expression).

Definition encoded_monic_quintic_quadratic_remainder1_expression :
    signed_expression 7 :=
  signed_minus (signed_coefficient pos3)
    (signed_plus
      (signed_mult encoded_monic_quintic_quadratic_b_expression
        encoded_monic_quintic_quadratic_q0_expression)
      (signed_mult encoded_monic_quintic_quadratic_c_expression
        encoded_monic_quintic_quadratic_q1_expression)).

Definition encoded_monic_quintic_quadratic_remainder0_expression :
    signed_expression 7 :=
  signed_minus (signed_coefficient pos2)
    (signed_mult encoded_monic_quintic_quadratic_c_expression
      encoded_monic_quintic_quadratic_q0_expression).

Definition encoded_monic_quintic_quadratic_zero_expression :
    nat_expression 7 :=
  NatMult
    (signed_zero_indicator_expression
      encoded_monic_quintic_quadratic_remainder1_expression)
    (signed_zero_indicator_expression
      encoded_monic_quintic_quadratic_remainder0_expression).

Definition encoded_monic_quintic_quadratic_outer_predicate :
    nat_expression 6 :=
  NatBoundedExists encoded_monic_quintic_quadratic_c_count_expression
    encoded_monic_quintic_quadratic_zero_expression.

Definition encoded_monic_quintic_has_quadratic_factor_expression :
    nat_expression 5 :=
  NatBoundedExists encoded_monic_quintic_quadratic_b_count_expression
    encoded_monic_quintic_quadratic_outer_predicate.

Definition encoded_monic_quintic_has_proper_factor_expression :
    nat_expression 5 :=
  NatNonzeroIndicator
    (NatPlus encoded_monic_quintic_has_linear_factor_expression
      encoded_monic_quintic_has_quadratic_factor_expression).

Definition encoded_monic_quintic_has_proper_factorb
    (coefficients : Vector.t nat 5) : bool :=
  Nat.eqb
    (eval_nat_expression encoded_monic_quintic_has_proper_factor_expression
      coefficients) 1.

Lemma eval_encoded_monic_quintic_linear_count coefficients :
  eval_nat_expression encoded_monic_quintic_linear_count_expression
    coefficients =
  Nat.add (Nat.mul 2 (encoded_monic_quintic_root_bound coefficients)) 1.
Proof.
rewrite /encoded_monic_quintic_linear_count_expression.
cbn [eval_nat_expression].
rewrite eval_encoded_monic_quintic_root_bound_expression.
by rewrite Nat.add_1_r.
Qed.

Lemma eval_encoded_monic_quintic_linear_body_root index coefficients :
  eval_nat_expression
      encoded_monic_quintic_linear_body_root_bound_expression
      (index ## coefficients) =
  encoded_monic_quintic_root_bound coefficients.
Proof. reflexivity. Qed.

Definition quintic_linear_candidate (f : QRF.monic_quintic)
    (index : nat) : int :=
  index%:Z - (QRF.quintic_root_bound f)%:Z.

Lemma eval_mathcomp_monic_quintic_linear_candidate index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_linear_candidate_expression
      (index ## encode_monic_quintic_coefficients f) =
  quintic_linear_candidate f index.
Proof.
rewrite /encoded_monic_quintic_linear_candidate_expression
  /quintic_linear_candidate SMFD.eval_mathcomp_signed_minus
  !eval_mathcomp_signed_of_nat_expression
  eval_encoded_monic_quintic_linear_body_root
  encoded_monic_quintic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_linear_q3 index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_linear_q3_expression
      (index ## encode_monic_quintic_coefficients f) =
  QAF.quintic_linear_q3 f (quintic_linear_candidate f index).
Proof.
rewrite /encoded_monic_quintic_linear_q3_expression
  /QAF.quintic_linear_q3 SMFD.eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient
  eval_mathcomp_monic_quintic_linear_candidate
  quintic_polynomial_coef4E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_linear_q2 index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_linear_q2_expression
      (index ## encode_monic_quintic_coefficients f) =
  QAF.quintic_linear_q2 f (quintic_linear_candidate f index).
Proof.
rewrite /encoded_monic_quintic_linear_q2_expression
  /QAF.quintic_linear_q2 SMFD.eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_linear_candidate
  eval_mathcomp_monic_quintic_linear_q3 quintic_polynomial_coef3E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_linear_q1 index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_linear_q1_expression
      (index ## encode_monic_quintic_coefficients f) =
  QAF.quintic_linear_q1 f (quintic_linear_candidate f index).
Proof.
rewrite /encoded_monic_quintic_linear_q1_expression
  /QAF.quintic_linear_q1 SMFD.eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_linear_candidate
  eval_mathcomp_monic_quintic_linear_q2 quintic_polynomial_coef2E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_linear_q0 index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_linear_q0_expression
      (index ## encode_monic_quintic_coefficients f) =
  QAF.quintic_linear_q0 f (quintic_linear_candidate f index).
Proof.
rewrite /encoded_monic_quintic_linear_q0_expression
  /QAF.quintic_linear_q0 SMFD.eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_linear_candidate
  eval_mathcomp_monic_quintic_linear_q1 quintic_polynomial_coef1E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_linear_remainder index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_linear_remainder_expression
      (index ## encode_monic_quintic_coefficients f) =
  (QRF.quintic_polynomial f)`_0 -
    quintic_linear_candidate f index *
      QAF.quintic_linear_q0 f (quintic_linear_candidate f index).
Proof.
rewrite /encoded_monic_quintic_linear_remainder_expression
  SMFD.eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_linear_candidate
  eval_mathcomp_monic_quintic_linear_q0 quintic_polynomial_coef0E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_encoded_monic_quintic_linear_zero index
    (f : QRF.monic_quintic) :
  eval_nat_expression encoded_monic_quintic_linear_zero_expression
      (index ## encode_monic_quintic_coefficients f) <> 0 <->
  QAF.quintic_linear_remainder_zerob f
      (quintic_linear_candidate f index) = true.
Proof.
rewrite /encoded_monic_quintic_linear_zero_expression
  SMFD.eval_signed_zero_indicator_mathcomp_iff
  eval_mathcomp_monic_quintic_linear_remainder
  /QAF.quintic_linear_remainder_zerob.
split.
- move=> h; apply/eqP; exact: subr0_eq h.
- move/eqP=> h; by rewrite h subrr.
Qed.

Theorem eval_encoded_monic_quintic_linear_true_iff
    (f : QRF.monic_quintic) :
  eval_nat_expression encoded_monic_quintic_has_linear_factor_expression
      (encode_monic_quintic_coefficients f) = 1 <->
  QAF.has_arithmetic_quintic_linear_factor f = true.
Proof.
rewrite /encoded_monic_quintic_has_linear_factor_expression
  eval_nat_bounded_exists_true_iff
  /QAF.has_arithmetic_quintic_linear_factor.
split.
- move=> [index [Hindex Hzero]].
  rewrite eval_encoded_monic_quintic_linear_count
    encoded_monic_quintic_root_bound_mathcomp in Hindex.
  apply/hasP.
  exists (quintic_linear_candidate f index).
  + apply/(SRC.mem_symmetric_interval _ _).
    exists index; split; first exact/ltP.
    reflexivity.
  + exact/(eval_encoded_monic_quintic_linear_zero index f).
- move/hasP=> [candidate Hcandidate Hzero].
  have [index [Hindex Hcandidate']] :=
    (proj1 (SRC.mem_symmetric_interval _ candidate)) Hcandidate.
  exists index; split.
  + rewrite eval_encoded_monic_quintic_linear_count
      encoded_monic_quintic_root_bound_mathcomp.
    exact/ltP.
  + apply/(eval_encoded_monic_quintic_linear_zero index f).
    rewrite /quintic_linear_candidate -Hcandidate'.
    exact Hzero.
Qed.

Lemma eval_encoded_monic_quintic_quadratic_b_count coefficients :
  eval_nat_expression encoded_monic_quintic_quadratic_b_count_expression
      coefficients =
  Nat.add
    (Nat.mul 2
      (Nat.mul 2 (encoded_monic_quintic_root_bound coefficients))) 1.
Proof.
rewrite /encoded_monic_quintic_quadratic_b_count_expression.
cbn [eval_nat_expression].
rewrite eval_encoded_monic_quintic_root_bound_expression Nat.add_1_r.
reflexivity.
Qed.

Lemma eval_encoded_monic_quintic_quadratic_outer_root b_index coefficients :
  eval_nat_expression
      encoded_monic_quintic_quadratic_outer_root_bound_expression
      (b_index ## coefficients) =
  encoded_monic_quintic_root_bound coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_monic_quintic_quadratic_c_count b_index coefficients :
  eval_nat_expression encoded_monic_quintic_quadratic_c_count_expression
      (b_index ## coefficients) =
  Nat.add
    (Nat.mul 2
      (Nat.mul (encoded_monic_quintic_root_bound coefficients)
        (encoded_monic_quintic_root_bound coefficients))) 1.
Proof.
rewrite /encoded_monic_quintic_quadratic_c_count_expression.
cbn [eval_nat_expression].
rewrite !eval_encoded_monic_quintic_quadratic_outer_root Nat.add_1_r.
reflexivity.
Qed.

Lemma eval_encoded_monic_quintic_quadratic_body_root
    c_index b_index coefficients :
  eval_nat_expression
      encoded_monic_quintic_quadratic_body_root_bound_expression
      (c_index ## b_index ## coefficients) =
  encoded_monic_quintic_root_bound coefficients.
Proof. reflexivity. Qed.

Definition quintic_quadratic_b_candidate (f : QRF.monic_quintic)
    (index : nat) : int :=
  index%:Z - (2 * QRF.quintic_root_bound f)%:Z.

Definition quintic_quadratic_c_candidate (f : QRF.monic_quintic)
    (index : nat) : int :=
  index%:Z -
    (QRF.quintic_root_bound f * QRF.quintic_root_bound f)%:Z.

Lemma eval_mathcomp_monic_quintic_quadratic_b c_index b_index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_quadratic_b_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) =
  quintic_quadratic_b_candidate f b_index.
Proof.
rewrite /encoded_monic_quintic_quadratic_b_expression
  /signed_symmetric_candidate /quintic_quadratic_b_candidate
  SMFD.eval_mathcomp_signed_minus
  !eval_mathcomp_signed_of_nat_expression.
cbn [eval_nat_expression].
rewrite eval_encoded_monic_quintic_quadratic_body_root
  encoded_monic_quintic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_quadratic_c c_index b_index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_quadratic_c_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) =
  quintic_quadratic_c_candidate f c_index.
Proof.
rewrite /encoded_monic_quintic_quadratic_c_expression
  /signed_symmetric_candidate /quintic_quadratic_c_candidate
  SMFD.eval_mathcomp_signed_minus
  !eval_mathcomp_signed_of_nat_expression.
cbn [eval_nat_expression].
rewrite !eval_encoded_monic_quintic_quadratic_body_root
  encoded_monic_quintic_root_bound_mathcomp.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_quadratic_q2 c_index b_index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_quadratic_q2_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) =
  QAF.quintic_quadratic_q2 f
    (quintic_quadratic_b_candidate f b_index).
Proof.
rewrite /encoded_monic_quintic_quadratic_q2_expression
  /QAF.quintic_quadratic_q2 SMFD.eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient
  eval_mathcomp_monic_quintic_quadratic_b quintic_polynomial_coef4E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_quadratic_q1 c_index b_index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_quadratic_q1_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) =
  QAF.quintic_quadratic_q1 f
    (quintic_quadratic_b_candidate f b_index)
    (quintic_quadratic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_quintic_quadratic_q1_expression
  /QAF.quintic_quadratic_q1
  SMFD.eval_mathcomp_signed_minus SMFD.eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_quadratic_b
  eval_mathcomp_monic_quintic_quadratic_c
  eval_mathcomp_monic_quintic_quadratic_q2 quintic_polynomial_coef3E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_quadratic_q0 c_index b_index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_quadratic_q0_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) =
  QAF.quintic_quadratic_q0 f
    (quintic_quadratic_b_candidate f b_index)
    (quintic_quadratic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_quintic_quadratic_q0_expression
  /QAF.quintic_quadratic_q0
  SMFD.eval_mathcomp_signed_minus SMFD.eval_mathcomp_signed_minus
  eval_mathcomp_signed_coefficient !eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_quadratic_b
  eval_mathcomp_monic_quintic_quadratic_c
  eval_mathcomp_monic_quintic_quadratic_q1
  eval_mathcomp_monic_quintic_quadratic_q2 quintic_polynomial_coef2E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_quadratic_remainder1 c_index b_index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_quadratic_remainder1_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) =
  (QRF.quintic_polynomial f)`_1 -
    (quintic_quadratic_b_candidate f b_index *
       QAF.quintic_quadratic_q0 f
         (quintic_quadratic_b_candidate f b_index)
         (quintic_quadratic_c_candidate f c_index) +
     quintic_quadratic_c_candidate f c_index *
       QAF.quintic_quadratic_q1 f
         (quintic_quadratic_b_candidate f b_index)
         (quintic_quadratic_c_candidate f c_index)).
Proof.
rewrite /encoded_monic_quintic_quadratic_remainder1_expression
  SMFD.eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_plus !eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_quadratic_b
  eval_mathcomp_monic_quintic_quadratic_c
  eval_mathcomp_monic_quintic_quadratic_q0
  eval_mathcomp_monic_quintic_quadratic_q1 quintic_polynomial_coef1E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_mathcomp_monic_quintic_quadratic_remainder0 c_index b_index
    (f : QRF.monic_quintic) :
  eval_mathcomp_signed_expression
      encoded_monic_quintic_quadratic_remainder0_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) =
  (QRF.quintic_polynomial f)`_0 -
    quintic_quadratic_c_candidate f c_index *
      QAF.quintic_quadratic_q0 f
        (quintic_quadratic_b_candidate f b_index)
        (quintic_quadratic_c_candidate f c_index).
Proof.
rewrite /encoded_monic_quintic_quadratic_remainder0_expression
  SMFD.eval_mathcomp_signed_minus eval_mathcomp_signed_coefficient
  eval_mathcomp_signed_mult
  eval_mathcomp_monic_quintic_quadratic_c
  eval_mathcomp_monic_quintic_quadratic_q0 quintic_polynomial_coef0E.
rewrite /encode_monic_quintic_coefficients mathcomp_zigzag_decode_encode.
reflexivity.
Qed.

Lemma eval_encoded_monic_quintic_quadratic_zero c_index b_index
    (f : QRF.monic_quintic) :
  eval_nat_expression encoded_monic_quintic_quadratic_zero_expression
      (c_index ## b_index ## encode_monic_quintic_coefficients f) <> 0 <->
  QAF.quintic_quadratic_remainder_zerob f
    (quintic_quadratic_b_candidate f b_index)
    (quintic_quadratic_c_candidate f c_index) = true.
Proof.
rewrite /encoded_monic_quintic_quadratic_zero_expression.
cbn [eval_nat_expression].
rewrite nat_product_nonzero_iff
  !SMFD.eval_signed_zero_indicator_mathcomp_iff
  eval_mathcomp_monic_quintic_quadratic_remainder1
  eval_mathcomp_monic_quintic_quadratic_remainder0
  /QAF.quintic_quadratic_remainder_zerob.
split.
- move=> [h1 h0].
  apply/andP; split; apply/eqP; exact: subr0_eq.
- move/andP=> [/eqP h1 /eqP h0].
  split; by [rewrite h1 subrr | rewrite h0 subrr].
Qed.

Lemma quintic_quadratic_c_candidateE (f : QRF.monic_quintic) index :
  quintic_quadratic_c_candidate f index =
    index%:Z - (expn (QRF.quintic_root_bound f) 2)%:Z.
Proof.
rewrite /quintic_quadratic_c_candidate.
have -> : muln (QRF.quintic_root_bound f) (QRF.quintic_root_bound f) =
    expn (QRF.quintic_root_bound f) 2
  by rewrite expnS expn1.
reflexivity.
Qed.

Theorem eval_encoded_monic_quintic_quadratic_true_iff
    (f : QRF.monic_quintic) :
  eval_nat_expression
      encoded_monic_quintic_has_quadratic_factor_expression
      (encode_monic_quintic_coefficients f) = 1 <->
  QAF.has_arithmetic_quintic_quadratic_factor f = true.
Proof.
rewrite /encoded_monic_quintic_has_quadratic_factor_expression
  eval_nat_bounded_exists_true_iff
  /QAF.has_arithmetic_quintic_quadratic_factor.
split.
- move=> [b_index [Hb Houter]].
  rewrite eval_encoded_monic_quintic_quadratic_b_count
    encoded_monic_quintic_root_bound_mathcomp in Hb.
  rewrite /encoded_monic_quintic_quadratic_outer_predicate
    eval_nat_bounded_exists_nonzero_iff in Houter.
  move: Houter=> [c_index [Hc Hzero]].
  rewrite eval_encoded_monic_quintic_quadratic_c_count
    encoded_monic_quintic_root_bound_mathcomp in Hc.
  apply/hasP.
  exists (quintic_quadratic_b_candidate f b_index).
  + apply/(SRC.mem_symmetric_interval _ _).
    exists b_index; split; first exact/ltP.
    reflexivity.
  + apply/hasP.
    exists (quintic_quadratic_c_candidate f c_index).
    * apply/(SRC.mem_symmetric_interval _ _).
      exists c_index; split; first exact/ltP.
      exact: quintic_quadratic_c_candidateE.
    * exact/(eval_encoded_monic_quintic_quadratic_zero
        c_index b_index f).
- move/hasP=> [b Hbmem Hinner].
  move/hasP: Hinner=> [c Hcmem Hzero].
  have [b_index [Hb Hbeq]] :=
    (proj1 (SRC.mem_symmetric_interval _ b)) Hbmem.
  have [c_index [Hc Hceq]] :=
    (proj1 (SRC.mem_symmetric_interval _ c)) Hcmem.
  exists b_index; split.
  + rewrite eval_encoded_monic_quintic_quadratic_b_count
      encoded_monic_quintic_root_bound_mathcomp.
    exact/ltP.
  + rewrite /encoded_monic_quintic_quadratic_outer_predicate
      eval_nat_bounded_exists_nonzero_iff.
    exists c_index; split.
    * rewrite eval_encoded_monic_quintic_quadratic_c_count
        encoded_monic_quintic_root_bound_mathcomp.
      exact/ltP.
    * apply/(eval_encoded_monic_quintic_quadratic_zero
        c_index b_index f).
      rewrite /quintic_quadratic_b_candidate
        quintic_quadratic_c_candidateE -Hbeq -Hceq.
      exact Hzero.
Qed.

Lemma nat_sum_nonzero_iff left right :
  Nat.add left right <> 0 <-> left <> 0 \/ right <> 0.
Proof.
split.
- destruct left as [|left].
  + cbn; intro H; right; exact H.
  + intro H; left; discriminate.
- intros [Hleft | Hright].
  + destruct left; [contradiction | discriminate].
  + destruct right; [contradiction |].
    destruct left; discriminate.
Qed.

Theorem eval_encoded_monic_quintic_proper_true_iff
    (f : QRF.monic_quintic) :
  eval_nat_expression encoded_monic_quintic_has_proper_factor_expression
      (encode_monic_quintic_coefficients f) = 1 <->
  QAF.has_arithmetic_quintic_proper_factor f = true.
Proof.
rewrite /encoded_monic_quintic_has_proper_factor_expression
  eval_nat_nonzero_indicator.
cbn [eval_nat_expression].
rewrite nat_sum_nonzero_iff
  !eval_nat_bounded_exists_nonzero_iff_one
  eval_encoded_monic_quintic_linear_true_iff
  eval_encoded_monic_quintic_quadratic_true_iff
  /QAF.has_arithmetic_quintic_proper_factor.
split.
- move=> [Hlinear | Hquadratic]; apply/orP.
  + by left.
  + by right.
- move/orP=> [Hlinear | Hquadratic].
  + by left.
  + by right.
Qed.

Theorem encoded_monic_quintic_has_proper_factorb_true_iff
    (f : QRF.monic_quintic) :
  encoded_monic_quintic_has_proper_factorb
      (encode_monic_quintic_coefficients f) = true <->
  QRF.has_bounded_proper_factor f = true.
Proof.
rewrite /encoded_monic_quintic_has_proper_factorb Nat.eqb_eq
  eval_encoded_monic_quintic_proper_true_iff
  QAF.has_arithmetic_quintic_proper_factorE.
reflexivity.
Qed.

Theorem encoded_monic_quintic_has_proper_factorb_mathcomp
    (f : QRF.monic_quintic) :
  encoded_monic_quintic_has_proper_factorb
      (encode_monic_quintic_coefficients f) =
  QRF.has_bounded_proper_factor f.
Proof.
apply Bool.eq_true_iff_eq.
exact (encoded_monic_quintic_has_proper_factorb_true_iff f).
Qed.

Lemma encoded_monic_quintic_has_proper_factor_indicator coefficients :
  eval_nat_expression encoded_monic_quintic_has_proper_factor_expression
      coefficients =
  bool_to_nat (encoded_monic_quintic_has_proper_factorb coefficients).
Proof.
destruct (eval_nat_nonzero_indicator_zero_or_one
  (NatPlus encoded_monic_quintic_has_linear_factor_expression
    encoded_monic_quintic_has_quadratic_factor_expression) coefficients)
  as [Hzero | Hone].
- rewrite /encoded_monic_quintic_has_proper_factor_expression in Hzero.
  rewrite /encoded_monic_quintic_has_proper_factorb
    /bool_to_nat Hzero.
  reflexivity.
- rewrite /encoded_monic_quintic_has_proper_factor_expression in Hone.
  rewrite /encoded_monic_quintic_has_proper_factorb
    /bool_to_nat Hone.
  reflexivity.
Qed.

Definition ra_encoded_monic_quintic_has_proper_factor : recalg 5 :=
  compile_nat_expression encoded_monic_quintic_has_proper_factor_expression.

Theorem ra_encoded_monic_quintic_has_proper_factor_primitive_recursive :
  prim_rec ra_encoded_monic_quintic_has_proper_factor.
Proof.
unfold ra_encoded_monic_quintic_has_proper_factor.
exact (compile_nat_expression_primitive_recursive
  encoded_monic_quintic_has_proper_factor_expression).
Qed.

Lemma ra_encoded_monic_quintic_has_proper_factor_correct coefficients :
  ⟦ra_encoded_monic_quintic_has_proper_factor⟧ coefficients
    (bool_to_nat
      (encoded_monic_quintic_has_proper_factorb coefficients)).
Proof.
rewrite -encoded_monic_quintic_has_proper_factor_indicator.
exact: compile_nat_expression_correct.
Qed.

Definition encoded_monic_quintic_proper_factor_relation
    (coefficients : Vector.t nat 5) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_quintic_has_proper_factorb coefficients).

Theorem encoded_monic_quintic_proper_factor_relation_murec :
  MuRec_computable encoded_monic_quintic_proper_factor_relation.
Proof.
unfold encoded_monic_quintic_proper_factor_relation.
refine (@recalg_graph_murec 5
  (fun coefficients => bool_to_nat
    (encoded_monic_quintic_has_proper_factorb coefficients))
  ra_encoded_monic_quintic_has_proper_factor _).
exact ra_encoded_monic_quintic_has_proper_factor_correct.
Qed.

Lemma encoded_monic_quintic_proper_factor_relation_mathcomp
    (f : QRF.monic_quintic) out :
  encoded_monic_quintic_proper_factor_relation
      (encode_monic_quintic_coefficients f) out <->
  out = bool_to_nat (QRF.has_bounded_proper_factor f).
Proof.
rewrite /encoded_monic_quintic_proper_factor_relation
  encoded_monic_quintic_has_proper_factorb_mathcomp.
reflexivity.
Qed.

Definition ra_encoded_monic_quintic_has_proper_factor_code : recalg 1 :=
  ra_comp ra_encoded_monic_quintic_has_proper_factor (ra_vec_project 5).

Lemma ra_encoded_monic_quintic_has_proper_factor_code_correct code :
  ⟦ra_encoded_monic_quintic_has_proper_factor_code⟧
      (code ## vec_nil)
      (bool_to_nat
        (encoded_monic_quintic_has_proper_factorb (project 5 code))).
Proof.
unfold ra_encoded_monic_quintic_has_proper_factor_code.
exists (project 5 code); split.
- exact (ra_encoded_monic_quintic_has_proper_factor_correct (project 5 code)).
- intro variable; rewrite vec_pos_set.
  exact: ra_vec_project_val_at.
Qed.

Definition encoded_monic_quintic_proper_factor_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_quintic_has_proper_factorb
      (project 5 (vec_head code))).

Theorem encoded_monic_quintic_proper_factor_code_relation_murec :
  MuRec_computable encoded_monic_quintic_proper_factor_code_relation.
Proof.
unfold encoded_monic_quintic_proper_factor_code_relation.
refine (@recalg_graph_murec 1
  (fun code => bool_to_nat
    (encoded_monic_quintic_has_proper_factorb
      (project 5 (vec_head code))))
  ra_encoded_monic_quintic_has_proper_factor_code _).
intro v; vec split v with code; vec nil v.
exact: ra_encoded_monic_quintic_has_proper_factor_code_correct.
Qed.

Lemma encoded_monic_quintic_proper_factor_code_relation_mathcomp
    (f : QRF.monic_quintic) out :
  encoded_monic_quintic_proper_factor_code_relation
      (inject (encode_monic_quintic_coefficients f) ## vec_nil) out <->
  out = bool_to_nat (QRF.has_bounded_proper_factor f).
Proof.
rewrite /encoded_monic_quintic_proper_factor_code_relation.
cbn [vec_head].
rewrite project_inject encoded_monic_quintic_has_proper_factorb_mathcomp.
reflexivity.
Qed.

(** Canonical zigzag coding of the integer represented by a signed
    expression.  This removes the otherwise harmless non-canonical
    positive/negative overlap before passing coefficients to a program
    that expects the ordinary zigzag representation. *)
Definition signed_zigzag_encode_expression {arity}
    (expression : signed_expression arity) : nat_expression arity :=
  NatIfZero
    (NatMinus (signed_negative expression) (signed_positive expression))
    (NatMult (NatConst 2)
      (NatMinus (signed_positive expression) (signed_negative expression)))
    (NatSucc
      (NatMult (NatConst 2)
        (NatMinus
          (NatMinus (signed_negative expression)
            (signed_positive expression))
          (NatConst 1)))).

Lemma eval_signed_zigzag_encode_expression {arity}
    (expression : signed_expression arity) values :
  eval_nat_expression (signed_zigzag_encode_expression expression) values =
  mathcomp_zigzag_encode
    (eval_mathcomp_signed_expression expression values).
Proof.
rewrite /signed_zigzag_encode_expression
  /eval_mathcomp_signed_expression /=.
set positive := eval_nat_expression (signed_positive expression) values.
set negative := eval_nat_expression (signed_negative expression) values.
destruct (le_dec negative positive) as [Hle | Hnot].
- have Htest : Nat.sub negative positive = 0.
  { apply Nat.sub_0_le. exact Hle. }
  have Hle_ssr : (negative <= positive)%N by exact/leP.
  rewrite Htest /=.
  rewrite (subzn Hle_ssr).
  reflexivity.
- have Hlt : (positive < negative)%coq_nat.
  { lia. }
  have Hdiff : Nat.sub negative positive <> 0.
  { exact (Nat.sub_gt negative positive Hlt). }
  have Hle_ssr : (positive <= negative)%N.
  { apply/leP. lia. }
  rewrite -[positive%:Z - negative%:Z]opprB.
  rewrite (subzn Hle_ssr).
  rewrite subnE.
  destruct (Nat.sub negative positive) as [|difference] eqn:Hdifference.
  + exfalso. apply Hdiff. reflexivity.
  + rewrite -NegzE /mathcomp_zigzag_encode /=.
    rewrite Nat.sub_0_r Nat.add_0_r mul2n addn1 -addnn addnE.
    reflexivity.
Qed.

Definition encoded_monic_linear_q4_code_expression : nat_expression 7 :=
  signed_zigzag_encode_expression encoded_monic_linear_q4_expression.

Definition encoded_monic_linear_q3_code_expression : nat_expression 7 :=
  signed_zigzag_encode_expression encoded_monic_linear_q3_expression.

Definition encoded_monic_linear_q2_code_expression : nat_expression 7 :=
  signed_zigzag_encode_expression encoded_monic_linear_q2_expression.

Definition encoded_monic_linear_q1_code_expression : nat_expression 7 :=
  signed_zigzag_encode_expression encoded_monic_linear_q1_expression.

Definition encoded_monic_linear_q0_code_expression : nat_expression 7 :=
  signed_zigzag_encode_expression encoded_monic_linear_q0_expression.

(** Ascending lower coefficients [q0, ..., q4] of the synthetic quintic
    quotient, both as values and as a vector of five compiled programs. *)
Definition encoded_monic_linear_quotient_coefficients
    (values : Vector.t nat 7) : Vector.t nat 5 :=
  eval_nat_expression encoded_monic_linear_q0_code_expression values ##
  eval_nat_expression encoded_monic_linear_q1_code_expression values ##
  eval_nat_expression encoded_monic_linear_q2_code_expression values ##
  eval_nat_expression encoded_monic_linear_q3_code_expression values ##
  eval_nat_expression encoded_monic_linear_q4_code_expression values ##
  vec_nil.

Definition ra_encoded_monic_linear_quotient_programs :
    Vector.t (recalg 7) 5 :=
  compile_nat_expression encoded_monic_linear_q0_code_expression ##
  compile_nat_expression encoded_monic_linear_q1_code_expression ##
  compile_nat_expression encoded_monic_linear_q2_code_expression ##
  compile_nat_expression encoded_monic_linear_q3_code_expression ##
  compile_nat_expression encoded_monic_linear_q4_code_expression ##
  vec_nil.

Lemma ra_encoded_monic_linear_quotient_programs_correct values variable :
  ⟦vec_pos ra_encoded_monic_linear_quotient_programs variable⟧ values
    (vec_pos (encoded_monic_linear_quotient_coefficients values) variable).
Proof.
analyse pos variable; cbn
  [ra_encoded_monic_linear_quotient_programs
   encoded_monic_linear_quotient_coefficients].
all: exact: compile_nat_expression_correct.
Qed.

Lemma sextic_linear_quotient_quintic_coef0E
    (f : SRC.monic_sextic) c :
  (QRF.sextic_linear_quotient_quintic f c)`_0 = SRC.linear_q0 f c.
Proof.
rewrite -quintic_polynomial_coef0E
  QRF.sextic_linear_quotient_quintic_correct /SRC.linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma sextic_linear_quotient_quintic_coef1E
    (f : SRC.monic_sextic) c :
  (QRF.sextic_linear_quotient_quintic f c)`_1 = SRC.linear_q1 f c.
Proof.
rewrite -quintic_polynomial_coef1E
  QRF.sextic_linear_quotient_quintic_correct /SRC.linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma sextic_linear_quotient_quintic_coef2E
    (f : SRC.monic_sextic) c :
  (QRF.sextic_linear_quotient_quintic f c)`_2 = SRC.linear_q2 f c.
Proof.
rewrite -quintic_polynomial_coef2E
  QRF.sextic_linear_quotient_quintic_correct /SRC.linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma sextic_linear_quotient_quintic_coef3E
    (f : SRC.monic_sextic) c :
  (QRF.sextic_linear_quotient_quintic f c)`_3 = SRC.linear_q3 f c.
Proof.
rewrite -quintic_polynomial_coef3E
  QRF.sextic_linear_quotient_quintic_correct /SRC.linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma sextic_linear_quotient_quintic_coef4E
    (f : SRC.monic_sextic) c :
  (QRF.sextic_linear_quotient_quintic f c)`_4 = SRC.linear_q4 f c.
Proof.
rewrite -quintic_polynomial_coef4E
  QRF.sextic_linear_quotient_quintic_correct /SRC.linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma encoded_monic_linear_quotient_coefficients_mathcomp index
    (f : SRC.monic_sextic) :
  encoded_monic_linear_quotient_coefficients
      (index ## SMFD.encode_monic_sextic_coefficients f) =
  encode_monic_quintic_coefficients
    (QRF.sextic_linear_quotient_quintic f
      (index%:Z - (SRC.root_bound f)%:Z)).
Proof.
apply vec_pos_ext=> variable.
unfold encoded_monic_linear_quotient_coefficients,
  encode_monic_quintic_coefficients.
analyse pos variable; repeat rewrite vec_pos_set.
- rewrite /encoded_monic_linear_q0_code_expression
    eval_signed_zigzag_encode_expression
    SMFD.eval_mathcomp_monic_linear_q0
    sextic_linear_quotient_quintic_coef0E.
  reflexivity.
- rewrite /encoded_monic_linear_q1_code_expression
    eval_signed_zigzag_encode_expression
    SMFD.eval_mathcomp_monic_linear_q1
    sextic_linear_quotient_quintic_coef1E.
  reflexivity.
- rewrite /encoded_monic_linear_q2_code_expression
    eval_signed_zigzag_encode_expression
    SMFD.eval_mathcomp_monic_linear_q2
    sextic_linear_quotient_quintic_coef2E.
  reflexivity.
- rewrite /encoded_monic_linear_q3_code_expression
    eval_signed_zigzag_encode_expression
    SMFD.eval_mathcomp_monic_linear_q3
    sextic_linear_quotient_quintic_coef3E.
  reflexivity.
- rewrite /encoded_monic_linear_q4_code_expression
    eval_signed_zigzag_encode_expression
    SMFD.eval_mathcomp_monic_linear_q4
    sextic_linear_quotient_quintic_coef4E.
  reflexivity.
Qed.

(** A Boolean view of the compiled remainder-zero indicator. *)
Definition encoded_monic_linear_remainder_zerob
    (values : Vector.t nat 7) : bool :=
  Nat.eqb
    (eval_nat_expression
      (signed_positive encoded_monic_linear_remainder_expression) values)
    (eval_nat_expression
      (signed_negative encoded_monic_linear_remainder_expression) values).

Lemma encoded_monic_linear_remainder_indicator values :
  eval_nat_expression encoded_monic_linear_remainder_zero_expression values =
  bool_to_nat (encoded_monic_linear_remainder_zerob values).
Proof. reflexivity. Qed.

Lemma encoded_monic_linear_remainder_zerob_true_iff values :
  encoded_monic_linear_remainder_zerob values = true <->
  eval_nat_expression encoded_monic_linear_remainder_zero_expression values
    <> 0.
Proof.
rewrite encoded_monic_linear_remainder_indicator.
destruct (encoded_monic_linear_remainder_zerob values); cbn [bool_to_nat].
- split.
  + intro. discriminate.
  + intro. reflexivity.
- split.
  + discriminate.
  + intro Hnonzero. exfalso. apply Hnonzero. reflexivity.
Qed.

Lemma encoded_monic_linear_remainder_zerob_mathcomp index
    (f : SRC.monic_sextic) :
  encoded_monic_linear_remainder_zerob
      (index ## SMFD.encode_monic_sextic_coefficients f) =
  SRC.linear_remainder_zerob f
    (index%:Z - (SRC.root_bound f)%:Z).
Proof.
apply Bool.eq_true_iff_eq.
rewrite encoded_monic_linear_remainder_zerob_true_iff.
exact (SMFD.eval_encoded_monic_linear_zero_mathcomp index f).
Qed.

Definition encoded_monic_reducible_linear_bodyb
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (values : Vector.t nat 7) : bool :=
  encoded_monic_linear_remainder_zerob values &&
  quintic_decisionb (encoded_monic_linear_quotient_coefficients values).

Lemma bool_to_nat_andb left right :
  bool_to_nat (left && right) = bool_to_nat left * bool_to_nat right.
Proof. by destruct left, right. Qed.

Lemma encoded_monic_reducible_linear_body_indicator
    quintic_decisionb values :
  bool_to_nat
    (encoded_monic_reducible_linear_bodyb quintic_decisionb values) =
  eval_nat_expression encoded_monic_linear_remainder_zero_expression values *
  bool_to_nat
    (quintic_decisionb
      (encoded_monic_linear_quotient_coefficients values)).
Proof.
rewrite /encoded_monic_reducible_linear_bodyb bool_to_nat_andb
  -encoded_monic_linear_remainder_indicator.
reflexivity.
Qed.

(** Constructor for the search body.  The supplied quintic program is run
    on the five canonical quotient codes, and its answer is multiplied by
    the independently compiled remainder-zero indicator. *)
Definition ra_encoded_monic_reducible_linear_body
    (quintic_decision : recalg 5) : recalg 7 :=
  ra_comp ra_mult
    (compile_nat_expression
       encoded_monic_linear_remainder_zero_expression ##
     ra_comp quintic_decision
       ra_encoded_monic_linear_quotient_programs ## vec_nil).

Lemma ra_encoded_monic_reducible_linear_body_correct
    (quintic_decision : recalg 5)
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decision_correct : forall coefficients,
      ⟦quintic_decision⟧ coefficients
        (bool_to_nat (quintic_decisionb coefficients))) values :
  ⟦ra_encoded_monic_reducible_linear_body quintic_decision⟧ values
    (bool_to_nat
      (encoded_monic_reducible_linear_bodyb quintic_decisionb values)).
Proof.
rewrite encoded_monic_reducible_linear_body_indicator.
eapply ra_comp2_val.
- exact: compile_nat_expression_correct.
- exists (encoded_monic_linear_quotient_coefficients values); split.
  + exact (quintic_decision_correct
      (encoded_monic_linear_quotient_coefficients values)).
  + intro variable; rewrite vec_pos_set.
    exact (ra_encoded_monic_linear_quotient_programs_correct
      values variable).
- exact: ra_mult_val.
Qed.

Definition encoded_monic_reducible_linear_sum
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (coefficients : Vector.t nat 6) : nat :=
  lsum
    (List.map
      (fun index => bool_to_nat
        (encoded_monic_reducible_linear_bodyb quintic_decisionb
          (index ## coefficients)))
      (list_an 0
        (eval_nat_expression
          encoded_monic_linear_candidate_count_expression coefficients))).

Definition ra_encoded_monic_reducible_linear_sum
    (quintic_decision : recalg 5) : recalg 6 :=
  ra_comp (ra_lsum
      (ra_encoded_monic_reducible_linear_body quintic_decision))
    (compile_nat_expression
       encoded_monic_linear_candidate_count_expression ##
     ra_identity_arguments 6).

Lemma Forall2_map_pointwise {A B C : Type} (relation : A -> B -> Prop)
    (left : C -> A) (right : C -> B) values :
  (forall value, relation (left value) (right value)) ->
  List.Forall2 relation (List.map left values) (List.map right values).
Proof.
intro Hpointwise.
induction values as [|value values IHvalues]; cbn; constructor; auto.
Qed.

Lemma ra_encoded_monic_reducible_linear_sum_correct
    (quintic_decision : recalg 5)
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decision_correct : forall coefficients,
      ⟦quintic_decision⟧ coefficients
        (bool_to_nat (quintic_decisionb coefficients))) coefficients :
  ⟦ra_encoded_monic_reducible_linear_sum quintic_decision⟧ coefficients
    (encoded_monic_reducible_linear_sum
      quintic_decisionb coefficients).
Proof.
unfold ra_encoded_monic_reducible_linear_sum,
  encoded_monic_reducible_linear_sum.
exists
  (eval_nat_expression encoded_monic_linear_candidate_count_expression
      coefficients ## coefficients); split.
- apply ra_lsum_spec.
  apply Forall2_map_pointwise.
  intro index.
  exact (ra_encoded_monic_reducible_linear_body_correct
    quintic_decision_correct (index ## coefficients)).
- intro variable; analyse pos variable; cbn.
  + exact (compile_nat_expression_correct
      encoded_monic_linear_candidate_count_expression coefficients).
  + unfold ra_identity_arguments. repeat rewrite vec_pos_set.
    exact: ra_proj_val.
all: unfold ra_identity_arguments; repeat rewrite vec_pos_set;
  exact: ra_proj_val.
Qed.

Definition encoded_monic_reducible_linear_branchb
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (coefficients : Vector.t nat 6) : bool :=
  negb
    (Nat.eqb
      (encoded_monic_reducible_linear_sum
        quintic_decisionb coefficients) 0).

Definition ra_encoded_monic_reducible_linear_branch
    (quintic_decision : recalg 5) : recalg 6 :=
  ra_comp ra_ite
    (ra_encoded_monic_reducible_linear_sum quintic_decision ##
     ra_cst_n 6 0 ## ra_cst_n 6 1 ## vec_nil).

Lemma ite_rel_nonzero_boolean value :
  ite_rel value 0 1 = bool_to_nat (negb (Nat.eqb value 0)).
Proof. by destruct value. Qed.

Lemma ra_encoded_monic_reducible_linear_branch_correct
    (quintic_decision : recalg 5)
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decision_correct : forall coefficients,
      ⟦quintic_decision⟧ coefficients
        (bool_to_nat (quintic_decisionb coefficients))) coefficients :
  ⟦ra_encoded_monic_reducible_linear_branch quintic_decision⟧ coefficients
    (bool_to_nat
      (encoded_monic_reducible_linear_branchb
        quintic_decisionb coefficients)).
Proof.
unfold ra_encoded_monic_reducible_linear_branch,
  encoded_monic_reducible_linear_branchb.
rewrite -ite_rel_nonzero_boolean.
eapply ra_comp3_val.
- exact (ra_encoded_monic_reducible_linear_sum_correct
    quintic_decision_correct coefficients).
- exact: ra_cst_n_val.
- exact: ra_cst_n_val.
- exact: ra_ite_val.
Qed.

Lemma encoded_monic_reducible_linear_branchb_true_iff
    quintic_decisionb coefficients :
  encoded_monic_reducible_linear_branchb
      quintic_decisionb coefficients = true <->
  exists index : nat,
    (index <
      eval_nat_expression encoded_monic_linear_candidate_count_expression
        coefficients)%coq_nat /\
    encoded_monic_reducible_linear_bodyb quintic_decisionb
      (index ## coefficients) = true.
Proof.
rewrite /encoded_monic_reducible_linear_branchb
  Bool.negb_true_iff Nat.eqb_neq
  /encoded_monic_reducible_linear_sum lsum_map_nonzero_iff.
split.
- intros (index & Hindex & Hbody).
  exists index; split.
  + apply list_an_spec in Hindex. lia.
  + destruct
      (encoded_monic_reducible_linear_bodyb quintic_decisionb
        (index ## coefficients)) eqn:Hvalue; cbn in Hbody.
    * reflexivity.
    * contradiction.
- intros (index & Hindex & Hbody).
  exists index; split.
  + apply list_an_spec. lia.
  + rewrite Hbody. discriminate.
Qed.

Definition bounded_reducible_linear_branchb
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (f : SRC.monic_sextic) : bool :=
  has
    (fun candidate =>
      SRC.linear_remainder_zerob f candidate &&
      quintic_decisionb
        (encode_monic_quintic_coefficients
          (QRF.sextic_linear_quotient_quintic f candidate)))
    (SRC.symmetric_interval (SRC.root_bound f)).

Lemma encoded_monic_reducible_linear_bodyb_mathcomp
    quintic_decisionb index (f : SRC.monic_sextic) :
  encoded_monic_reducible_linear_bodyb quintic_decisionb
      (index ## SMFD.encode_monic_sextic_coefficients f) =
  SRC.linear_remainder_zerob f
      (index%:Z - (SRC.root_bound f)%:Z) &&
  quintic_decisionb
    (encode_monic_quintic_coefficients
      (QRF.sextic_linear_quotient_quintic f
        (index%:Z - (SRC.root_bound f)%:Z))).
Proof.
rewrite /encoded_monic_reducible_linear_bodyb
  encoded_monic_linear_remainder_zerob_mathcomp
  encoded_monic_linear_quotient_coefficients_mathcomp.
reflexivity.
Qed.

Theorem encoded_monic_reducible_linear_branchb_mathcomp
    quintic_decisionb (f : SRC.monic_sextic) :
  encoded_monic_reducible_linear_branchb quintic_decisionb
      (SMFD.encode_monic_sextic_coefficients f) =
  bounded_reducible_linear_branchb quintic_decisionb f.
Proof.
apply Bool.eq_true_iff_eq.
rewrite encoded_monic_reducible_linear_branchb_true_iff.
split.
- intros (index & Hindex & Hbody).
  apply/hasP.
  exists (index%:Z - (SRC.root_bound f)%:Z).
  + apply SRC.mem_symmetric_interval.
    exists index; split=> //.
    rewrite eval_encoded_monic_linear_candidate_count_expression
      SMFD.encoded_monic_sextic_root_bound_mathcomp in Hindex.
    exact/ltP.
  + rewrite -encoded_monic_reducible_linear_bodyb_mathcomp.
    exact Hbody.
- move/hasP=> [candidate Hcandidate Hbody].
  have [index [Hindex Hcandidate_eq]] :=
    (proj1 (SRC.mem_symmetric_interval _ _) Hcandidate).
  subst candidate.
  exists index; split.
  + rewrite eval_encoded_monic_linear_candidate_count_expression
      SMFD.encoded_monic_sextic_root_bound_mathcomp.
    exact/ltP.
  + rewrite encoded_monic_reducible_linear_bodyb_mathcomp.
    exact Hbody.
Qed.

Definition encoded_monic_reducible_linear_branch_relation
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (coefficients : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_reducible_linear_branchb
      quintic_decisionb coefficients).

Theorem encoded_monic_reducible_linear_branch_relation_murec
    (quintic_decision : recalg 5)
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decision_correct : forall coefficients,
      ⟦quintic_decision⟧ coefficients
        (bool_to_nat (quintic_decisionb coefficients))) :
  MuRec_computable
    (encoded_monic_reducible_linear_branch_relation quintic_decisionb).
Proof.
unfold encoded_monic_reducible_linear_branch_relation.
refine (@recalg_graph_murec 6
  (fun coefficients => bool_to_nat
    (encoded_monic_reducible_linear_branchb
      quintic_decisionb coefficients))
  (ra_encoded_monic_reducible_linear_branch quintic_decision) _).
exact (ra_encoded_monic_reducible_linear_branch_correct
  quintic_decision_correct).
Qed.

Lemma encoded_monic_reducible_linear_branch_relation_mathcomp
    quintic_decisionb (f : SRC.monic_sextic) out :
  encoded_monic_reducible_linear_branch_relation quintic_decisionb
      (SMFD.encode_monic_sextic_coefficients f) out <->
  out = bool_to_nat (bounded_reducible_linear_branchb quintic_decisionb f).
Proof.
rewrite /encoded_monic_reducible_linear_branch_relation
  encoded_monic_reducible_linear_branchb_mathcomp.
reflexivity.
Qed.

Definition ra_encoded_monic_reducible_linear_branch_code
    (quintic_decision : recalg 5) : recalg 1 :=
  ra_comp (ra_encoded_monic_reducible_linear_branch quintic_decision)
    (ra_vec_project 6).

Lemma ra_encoded_monic_reducible_linear_branch_code_correct
    (quintic_decision : recalg 5)
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decision_correct : forall coefficients,
      ⟦quintic_decision⟧ coefficients
        (bool_to_nat (quintic_decisionb coefficients))) code :
  ⟦ra_encoded_monic_reducible_linear_branch_code quintic_decision⟧
      (code ## vec_nil)
      (bool_to_nat
        (encoded_monic_reducible_linear_branchb
          quintic_decisionb (project 6 code))).
Proof.
unfold ra_encoded_monic_reducible_linear_branch_code.
exists (project 6 code); split.
- exact (ra_encoded_monic_reducible_linear_branch_correct
    quintic_decision_correct (project 6 code)).
- intro variable; rewrite vec_pos_set.
  exact: ra_vec_project_val_at.
Qed.

Definition encoded_monic_reducible_linear_branch_code_relation
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_reducible_linear_branchb quintic_decisionb
      (project 6 (vec_head code))).

Theorem encoded_monic_reducible_linear_branch_code_relation_murec
    (quintic_decision : recalg 5)
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decision_correct : forall coefficients,
      ⟦quintic_decision⟧ coefficients
        (bool_to_nat (quintic_decisionb coefficients))) :
  MuRec_computable
    (encoded_monic_reducible_linear_branch_code_relation quintic_decisionb).
Proof.
unfold encoded_monic_reducible_linear_branch_code_relation.
refine (@recalg_graph_murec 1
  (fun code => bool_to_nat
    (encoded_monic_reducible_linear_branchb quintic_decisionb
      (project 6 (vec_head code))))
  (ra_encoded_monic_reducible_linear_branch_code quintic_decision) _).
intro values; vec split values with code; vec nil values.
exact (ra_encoded_monic_reducible_linear_branch_code_correct
  quintic_decision_correct code).
Qed.

Lemma encoded_monic_reducible_linear_branch_code_relation_mathcomp
    quintic_decisionb (f : SRC.monic_sextic) out :
  encoded_monic_reducible_linear_branch_code_relation quintic_decisionb
      (inject (SMFD.encode_monic_sextic_coefficients f) ## vec_nil) out <->
  out = bool_to_nat (bounded_reducible_linear_branchb quintic_decisionb f).
Proof.
rewrite /encoded_monic_reducible_linear_branch_code_relation.
cbn [vec_head].
rewrite project_inject encoded_monic_reducible_linear_branchb_mathcomp.
reflexivity.
Qed.

Print Assumptions encoded_monic_quintic_has_proper_factorb_mathcomp.
Print Assumptions encoded_monic_quintic_proper_factor_relation_murec.
Print Assumptions encoded_monic_quintic_proper_factor_code_relation_murec.
Print Assumptions ra_encoded_monic_linear_quotient_programs_correct.
Print Assumptions encoded_monic_linear_quotient_coefficients_mathcomp.
Print Assumptions ra_encoded_monic_reducible_linear_branch_correct.
Print Assumptions encoded_monic_reducible_linear_branchb_mathcomp.
Print Assumptions encoded_monic_reducible_linear_branch_relation_murec.
Print Assumptions encoded_monic_reducible_linear_branch_code_relation_murec.

End PolynomialFormulasSexticMuRecQuinticBranch.
