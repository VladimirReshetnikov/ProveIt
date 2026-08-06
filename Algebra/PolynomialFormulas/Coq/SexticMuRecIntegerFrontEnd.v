(* ===================================================================== *)
(*  Mu-recursive exact-degree test and integral sextic monicization.     *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_field.

From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.MuRec.Util Require Import recalg recomp ra_recomp.

From PolynomialFormulas Require Import
  SexticRecursiveCore SexticMuRecComputability
  SexticMuRecFactorDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Module PolynomialFormulasSexticMuRecIntegerFrontEnd.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.

(* --------------------------------------------------------------------- *)
(* Encoding the value of a signed expression back into zigzag form.      *)

Definition signed_zigzag_code_expression {arity}
    (expression : signed_expression arity) : nat_expression arity :=
  let positive := signed_positive expression in
  let negative := signed_negative expression in
  let positive_difference := NatMinus positive negative in
  let negative_difference := NatMinus negative positive in
  NatIfZero negative_difference
    (NatMult (NatConst 2) positive_difference)
    (NatSucc
      (NatMult (NatConst 2)
        (NatMinus negative_difference (NatConst 1)))).

Lemma eval_signed_zigzag_code_expression {arity}
    (expression : signed_expression arity) values :
  eval_nat_expression (signed_zigzag_code_expression expression) values =
  mathcomp_zigzag_encode
    (eval_mathcomp_signed_expression expression values).
Proof.
  unfold signed_zigzag_code_expression,
    eval_mathcomp_signed_expression.
  cbn [eval_nat_expression].
  remember (eval_nat_expression (signed_positive expression) values)
    as positive eqn:Hpositive.
  remember (eval_nat_expression (signed_negative expression) values)
    as negative eqn:Hnegative.
  destruct (le_dec negative positive) as [Hle | Hnotle].
  - have Hzero : Nat.sub negative positive = 0%nat.
    { apply Nat.sub_0_le. exact Hle. }
    rewrite Hzero.
    have Hdecomp :
        positive = Nat.add (Nat.sub positive negative) negative by lia.
    have Hint : (positive%:Z - negative%:Z : int) =
        Posz (Nat.sub positive negative).
    { by rewrite Hdecomp PoszD addrK Nat.add_sub. }
    rewrite Hint.
    rewrite /mathcomp_zigzag_encode.
    reflexivity.
  - have Hlt : Nat.lt positive negative by lia.
    have Hposle : Nat.le positive negative by lia.
    have Hzero : Nat.sub positive negative = 0%nat.
    { apply Nat.sub_0_le. exact Hposle. }
    rewrite Hzero.
    have Hdiff : exists magnitude,
        Nat.sub negative positive = S magnitude.
    { have Hneq : Nat.sub negative positive <> 0%nat.
      { move=> Hzero'. apply Hnotle.
        exact: (proj1 (Nat.sub_0_le negative positive) Hzero'). }
      destruct (Nat.sub negative positive) as [|magnitude] eqn:Hdifference.
      - by exfalso; apply Hneq.
      - by exists magnitude. }
    destruct Hdiff as [magnitude Hdiff].
    rewrite Hdiff /=.
    have Hint : (positive%:Z - negative%:Z : int) = Negz magnitude.
    { have Hdecomp : negative = Nat.add positive (S magnitude) by lia.
      rewrite Hdecomp PoszD NegzE opprD addrA subrr add0r.
      reflexivity. }
    rewrite Hint /mathcomp_zigzag_encode.
    rewrite !Nat.sub_0_r !Nat.add_0_r.
    change (S (Nat.add magnitude magnitude) =
      Nat.add (Nat.mul 2 magnitude) 1).
    lia.
Qed.

Definition ra_signed_zigzag_code {arity}
    (expression : signed_expression arity) : recalg arity :=
  compile_nat_expression (signed_zigzag_code_expression expression).

Lemma ra_signed_zigzag_code_correct {arity}
    (expression : signed_expression arity) values :
  ⟦ra_signed_zigzag_code expression⟧ values
    (mathcomp_zigzag_encode
      (eval_mathcomp_signed_expression expression values)).
Proof.
  unfold ra_signed_zigzag_code.
  rewrite <- eval_signed_zigzag_code_expression.
  apply compile_nat_expression_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* Seven raw integer coefficients and the exact-degree Boolean.          *)

Definition decode_sextic_coefficients
    (values : Vector.t nat 7) : SRC.sextic_coefficients :=
  [tuple
    mathcomp_zigzag_decode (vec_pos values pos0);
    mathcomp_zigzag_decode (vec_pos values pos1);
    mathcomp_zigzag_decode (vec_pos values pos2);
    mathcomp_zigzag_decode (vec_pos values pos3);
    mathcomp_zigzag_decode (vec_pos values pos4);
    mathcomp_zigzag_decode (vec_pos values pos5);
    mathcomp_zigzag_decode (vec_pos values pos6)].

Definition encoded_raw_is_sexticb (values : Vector.t nat 7) : bool :=
  negb (Nat.eqb
    (eval_nat_expression
      (signed_coefficient_magnitude_expression (arity := 7) pos6) values)
    0).

Definition raw_is_sextic_indicator_expression : nat_expression 7 :=
  NatIfZero
    (signed_coefficient_magnitude_expression (arity := 7) pos6)
    (NatConst 0) (NatConst 1).

Lemma raw_is_sextic_indicator_correct values :
  eval_nat_expression raw_is_sextic_indicator_expression values =
    bool_to_nat (encoded_raw_is_sexticb values).
Proof.
  unfold raw_is_sextic_indicator_expression, encoded_raw_is_sexticb,
    bool_to_nat.
  cbn [eval_nat_expression].
  remember
    (eval_nat_expression
      (signed_coefficient_magnitude_expression (arity := 7) pos6) values)
    as magnitude.
  destruct magnitude; reflexivity.
Qed.

Definition ra_raw_is_sextic : recalg 7 :=
  compile_nat_expression raw_is_sextic_indicator_expression.

Lemma ra_raw_is_sextic_correct values :
  ⟦ra_raw_is_sextic⟧ values (bool_to_nat (encoded_raw_is_sexticb values)).
Proof.
  unfold ra_raw_is_sextic.
  rewrite <- raw_is_sextic_indicator_correct.
  apply compile_nat_expression_correct.
Qed.

Lemma decode_sextic_leading values :
  (decode_sextic_coefficients values)`_6 =
    mathcomp_zigzag_decode (vec_pos values pos6).
Proof. reflexivity. Qed.

Lemma encoded_raw_is_sexticb_mathcomp values :
  encoded_raw_is_sexticb values =
    SRC.is_sexticb (decode_sextic_coefficients values).
Proof.
  rewrite /encoded_raw_is_sexticb /SRC.is_sexticb
    decode_sextic_leading.
  apply f_equal.
  apply Bool.eq_true_iff_eq.
  rewrite Nat.eqb_eq.
  split.
  - move=> Hmagnitude. apply/eqP.
    apply (proj1 (zigzag_mathcomp_zero_iff (vec_pos values pos6))).
    exact: (proj1
      (zigzag_magnitude_zero_iff (vec_pos values pos6)) Hmagnitude).
  - move/eqP=> Hdecode.
    apply (proj2 (zigzag_magnitude_zero_iff (vec_pos values pos6))).
    exact: (proj2
      (zigzag_mathcomp_zero_iff (vec_pos values pos6)) Hdecode).
Qed.

Definition raw_is_sextic_relation
    (values : Vector.t nat 7) (out : nat) : Prop :=
  out = bool_to_nat (encoded_raw_is_sexticb values).

Theorem raw_is_sextic_relation_murec :
  MuRec_computable raw_is_sextic_relation.
Proof.
  unfold raw_is_sextic_relation.
  refine (@recalg_graph_murec 7
    (fun values => bool_to_nat (encoded_raw_is_sexticb values))
    ra_raw_is_sextic _).
  apply ra_raw_is_sextic_correct.
Qed.

Definition ra_raw_is_sextic_from_code : recalg 1 :=
  ra_comp ra_raw_is_sextic (ra_vec_project 7).

Lemma ra_raw_is_sextic_from_code_correct code :
  ⟦ra_raw_is_sextic_from_code⟧ (code ## vec_nil)
    (bool_to_nat (encoded_raw_is_sexticb (project 7 code))).
Proof.
  unfold ra_raw_is_sextic_from_code.
  exists (project 7 code); split.
  - apply ra_raw_is_sextic_correct.
  - intro variable. rewrite vec_pos_set.
    apply ra_vec_project_val_at.
Qed.

Definition raw_is_sextic_one_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_raw_is_sexticb (project 7 (vec_head code))).

Theorem raw_is_sextic_one_code_relation_murec :
  MuRec_computable raw_is_sextic_one_code_relation.
Proof.
  unfold raw_is_sextic_one_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => bool_to_nat
      (encoded_raw_is_sexticb (project 7 (vec_head code))))
    ra_raw_is_sextic_from_code _).
  intro values. vec split values with code. vec nil values.
  apply ra_raw_is_sextic_from_code_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* [a_i * a_6^(5-i)] as six fixed signed expressions.                   *)

Definition raw_monic_coefficient0 : signed_expression 7 :=
  signed_mult (signed_coefficient pos0)
    (signed_power (signed_coefficient pos6) 5).
Definition raw_monic_coefficient1 : signed_expression 7 :=
  signed_mult (signed_coefficient pos1)
    (signed_power (signed_coefficient pos6) 4).
Definition raw_monic_coefficient2 : signed_expression 7 :=
  signed_mult (signed_coefficient pos2)
    (signed_power (signed_coefficient pos6) 3).
Definition raw_monic_coefficient3 : signed_expression 7 :=
  signed_mult (signed_coefficient pos3)
    (signed_power (signed_coefficient pos6) 2).
Definition raw_monic_coefficient4 : signed_expression 7 :=
  signed_mult (signed_coefficient pos4)
    (signed_power (signed_coefficient pos6) 1).
Definition raw_monic_coefficient5 : signed_expression 7 :=
  signed_coefficient pos5.

Definition raw_monic_coefficient_expressions :
    Vector.t (signed_expression 7) 6 :=
  raw_monic_coefficient0 ## raw_monic_coefficient1 ##
  raw_monic_coefficient2 ## raw_monic_coefficient3 ##
  raw_monic_coefficient4 ## raw_monic_coefficient5 ## vec_nil.

Definition encoded_monicization (values : Vector.t nat 7) :
    Vector.t nat 6 :=
  vec_set_pos (fun variable =>
    eval_nat_expression
      (signed_zigzag_code_expression
        (vec_pos raw_monic_coefficient_expressions variable)) values).

Definition ra_monicization_components : Vector.t (recalg 7) 6 :=
  vec_set_pos (fun variable =>
    ra_signed_zigzag_code
      (vec_pos raw_monic_coefficient_expressions variable)).

Lemma raw_monicize0 coefficients :
  (SRC.monicize coefficients)`_0 = coefficients`_0 * coefficients`_6 ^ 5.
Proof.
  rewrite -(@tnth_nth 6 int 0 (SRC.monicize coefficients)
    (@Ordinal 6 0 isT)).
  rewrite /SRC.monicize tnth_mktuple.
  reflexivity.
Qed.

Lemma raw_monicize1 coefficients :
  (SRC.monicize coefficients)`_1 = coefficients`_1 * coefficients`_6 ^ 4.
Proof.
  rewrite -(@tnth_nth 6 int 0 (SRC.monicize coefficients)
    (@Ordinal 6 1 isT)).
  rewrite /SRC.monicize tnth_mktuple.
  reflexivity.
Qed.

Lemma raw_monicize2 coefficients :
  (SRC.monicize coefficients)`_2 = coefficients`_2 * coefficients`_6 ^ 3.
Proof.
  rewrite -(@tnth_nth 6 int 0 (SRC.monicize coefficients)
    (@Ordinal 6 2 isT)).
  rewrite /SRC.monicize tnth_mktuple.
  reflexivity.
Qed.

Lemma raw_monicize3 coefficients :
  (SRC.monicize coefficients)`_3 = coefficients`_3 * coefficients`_6 ^ 2.
Proof.
  rewrite -(@tnth_nth 6 int 0 (SRC.monicize coefficients)
    (@Ordinal 6 3 isT)).
  rewrite /SRC.monicize tnth_mktuple.
  reflexivity.
Qed.

Lemma raw_monicize4 coefficients :
  (SRC.monicize coefficients)`_4 = coefficients`_4 * coefficients`_6.
Proof.
  rewrite -(@tnth_nth 6 int 0 (SRC.monicize coefficients)
    (@Ordinal 6 4 isT)).
  rewrite /SRC.monicize tnth_mktuple.
  reflexivity.
Qed.

Lemma raw_monicize5 coefficients :
  (SRC.monicize coefficients)`_5 = coefficients`_5.
Proof.
  rewrite -(@tnth_nth 6 int 0 (SRC.monicize coefficients)
    (@Ordinal 6 5 isT)).
  rewrite /SRC.monicize tnth_mktuple.
  by rewrite mulr1.
Qed.

Lemma ra_monicization_component_correct variable values :
  ⟦vec_pos ra_monicization_components variable⟧ values
    (vec_pos (encoded_monicization values) variable).
Proof.
  rewrite /ra_monicization_components /encoded_monicization !vec_pos_set.
  unfold ra_signed_zigzag_code.
  apply compile_nat_expression_correct.
Qed.

Lemma encoded_monicization_mathcomp values :
  encoded_monicization values =
    FD.encode_monic_sextic_coefficients
      (SRC.monicize (decode_sextic_coefficients values)).
Proof.
  apply vec_pos_ext=> variable.
  rewrite /encoded_monicization vec_pos_set.
  analyse pos variable.
  all: unfold raw_monic_coefficient_expressions,
    FD.encode_monic_sextic_coefficients.
  all: repeat rewrite <- vec_pos_tail.
  all: rewrite !vec_pos0.
  all: cbn [vec_head vec_tail].
  all: rewrite eval_signed_zigzag_code_expression.
  all: rewrite ?eval_mathcomp_signed_mult ?eval_mathcomp_signed_power
    ?eval_mathcomp_signed_coefficient
    ?eval_mathcomp_signed_of_nat_expression.
  all: rewrite ?raw_monicize0 ?raw_monicize1 ?raw_monicize2
    ?raw_monicize3 ?raw_monicize4 ?raw_monicize5.
  all: cbn [decode_sextic_coefficients eval_nat_expression].
  all: rewrite ?expr0 ?mulr1.
  all: reflexivity.
Qed.

Definition ra_encoded_monicization_code : recalg 7 :=
  ra_comp (ra_inject 6) ra_monicization_components.

Lemma ra_encoded_monicization_code_correct values :
  ⟦ra_encoded_monicization_code⟧ values
    (inject (encoded_monicization values)).
Proof.
  unfold ra_encoded_monicization_code.
  exists (encoded_monicization values); split.
  - apply ra_inject_val.
  - intro variable. rewrite vec_pos_set.
    apply ra_monicization_component_correct.
Qed.

Definition encoded_monicization_code_relation
    (values : Vector.t nat 7) (out : nat) : Prop :=
  out = inject (encoded_monicization values).

Theorem encoded_monicization_code_relation_murec :
  MuRec_computable encoded_monicization_code_relation.
Proof.
  unfold encoded_monicization_code_relation.
  refine (@recalg_graph_murec 7
    (fun values => inject (encoded_monicization values))
    ra_encoded_monicization_code _).
  apply ra_encoded_monicization_code_correct.
Qed.

Definition ra_encoded_monicization_from_code : recalg 1 :=
  ra_comp ra_encoded_monicization_code (ra_vec_project 7).

Lemma ra_encoded_monicization_from_code_correct code :
  ⟦ra_encoded_monicization_from_code⟧ (code ## vec_nil)
    (inject (encoded_monicization (project 7 code))).
Proof.
  unfold ra_encoded_monicization_from_code.
  exists (project 7 code); split.
  - apply ra_encoded_monicization_code_correct.
  - intro variable. rewrite vec_pos_set.
    apply ra_vec_project_val_at.
Qed.

Definition encoded_monicization_one_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = inject
    (encoded_monicization (project 7 (vec_head code))).

Theorem encoded_monicization_one_code_relation_murec :
  MuRec_computable encoded_monicization_one_code_relation.
Proof.
  unfold encoded_monicization_one_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => inject
      (encoded_monicization (project 7 (vec_head code))))
    ra_encoded_monicization_from_code _).
  intro values. vec split values with code. vec nil values.
  apply ra_encoded_monicization_from_code_correct.
Qed.

Print Assumptions raw_is_sextic_relation_murec.
Print Assumptions raw_is_sextic_one_code_relation_murec.
Print Assumptions encoded_monicization_mathcomp.
Print Assumptions encoded_monicization_code_relation_murec.
Print Assumptions encoded_monicization_one_code_relation_murec.

End PolynomialFormulasSexticMuRecIntegerFrontEnd.
