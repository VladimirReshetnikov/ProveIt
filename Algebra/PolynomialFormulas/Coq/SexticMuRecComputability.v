(* ===================================================================== *)
(*  Direct Mu-recursive certificates for seven signed coefficients.      *)
(*                                                                       *)
(*  This file deliberately uses only the concrete recursive-algebra      *)
(*  layer of the Coq Library of Undecidability Proofs.  In particular,   *)
(*  it does not appeal to extraction, an opaque computability oracle, or  *)
(*  the much larger equivalence between machine models.                  *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia Ring Vector ZArith.

From Undecidability.Shared.Libs.DLW
  Require Import pos vec.

From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* --------------------------------------------------------------------- *)
(* Small semantic composition lemmas.                                    *)

Lemma ra_comp1_val {input} (outer : recalg 1) (inner : recalg input)
    (v : Vector.t nat input) x out :
  ⟦inner⟧ v x ->
  ⟦outer⟧ (x ## vec_nil) out ->
  ⟦ra_comp outer (inner ## vec_nil)⟧ v out.
Proof.
  intros Hinner Houter.
  exists (x ## vec_nil); split; auto.
  intros p; analyse pos p; cbn; exact Hinner.
Qed.

Lemma ra_comp2_val {input} (outer : recalg 2)
    (left right : recalg input) (v : Vector.t nat input)
    left_out right_out out :
  ⟦left⟧ v left_out ->
  ⟦right⟧ v right_out ->
  ⟦outer⟧ (left_out ## right_out ## vec_nil) out ->
  ⟦ra_comp outer (left ## right ## vec_nil)⟧ v out.
Proof.
  intros Hleft Hright Houter.
  exists (left_out ## right_out ## vec_nil); split; auto.
  intros p; analyse pos p; cbn; assumption.
Qed.

Lemma ra_comp3_val {input} (outer : recalg 3)
    (first second third : recalg input) (v : Vector.t nat input)
    first_out second_out third_out out :
  ⟦first⟧ v first_out ->
  ⟦second⟧ v second_out ->
  ⟦third⟧ v third_out ->
  ⟦outer⟧ (first_out ## second_out ## third_out ## vec_nil) out ->
  ⟦ra_comp outer (first ## second ## third ## vec_nil)⟧ v out.
Proof.
  intros Hfirst Hsecond Hthird Houter.
  exists (first_out ## second_out ## third_out ## vec_nil); split; auto.
  intros p; analyse pos p; cbn; assumption.
Qed.

(* Turning a proved [recalg] value theorem into the graph relation expected
   by [MuRec_computable] requires only the checked equivalence between the
   compositional and big-step semantics plus determinism. *)
Lemma recalg_graph_murec {arity} (function : Vector.t nat arity -> nat)
    (program : recalg arity)
    (program_correct : forall v, ⟦program⟧ v (function v)) :
  MuRec_computable (fun v out => out = function v).
Proof.
  exists program.
  intros v out.
  rewrite <- ra_rel_spec.
  split.
  - intros ->. apply program_correct.
  - intro Hrun.
    eapply ra_rel_fun.
    + exact Hrun.
    + apply program_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* A tiny first-order language of primitive-recursive natural functions.  *)

Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition nat_eq_code (left right : nat) : nat :=
  ite_rel (left - right) (right - left) 1.

Lemma nat_eq_code_indicator left right :
  1 - nat_eq_code left right = bool_to_nat (Nat.eqb left right).
Proof.
  unfold nat_eq_code, bool_to_nat, ite_rel.
  destruct (Nat.eqb left right) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    rewrite Heq, Nat.sub_diag. reflexivity.
  - apply Nat.eqb_neq in Heq.
    destruct (left - right) eqn:Hminus; lia.
Qed.

Inductive nat_expression (arity : nat) : Type :=
  | NatConst : nat -> nat_expression arity
  | NatVar : pos arity -> nat_expression arity
  | NatSucc : nat_expression arity -> nat_expression arity
  | NatPlus : nat_expression arity -> nat_expression arity ->
      nat_expression arity
  | NatMult : nat_expression arity -> nat_expression arity ->
      nat_expression arity
  | NatDiv2 : nat_expression arity -> nat_expression arity
  | NatMod2 : nat_expression arity -> nat_expression arity
  | NatIfZero : nat_expression arity -> nat_expression arity ->
      nat_expression arity -> nat_expression arity
  | NatEqIndicator : nat_expression arity -> nat_expression arity ->
      nat_expression arity.

Arguments NatConst {arity} _.
Arguments NatVar {arity} _.
Arguments NatSucc {arity} _.
Arguments NatPlus {arity} _ _.
Arguments NatMult {arity} _ _.
Arguments NatDiv2 {arity} _.
Arguments NatMod2 {arity} _.
Arguments NatIfZero {arity} _ _ _.
Arguments NatEqIndicator {arity} _ _.

Fixpoint eval_nat_expression {arity} (expression : nat_expression arity)
    (v : Vector.t nat arity) : nat :=
  match expression with
  | NatConst constant => constant
  | NatVar variable => vec_pos v variable
  | NatSucc inner => S (eval_nat_expression inner v)
  | NatPlus lhs rhs =>
      eval_nat_expression lhs v + eval_nat_expression rhs v
  | NatMult lhs rhs =>
      eval_nat_expression lhs v * eval_nat_expression rhs v
  | NatDiv2 inner => gcd.div (eval_nat_expression inner v) 2
  | NatMod2 inner => gcd.rem (eval_nat_expression inner v) 2
  | NatIfZero test if_zero if_nonzero =>
      ite_rel (eval_nat_expression test v)
        (eval_nat_expression if_zero v)
        (eval_nat_expression if_nonzero v)
  | NatEqIndicator lhs rhs =>
      bool_to_nat
        (Nat.eqb (eval_nat_expression lhs v)
                 (eval_nat_expression rhs v))
  end.

Fixpoint compile_nat_expression {arity}
    (expression : nat_expression arity) : recalg arity :=
  match expression with
  | NatConst constant => ra_cst_n arity constant
  | NatVar variable => ra_proj variable
  | NatSucc inner =>
      ra_comp ra_succ (compile_nat_expression inner ## vec_nil)
  | NatPlus lhs rhs =>
      ra_comp ra_plus
        (compile_nat_expression lhs ##
         compile_nat_expression rhs ## vec_nil)
  | NatMult lhs rhs =>
      ra_comp ra_mult
        (compile_nat_expression lhs ##
         compile_nat_expression rhs ## vec_nil)
  | NatDiv2 inner =>
      ra_comp ra_div2 (compile_nat_expression inner ## vec_nil)
  | NatMod2 inner =>
      ra_comp ra_mod2 (compile_nat_expression inner ## vec_nil)
  | NatIfZero test if_zero if_nonzero =>
      ra_comp ra_ite
        (compile_nat_expression test ##
         compile_nat_expression if_zero ##
         compile_nat_expression if_nonzero ## vec_nil)
  | NatEqIndicator lhs rhs =>
      ra_comp ra_not
        (ra_comp ra_eq
          (compile_nat_expression lhs ##
           compile_nat_expression rhs ## vec_nil) ## vec_nil)
  end.

Theorem compile_nat_expression_correct {arity}
    (expression : nat_expression arity) v :
  ⟦compile_nat_expression expression⟧ v
    (eval_nat_expression expression v).
Proof.
  induction expression; cbn [compile_nat_expression eval_nat_expression].
  - apply ra_cst_n_val.
  - apply ra_proj_val.
  - eapply ra_comp1_val.
    + exact IHexpression.
    + reflexivity.
  - eapply ra_comp2_val.
    + exact IHexpression1.
    + exact IHexpression2.
    + apply ra_plus_val.
  - eapply ra_comp2_val.
    + exact IHexpression1.
    + exact IHexpression2.
    + apply ra_mult_val.
  - eapply ra_comp1_val.
    + exact IHexpression.
    + apply ra_div2_val.
  - eapply ra_comp1_val.
    + exact IHexpression.
    + apply ra_mod2_val.
  - eapply ra_comp3_val.
    + exact IHexpression1.
    + exact IHexpression2.
    + exact IHexpression3.
    + apply ra_ite_val.
  - rewrite <- nat_eq_code_indicator.
    eapply ra_comp1_val.
    + eapply ra_comp2_val.
      * exact IHexpression1.
      * exact IHexpression2.
      * apply ra_eq_val.
    + apply ra_not_val.
Qed.

Theorem compile_nat_expression_primitive_recursive {arity}
    (expression : nat_expression arity) :
  prim_rec (compile_nat_expression expression).
Proof.
  induction expression; cbn [compile_nat_expression]; ra prim rec.
Qed.

(* --------------------------------------------------------------------- *)
(* Genuine zig-zag encodings of signed integers.                         *)

Definition zigzag_positive (code : nat) : nat :=
  ite_rel (gcd.rem code 2) (gcd.div code 2) 0.

Definition zigzag_negative (code : nat) : nat :=
  ite_rel (gcd.rem code 2) 0 (S (gcd.div code 2)).

Definition zigzag_decode (code : nat) : Z :=
  (Z.of_nat (zigzag_positive code) -
   Z.of_nat (zigzag_negative code))%Z.

Definition zigzag_encode (value : Z) : nat :=
  match value with
  | Z0 => 0
  | Zpos positive => 2 * Pos.to_nat positive
  | Zneg positive => 2 * (Pos.to_nat positive - 1) + 1
  end.

Lemma div_even_by_two magnitude : gcd.div (2 * magnitude) 2 = magnitude.
Proof.
  apply gcd.div_2_fix_1.
Qed.

Lemma rem_even_by_two magnitude : gcd.rem (2 * magnitude) 2 = 0.
Proof.
  apply gcd.rem_2_fix_1.
Qed.

Lemma div_odd_by_two magnitude : gcd.div (2 * magnitude + 1) 2 = magnitude.
Proof.
  replace (2 * magnitude + 1) with (1 + 2 * magnitude) by lia.
  apply gcd.div_2_fix_2.
Qed.

Lemma rem_odd_by_two magnitude : gcd.rem (2 * magnitude + 1) 2 = 1.
Proof.
  replace (2 * magnitude + 1) with (1 + 2 * magnitude) by lia.
  apply gcd.rem_2_fix_2.
Qed.

Lemma zigzag_positive_even magnitude :
  zigzag_positive (2 * magnitude) = magnitude.
Proof.
  unfold zigzag_positive.
  rewrite rem_even_by_two, div_even_by_two. reflexivity.
Qed.

Lemma zigzag_negative_even magnitude :
  zigzag_negative (2 * magnitude) = 0.
Proof.
  unfold zigzag_negative.
  rewrite rem_even_by_two. reflexivity.
Qed.

Lemma zigzag_positive_odd magnitude :
  zigzag_positive (2 * magnitude + 1) = 0.
Proof.
  unfold zigzag_positive.
  rewrite rem_odd_by_two. reflexivity.
Qed.

Lemma zigzag_negative_odd magnitude :
  zigzag_negative (2 * magnitude + 1) = S magnitude.
Proof.
  unfold zigzag_negative.
  rewrite rem_odd_by_two, div_odd_by_two. reflexivity.
Qed.

Theorem zigzag_decode_encode value :
  zigzag_decode (zigzag_encode value) = value.
Proof.
  destruct value as [|positive|positive].
  - unfold zigzag_encode, zigzag_decode.
    change
      (Z.of_nat (zigzag_positive (2 * 0)) -
       Z.of_nat (zigzag_negative (2 * 0)) = 0)%Z.
    rewrite zigzag_positive_even, zigzag_negative_even. reflexivity.
  - unfold zigzag_encode, zigzag_decode.
    rewrite zigzag_positive_even, zigzag_negative_even.
    rewrite Z.sub_0_r, positive_nat_Z. reflexivity.
  - unfold zigzag_encode, zigzag_decode.
    rewrite zigzag_positive_odd, zigzag_negative_odd.
    pose proof (Pos2Nat.is_pos positive) as Hpositive.
    replace (S (Pos.to_nat positive - 1)) with (Pos.to_nat positive) by lia.
    rewrite positive_nat_Z. reflexivity.
Qed.

Definition zigzag_positive_expression {arity}
    (code : nat_expression arity) : nat_expression arity :=
  NatIfZero (NatMod2 code) (NatDiv2 code) (NatConst 0).

Definition zigzag_negative_expression {arity}
    (code : nat_expression arity) : nat_expression arity :=
  NatIfZero (NatMod2 code) (NatConst 0) (NatSucc (NatDiv2 code)).

Lemma eval_zigzag_positive_expression {arity}
    (code : nat_expression arity) v :
  eval_nat_expression (zigzag_positive_expression code) v =
  zigzag_positive (eval_nat_expression code v).
Proof. reflexivity. Qed.

Lemma eval_zigzag_negative_expression {arity}
    (code : nat_expression arity) v :
  eval_nat_expression (zigzag_negative_expression code) v =
  zigzag_negative (eval_nat_expression code v).
Proof. reflexivity. Qed.

(* A signed expression is represented by natural positive and negative
   components.  It denotes [positive - negative] in [Z]. *)
Record signed_expression (arity : nat) : Type := {
  signed_positive : nat_expression arity;
  signed_negative : nat_expression arity
}.

Arguments signed_positive {arity} _.
Arguments signed_negative {arity} _.

Definition eval_signed_expression {arity}
    (expression : signed_expression arity) v : Z :=
  (Z.of_nat (eval_nat_expression (signed_positive expression) v) -
   Z.of_nat (eval_nat_expression (signed_negative expression) v))%Z.

Definition signed_coefficient {arity} (variable : pos arity) :
    signed_expression arity :=
  {| signed_positive := zigzag_positive_expression (NatVar variable);
     signed_negative := zigzag_negative_expression (NatVar variable) |}.

Definition signed_plus {arity} (left right : signed_expression arity) :
    signed_expression arity :=
  {| signed_positive :=
       NatPlus (signed_positive left) (signed_positive right);
     signed_negative :=
       NatPlus (signed_negative left) (signed_negative right) |}.

Definition signed_negate {arity} (expression : signed_expression arity) :
    signed_expression arity :=
  {| signed_positive := signed_negative expression;
     signed_negative := signed_positive expression |}.

Definition signed_minus {arity} (left right : signed_expression arity) :
    signed_expression arity :=
  signed_plus left (signed_negate right).

Definition signed_mult {arity} (left right : signed_expression arity) :
    signed_expression arity :=
  {| signed_positive :=
       NatPlus
         (NatMult (signed_positive left) (signed_positive right))
         (NatMult (signed_negative left) (signed_negative right));
     signed_negative :=
       NatPlus
         (NatMult (signed_positive left) (signed_negative right))
         (NatMult (signed_negative left) (signed_positive right)) |}.

Lemma eval_signed_coefficient {arity} (variable : pos arity) v :
  eval_signed_expression (signed_coefficient variable) v =
  zigzag_decode (vec_pos v variable).
Proof. reflexivity. Qed.

Lemma eval_signed_plus {arity} (left right : signed_expression arity) v :
  eval_signed_expression (signed_plus left right) v =
  (eval_signed_expression left v + eval_signed_expression right v)%Z.
Proof.
  unfold eval_signed_expression, signed_plus; cbn.
  repeat rewrite Nat2Z.inj_add. lia.
Qed.

Lemma eval_signed_negate {arity} (expression : signed_expression arity) v :
  eval_signed_expression (signed_negate expression) v =
  (- eval_signed_expression expression v)%Z.
Proof.
  unfold eval_signed_expression, signed_negate; cbn. lia.
Qed.

Lemma eval_signed_minus {arity} (left right : signed_expression arity) v :
  eval_signed_expression (signed_minus left right) v =
  (eval_signed_expression left v - eval_signed_expression right v)%Z.
Proof.
  unfold signed_minus.
  rewrite eval_signed_plus, eval_signed_negate. ring.
Qed.

Lemma eval_signed_mult {arity} (left right : signed_expression arity) v :
  eval_signed_expression (signed_mult left right) v =
  (eval_signed_expression left v * eval_signed_expression right v)%Z.
Proof.
  unfold eval_signed_expression, signed_mult; cbn.
  repeat rewrite Nat2Z.inj_add.
  repeat rewrite Nat2Z.inj_mul.
  ring.
Qed.

Definition signed_equality_expression {arity}
    (left right : signed_expression arity) : nat_expression arity :=
  NatEqIndicator
    (NatPlus (signed_positive left) (signed_negative right))
    (NatPlus (signed_negative left) (signed_positive right)).

Definition signed_expression_eqb {arity}
    (left right : signed_expression arity) v : bool :=
  Nat.eqb
    (eval_nat_expression
      (NatPlus (signed_positive left) (signed_negative right)) v)
    (eval_nat_expression
      (NatPlus (signed_negative left) (signed_positive right)) v).

Lemma eval_signed_equality_expression {arity}
    (left right : signed_expression arity) v :
  eval_nat_expression (signed_equality_expression left right) v =
  bool_to_nat (signed_expression_eqb left right v).
Proof. reflexivity. Qed.

Theorem signed_expression_eqb_true_iff {arity}
    (left right : signed_expression arity) v :
  signed_expression_eqb left right v = true <->
  eval_signed_expression left v = eval_signed_expression right v.
Proof.
  unfold signed_expression_eqb, eval_signed_expression.
  rewrite Nat.eqb_eq.
  rewrite <- Nat2Z.inj_iff.
  cbn [eval_nat_expression].
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.

(* --------------------------------------------------------------------- *)
(* A representative seven-coefficient signed Boolean.                    *)

Definition seven_signed_left : signed_expression 7 :=
  signed_plus (signed_coefficient pos0)
    (signed_mult (signed_coefficient pos1) (signed_coefficient pos2)).

Definition seven_signed_right : signed_expression 7 :=
  signed_plus
    (signed_mult (signed_coefficient pos3) (signed_coefficient pos4))
    (signed_plus (signed_coefficient pos5) (signed_coefficient pos6)).

Definition seven_signed_boolean (coefficients : Vector.t nat 7) : bool :=
  signed_expression_eqb seven_signed_left seven_signed_right coefficients.

Definition seven_signed_indicator_expression : nat_expression 7 :=
  signed_equality_expression seven_signed_left seven_signed_right.

Definition ra_seven_signed_indicator : recalg 7 :=
  compile_nat_expression seven_signed_indicator_expression.

Lemma ra_seven_signed_indicator_correct coefficients :
  ⟦ra_seven_signed_indicator⟧ coefficients
    (bool_to_nat (seven_signed_boolean coefficients)).
Proof.
  unfold ra_seven_signed_indicator, seven_signed_indicator_expression,
    seven_signed_boolean.
  rewrite <- eval_signed_equality_expression.
  apply compile_nat_expression_correct.
Qed.

Definition seven_signed_relation
    (coefficients : Vector.t nat 7) (out : nat) : Prop :=
  out = bool_to_nat (seven_signed_boolean coefficients).

Theorem seven_signed_relation_murec :
  MuRec_computable seven_signed_relation.
Proof.
  unfold seven_signed_relation.
  refine (@recalg_graph_murec 7
    (fun coefficients => bool_to_nat (seven_signed_boolean coefficients))
    ra_seven_signed_indicator _).
  apply ra_seven_signed_indicator_correct.
Qed.

Theorem seven_signed_boolean_true_iff coefficients :
  seven_signed_boolean coefficients = true <->
  (zigzag_decode (vec_pos coefficients pos0) +
   zigzag_decode (vec_pos coefficients pos1) *
     zigzag_decode (vec_pos coefficients pos2) =
   zigzag_decode (vec_pos coefficients pos3) *
     zigzag_decode (vec_pos coefficients pos4) +
   (zigzag_decode (vec_pos coefficients pos5) +
    zigzag_decode (vec_pos coefficients pos6)))%Z.
Proof.
  unfold seven_signed_boolean.
  rewrite signed_expression_eqb_true_iff.
  unfold seven_signed_left, seven_signed_right.
  repeat rewrite eval_signed_plus.
  repeat rewrite eval_signed_mult.
  repeat rewrite eval_signed_coefficient.
  reflexivity.
Qed.

Definition encode_seven_coefficients
    (coefficients : Vector.t Z 7) : Vector.t nat 7 :=
  vec_map zigzag_encode coefficients.

Lemma encode_seven_coefficients_correct coefficients variable :
  zigzag_decode
    (vec_pos (encode_seven_coefficients coefficients) variable) =
  vec_pos coefficients variable.
Proof.
  unfold encode_seven_coefficients.
  rewrite vec_pos_map, zigzag_decode_encode. reflexivity.
Qed.

Theorem seven_signed_boolean_encoded_true_iff
    (coefficients : Vector.t Z 7) :
  seven_signed_boolean (encode_seven_coefficients coefficients) = true <->
  (vec_pos coefficients pos0 +
   vec_pos coefficients pos1 * vec_pos coefficients pos2 =
   vec_pos coefficients pos3 * vec_pos coefficients pos4 +
   (vec_pos coefficients pos5 + vec_pos coefficients pos6))%Z.
Proof.
  rewrite seven_signed_boolean_true_iff.
  repeat rewrite encode_seven_coefficients_correct.
  reflexivity.
Qed.

(* The same program can consume a single natural that pairs seven zig-zag
   coefficient codes. *)
Lemma ra_vec_project_val_at arity (variable : pos arity) code :
  ⟦vec_pos (ra_vec_project arity) variable⟧ (code ## vec_nil)
    (vec_pos (project arity code) variable).
Proof.
  replace (vec_pos (ra_vec_project arity) variable)
    with (@ra_project arity variable).
  - apply ra_project_val.
  - unfold ra_vec_project. symmetry. apply vec_pos_set.
Qed.

Opaque ra_vec_project.

Definition ra_seven_signed_code : recalg 1 :=
  ra_comp ra_seven_signed_indicator (ra_vec_project 7).

Lemma ra_seven_signed_code_correct code :
  ⟦ra_seven_signed_code⟧ (code ## vec_nil)
    (bool_to_nat (seven_signed_boolean (project 7 code))).
Proof.
  unfold ra_seven_signed_code.
  exists (project 7 code); split.
  - apply ra_seven_signed_indicator_correct.
  - intro variable. rewrite vec_pos_set.
    apply ra_vec_project_val_at.
Qed.

Definition seven_signed_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (seven_signed_boolean (project 7 (vec_head code))).

Theorem seven_signed_code_relation_murec :
  MuRec_computable seven_signed_code_relation.
Proof.
  unfold seven_signed_code_relation.
  refine (@recalg_graph_murec 1
    (fun code =>
      bool_to_nat (seven_signed_boolean (project 7 (vec_head code))))
    ra_seven_signed_code _).
  intro v. vec split v with code. vec nil v.
  apply ra_seven_signed_code_correct.
Qed.

Lemma seven_signed_code_roundtrip coefficients out :
  seven_signed_code_relation (inject coefficients ## vec_nil) out <->
  seven_signed_relation coefficients out.
Proof.
  unfold seven_signed_code_relation, seven_signed_relation.
  cbn [vec_head].
  now rewrite project_inject.
Qed.

Print Assumptions recalg_graph_murec.
Print Assumptions zigzag_decode_encode.
Print Assumptions seven_signed_relation_murec.
Print Assumptions seven_signed_code_relation_murec.
