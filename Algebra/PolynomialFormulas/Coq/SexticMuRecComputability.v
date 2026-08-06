(* ===================================================================== *)
(*  Direct Mu-recursive certificates for seven signed coefficients.      *)
(*                                                                       *)
(*  This file deliberately uses only the concrete recursive-algebra      *)
(*  layer of the Coq Library of Undecidability Proofs.  In particular,   *)
(*  it does not appeal to extraction, an opaque computability oracle, or  *)
(*  the much larger equivalence between machine models.                  *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia List Ring Vector ZArith.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.

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
  | NatMinus : nat_expression arity -> nat_expression arity ->
      nat_expression arity
  | NatMult : nat_expression arity -> nat_expression arity ->
      nat_expression arity
  | NatDiv2 : nat_expression arity -> nat_expression arity
  | NatMod2 : nat_expression arity -> nat_expression arity
  | NatIfZero : nat_expression arity -> nat_expression arity ->
      nat_expression arity -> nat_expression arity
  | NatEqIndicator : nat_expression arity -> nat_expression arity ->
      nat_expression arity
  | NatBoundedSum : nat_expression arity -> nat_expression (S arity) ->
      nat_expression arity.

Arguments NatConst {arity} _.
Arguments NatVar {arity} _.
Arguments NatSucc {arity} _.
Arguments NatPlus {arity} _ _.
Arguments NatMinus {arity} _ _.
Arguments NatMult {arity} _ _.
Arguments NatDiv2 {arity} _.
Arguments NatMod2 {arity} _.
Arguments NatIfZero {arity} _ _ _.
Arguments NatEqIndicator {arity} _ _.
Arguments NatBoundedSum {arity} _ _.

(* [NatBoundedSum upper body] evaluates [body] at indices
   [0, ..., upper - 1].  In [body], [pos0] is the index and every original
   variable is shifted by one position. *)
Fixpoint eval_nat_expression {arity} (expression : nat_expression arity)
    (v : Vector.t nat arity) : nat :=
  match expression with
  | NatConst constant => constant
  | NatVar variable => vec_pos v variable
  | NatSucc inner => S (eval_nat_expression inner v)
  | NatPlus lhs rhs =>
      eval_nat_expression lhs v + eval_nat_expression rhs v
  | NatMinus lhs rhs =>
      eval_nat_expression lhs v - eval_nat_expression rhs v
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
  | NatBoundedSum upper body =>
      lsum
        (List.map (fun index => eval_nat_expression body (index ## v))
                  (list_an 0 (eval_nat_expression upper v)))
  end.

Definition ra_identity_arguments arity : Vector.t (recalg arity) arity :=
  vec_set_pos (fun variable => ra_proj variable).

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
  | NatMinus lhs rhs =>
      ra_comp ra_minus
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
  | NatBoundedSum upper body =>
      ra_comp (ra_lsum (compile_nat_expression body))
        (compile_nat_expression upper ## ra_identity_arguments arity)
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
    + apply IHexpression.
    + reflexivity.
  - eapply ra_comp2_val.
    + apply IHexpression1.
    + apply IHexpression2.
    + apply ra_plus_val.
  - eapply ra_comp2_val.
    + apply IHexpression1.
    + apply IHexpression2.
    + apply ra_minus_val.
  - eapply ra_comp2_val.
    + apply IHexpression1.
    + apply IHexpression2.
    + apply ra_mult_val.
  - eapply ra_comp1_val.
    + apply IHexpression.
    + apply ra_div2_val.
  - eapply ra_comp1_val.
    + apply IHexpression.
    + apply ra_mod2_val.
  - eapply ra_comp3_val.
    + apply IHexpression1.
    + apply IHexpression2.
    + apply IHexpression3.
    + apply ra_ite_val.
  - rewrite <- nat_eq_code_indicator.
    eapply ra_comp1_val.
    + eapply ra_comp2_val.
      * apply IHexpression1.
      * apply IHexpression2.
      * apply ra_eq_val.
    + apply ra_not_val.
  - exists
      (eval_nat_expression expression1 v ## v); split.
    + apply ra_lsum_spec.
      induction (list_an 0 (eval_nat_expression expression1 v))
        as [|index indices IHindices]; cbn.
      * constructor.
      * constructor.
        -- apply IHexpression2.
        -- exact IHindices.
    + intro variable; analyse pos variable; cbn.
      * apply IHexpression1.
      * unfold ra_identity_arguments. repeat rewrite vec_pos_set.
        apply ra_proj_val.
Qed.

Theorem compile_nat_expression_primitive_recursive {arity}
    (expression : nat_expression arity) :
  prim_rec (compile_nat_expression expression).
Proof.
  induction expression; cbn [compile_nat_expression]; ra prim rec.
  unfold ra_identity_arguments. rewrite vec_pos_set. exact I.
Qed.

(* Convenient interfaces for the two new arithmetic/search forms. *)
Lemma eval_nat_minus {arity} (left right : nat_expression arity) v :
  eval_nat_expression (NatMinus left right) v =
  eval_nat_expression left v - eval_nat_expression right v.
Proof. reflexivity. Qed.

Lemma eval_nat_bounded_sum {arity} (upper : nat_expression arity)
    (body : nat_expression (S arity)) v :
  eval_nat_expression (NatBoundedSum upper body) v =
  lsum
    (List.map (fun index => eval_nat_expression body (index ## v))
              (list_an 0 (eval_nat_expression upper v))).
Proof. reflexivity. Qed.

Definition NatNonzeroIndicator {arity}
    (expression : nat_expression arity) : nat_expression arity :=
  NatIfZero expression (NatConst 0) (NatConst 1).

Definition NatZeroIndicator {arity}
    (expression : nat_expression arity) : nat_expression arity :=
  NatIfZero expression (NatConst 1) (NatConst 0).

Definition NatBoundedExists {arity} (upper : nat_expression arity)
    (predicate : nat_expression (S arity)) : nat_expression arity :=
  NatNonzeroIndicator (NatBoundedSum upper predicate).

Lemma eval_nat_nonzero_indicator {arity}
    (expression : nat_expression arity) v :
  eval_nat_expression (NatNonzeroIndicator expression) v = 1 <->
  eval_nat_expression expression v <> 0.
Proof.
  unfold NatNonzeroIndicator; cbn [eval_nat_expression].
  unfold ite_rel.
  destruct (eval_nat_expression expression v); cbn; lia.
Qed.

Lemma eval_nat_nonzero_indicator_nonzero_iff {arity}
    (expression : nat_expression arity) v :
  eval_nat_expression (NatNonzeroIndicator expression) v <> 0 <->
  eval_nat_expression expression v <> 0.
Proof.
  unfold NatNonzeroIndicator; cbn [eval_nat_expression].
  unfold ite_rel.
  destruct (eval_nat_expression expression v); cbn; lia.
Qed.

Lemma eval_nat_zero_indicator {arity}
    (expression : nat_expression arity) v :
  eval_nat_expression (NatZeroIndicator expression) v = 1 <->
  eval_nat_expression expression v = 0.
Proof.
  unfold NatZeroIndicator; cbn [eval_nat_expression].
  unfold ite_rel.
  destruct (eval_nat_expression expression v); cbn; lia.
Qed.

Lemma lsum_map_nonzero_iff {A : Type} (function : A -> nat) values :
  lsum (List.map function values) <> 0 <->
  exists value, List.In value values /\ function value <> 0.
Proof.
  induction values as [|value values IHvalues]; cbn.
  - firstorder.
  - destruct (Nat.eq_dec (function value) 0) as [Hzero|Hnonzero].
    + rewrite Hzero, Nat.add_0_l, IHvalues.
      split.
      * intros (found & Hfound & Hfound_nonzero).
        exists found; split; auto.
      * intros (found & [<-|Hfound] & Hfound_nonzero).
        -- contradiction.
        -- exists found; auto.
    + split.
      * intro. exists value; auto.
      * intro. lia.
Qed.

Lemma eval_nat_bounded_sum_nonzero_iff {arity}
    (upper : nat_expression arity)
    (body : nat_expression (S arity)) v :
  eval_nat_expression (NatBoundedSum upper body) v <> 0 <->
  exists index,
    index < eval_nat_expression upper v /\
    eval_nat_expression body (index ## v) <> 0.
Proof.
  rewrite eval_nat_bounded_sum, lsum_map_nonzero_iff.
  split.
  - intros (index & Hindex & Hnonzero).
    exists index; split; auto.
    apply list_an_spec in Hindex. lia.
  - intros (index & Hindex & Hnonzero).
    exists index; split; auto.
    apply list_an_spec. lia.
Qed.

Theorem eval_nat_bounded_exists_true_iff {arity}
    (upper : nat_expression arity)
    (predicate : nat_expression (S arity)) v :
  eval_nat_expression (NatBoundedExists upper predicate) v = 1 <->
  exists index,
    index < eval_nat_expression upper v /\
    eval_nat_expression predicate (index ## v) <> 0.
Proof.
  unfold NatBoundedExists.
  rewrite eval_nat_nonzero_indicator.
  apply eval_nat_bounded_sum_nonzero_iff.
Qed.

Theorem eval_nat_bounded_exists_nonzero_iff {arity}
    (upper : nat_expression arity)
    (predicate : nat_expression (S arity)) v :
  eval_nat_expression (NatBoundedExists upper predicate) v <> 0 <->
  exists index,
    index < eval_nat_expression upper v /\
    eval_nat_expression predicate (index ## v) <> 0.
Proof.
  unfold NatBoundedExists.
  rewrite eval_nat_nonzero_indicator_nonzero_iff.
  apply eval_nat_bounded_sum_nonzero_iff.
Qed.

Theorem compile_nat_bounded_exists_outputs_one_iff {arity}
    (upper : nat_expression arity)
    (predicate : nat_expression (S arity)) v :
  ⟦compile_nat_expression (NatBoundedExists upper predicate)⟧ v 1 <->
  exists index,
    index < eval_nat_expression upper v /\
    eval_nat_expression predicate (index ## v) <> 0.
Proof.
  rewrite <- eval_nat_bounded_exists_true_iff.
  split.
  - intro Hrun.
    symmetry.
    eapply ra_rel_fun.
    + exact Hrun.
    + apply compile_nat_expression_correct.
  - intro Heval.
    replace 1 with
      (eval_nat_expression (NatBoundedExists upper predicate) v)
      by lia.
    apply compile_nat_expression_correct.
Qed.

Corollary compile_nat_bounded_exists_primitive_recursive {arity}
    (upper : nat_expression arity)
    (predicate : nat_expression (S arity)) :
  prim_rec (compile_nat_expression (NatBoundedExists upper predicate)).
Proof. apply compile_nat_expression_primitive_recursive. Qed.

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

Definition signed_of_nat_expression {arity}
    (expression : nat_expression arity) : signed_expression arity :=
  {| signed_positive := expression; signed_negative := NatConst 0 |}.

Definition signed_one {arity} : signed_expression arity :=
  signed_of_nat_expression (NatConst 1).

Definition signed_zero {arity} : signed_expression arity :=
  signed_of_nat_expression (NatConst 0).

Fixpoint signed_power {arity} (expression : signed_expression arity)
    (exponent : nat) : signed_expression arity :=
  match exponent with
  | 0 => signed_one
  | S exponent' => signed_mult expression (signed_power expression exponent')
  end.

Fixpoint z_nat_power (base : Z) (exponent : nat) : Z :=
  match exponent with
  | 0 => 1%Z
  | S exponent' => (base * z_nat_power base exponent')%Z
  end.

Lemma eval_signed_of_nat_expression {arity}
    (expression : nat_expression arity) v :
  eval_signed_expression (signed_of_nat_expression expression) v =
  Z.of_nat (eval_nat_expression expression v).
Proof.
  unfold signed_of_nat_expression, eval_signed_expression; cbn.
  lia.
Qed.

Lemma eval_signed_power {arity} (expression : signed_expression arity)
    exponent v :
  eval_signed_expression (signed_power expression exponent) v =
  z_nat_power (eval_signed_expression expression v) exponent.
Proof.
  induction exponent as [|exponent IHexponent]; cbn [signed_power].
  - apply eval_signed_of_nat_expression.
  - rewrite eval_signed_mult, IHexponent. reflexivity.
Qed.

(* This is the expression-level counterpart of
   [SexticRationalRootSearch.homogeneous_eval]: coefficients are ascending,
   and each recursive step clears the denominator by the length of its tail. *)
Fixpoint signed_homogeneous_list_expression {arity}
    (coefficients : list (signed_expression arity))
    (numerator denominator : signed_expression arity) :
    signed_expression arity :=
  match coefficients with
  | List.nil => signed_zero
  | List.cons coefficient coefficients' =>
      signed_plus
        (signed_mult coefficient
          (signed_power denominator (List.length coefficients')))
        (signed_mult numerator
          (signed_homogeneous_list_expression coefficients'
            numerator denominator))
  end.

Fixpoint z_homogeneous_list_value (coefficients : list Z)
    (numerator denominator : Z) : Z :=
  match coefficients with
  | List.nil => 0%Z
  | List.cons coefficient coefficients' =>
      (coefficient * z_nat_power denominator (List.length coefficients') +
       numerator *
         z_homogeneous_list_value coefficients' numerator denominator)%Z
  end.

Theorem eval_signed_homogeneous_list_expression {arity}
    (coefficients : list (signed_expression arity)) numerator denominator
    values :
  eval_signed_expression
    (signed_homogeneous_list_expression coefficients numerator denominator)
    values =
  z_homogeneous_list_value
    (List.map (fun coefficient =>
      eval_signed_expression coefficient values) coefficients)
    (eval_signed_expression numerator values)
    (eval_signed_expression denominator values).
Proof.
  induction coefficients as [|coefficient coefficients IHcoefficients];
    cbn [signed_homogeneous_list_expression z_homogeneous_list_value].
  - apply eval_signed_of_nat_expression.
  - rewrite eval_signed_plus, !eval_signed_mult, eval_signed_power,
      IHcoefficients.
    cbn [List.map z_homogeneous_list_value].
    rewrite length_map. reflexivity.
Qed.

Definition signed_homogeneous_sextic_expression {arity}
    (a0 a1 a2 a3 a4 a5 a6 u v : signed_expression arity) :
    signed_expression arity :=
  let tail5 := signed_plus (signed_mult a5 v) (signed_mult u a6) in
  let tail4 := signed_plus (signed_mult a4 (signed_power v 2))
    (signed_mult u tail5) in
  let tail3 := signed_plus (signed_mult a3 (signed_power v 3))
    (signed_mult u tail4) in
  let tail2 := signed_plus (signed_mult a2 (signed_power v 4))
    (signed_mult u tail3) in
  let tail1 := signed_plus (signed_mult a1 (signed_power v 5))
    (signed_mult u tail2) in
  signed_plus (signed_mult a0 (signed_power v 6))
    (signed_mult u tail1).

Definition homogeneous_sextic_value
    (a0 a1 a2 a3 a4 a5 a6 u v : Z) : Z :=
  (a0 * z_nat_power v 6 + u *
    (a1 * z_nat_power v 5 + u *
      (a2 * z_nat_power v 4 + u *
        (a3 * z_nat_power v 3 + u *
          (a4 * z_nat_power v 2 + u * (a5 * v + u * a6))))))%Z.

Lemma eval_signed_homogeneous_sextic_expression {arity}
    (a0 a1 a2 a3 a4 a5 a6 u v : signed_expression arity) values :
  eval_signed_expression
    (signed_homogeneous_sextic_expression a0 a1 a2 a3 a4 a5 a6 u v)
    values =
  homogeneous_sextic_value
    (eval_signed_expression a0 values)
    (eval_signed_expression a1 values)
    (eval_signed_expression a2 values)
    (eval_signed_expression a3 values)
    (eval_signed_expression a4 values)
    (eval_signed_expression a5 values)
    (eval_signed_expression a6 values)
    (eval_signed_expression u values)
    (eval_signed_expression v values).
Proof.
  unfold signed_homogeneous_sextic_expression,
    homogeneous_sextic_value.
  repeat first
    [ rewrite eval_signed_plus
    | rewrite eval_signed_mult
    | rewrite eval_signed_power ].
  reflexivity.
Qed.

(* The sum of the two truncated differences is the ordinary absolute
   magnitude of the represented integer.  This stays in [nat], so it can be
   used directly as a bounded-search limit. *)
Definition signed_absolute_magnitude_expression {arity}
    (expression : signed_expression arity) : nat_expression arity :=
  NatPlus
    (NatMinus (signed_positive expression) (signed_negative expression))
    (NatMinus (signed_negative expression) (signed_positive expression)).

Lemma eval_signed_absolute_magnitude_expression {arity}
    (expression : signed_expression arity) v :
  Z.of_nat
    (eval_nat_expression
      (signed_absolute_magnitude_expression expression) v) =
  Z.abs (eval_signed_expression expression v).
Proof.
  unfold signed_absolute_magnitude_expression, eval_signed_expression.
  cbn [eval_nat_expression].
  remember (eval_nat_expression (signed_positive expression) v)
    as positive eqn:Hpositive.
  remember (eval_nat_expression (signed_negative expression) v)
    as negative eqn:Hnegative.
  destruct (le_dec negative positive) as [Hle|Hnotle].
  - assert (negative - positive = 0) as Hzero.
    { apply Nat.sub_0_le. exact Hle. }
    rewrite Hzero, Nat.add_0_r, Nat2Z.inj_sub by exact Hle.
    rewrite Z.abs_eq by lia. reflexivity.
  - assert (positive <= negative) as Hle by lia.
    assert (positive - negative = 0) as Hzero.
    { apply Nat.sub_0_le. exact Hle. }
    rewrite Hzero, Nat.add_0_l, Nat2Z.inj_sub by exact Hle.
    rewrite Z.abs_neq by lia. ring.
Qed.

Definition zigzag_magnitude (code : nat) : nat :=
  (zigzag_positive code - zigzag_negative code) +
  (zigzag_negative code - zigzag_positive code).

Lemma zigzag_magnitude_spec code :
  Z.of_nat (zigzag_magnitude code) = Z.abs (zigzag_decode code).
Proof.
  unfold zigzag_magnitude, zigzag_decode.
  destruct
    (le_dec (zigzag_negative code) (zigzag_positive code))
    as [Hle|Hnotle].
  - assert
      (zigzag_negative code - zigzag_positive code = 0) as Hzero.
    { apply Nat.sub_0_le. exact Hle. }
    rewrite Hzero, Nat.add_0_r, Nat2Z.inj_sub by exact Hle.
    rewrite Z.abs_eq by lia. reflexivity.
  - assert
      (zigzag_positive code <= zigzag_negative code) as Hle by lia.
    assert
      (zigzag_positive code - zigzag_negative code = 0) as Hzero.
    { apply Nat.sub_0_le. exact Hle. }
    rewrite Hzero, Nat.add_0_l, Nat2Z.inj_sub by exact Hle.
    rewrite Z.abs_neq by lia. ring.
Qed.

Lemma zigzag_magnitude_zero_iff code :
  zigzag_magnitude code = 0 <-> zigzag_decode code = 0%Z.
Proof.
  split.
  - intro Hzero.
    rewrite <- Z.abs_0_iff.
    pose proof (zigzag_magnitude_spec code) as Hspec.
    rewrite Hzero in Hspec. cbn in Hspec. lia.
  - intro Hzero.
    apply Nat2Z.inj.
    pose proof (zigzag_magnitude_spec code) as Hspec.
    rewrite Hzero in Hspec. cbn in Hspec. lia.
Qed.

Definition signed_coefficient_magnitude_expression {arity}
    (variable : pos arity) : nat_expression arity :=
  signed_absolute_magnitude_expression (signed_coefficient variable).

Lemma eval_signed_coefficient_magnitude_expression {arity}
    (variable : pos arity) values :
  eval_nat_expression
    (signed_coefficient_magnitude_expression variable) values =
  zigzag_magnitude (vec_pos values variable).
Proof. reflexivity. Qed.

Definition signed_zero_indicator_expression {arity}
    (expression : signed_expression arity) : nat_expression arity :=
  NatEqIndicator
    (signed_positive expression) (signed_negative expression).

Lemma eval_signed_zero_indicator_expression {arity}
    (expression : signed_expression arity) v :
  eval_nat_expression (signed_zero_indicator_expression expression) v = 1 <->
  eval_signed_expression expression v = 0%Z.
Proof.
  unfold signed_zero_indicator_expression, eval_signed_expression.
  cbn [eval_nat_expression].
  unfold bool_to_nat.
  destruct
    (Nat.eqb
      (eval_nat_expression (signed_positive expression) v)
      (eval_nat_expression (signed_negative expression) v))
    eqn:Heq; cbn.
  - apply Nat.eqb_eq in Heq. lia.
  - apply Nat.eqb_neq in Heq. lia.
Qed.

Lemma eval_signed_zero_indicator_nonzero_iff {arity}
    (expression : signed_expression arity) v :
  eval_nat_expression (signed_zero_indicator_expression expression) v <> 0
  <-> eval_signed_expression expression v = 0%Z.
Proof.
  unfold signed_zero_indicator_expression, eval_signed_expression.
  cbn [eval_nat_expression].
  unfold bool_to_nat.
  destruct
    (Nat.eqb
      (eval_nat_expression (signed_positive expression) v)
      (eval_nat_expression (signed_negative expression) v))
    eqn:Heq; cbn.
  - apply Nat.eqb_eq in Heq. lia.
  - apply Nat.eqb_neq in Heq. lia.
Qed.

Corollary compile_signed_zero_indicator_primitive_recursive {arity}
    (expression : signed_expression arity) :
  prim_rec
    (compile_nat_expression (signed_zero_indicator_expression expression)).
Proof. apply compile_nat_expression_primitive_recursive. Qed.

(* --------------------------------------------------------------------- *)
(* The concrete homogeneous rational-root search for seven coefficients. *)

Definition encoded_sextic_constant_magnitude
    (coefficients : Vector.t nat 7) : nat :=
  zigzag_magnitude (vec_pos coefficients pos0).

Definition encoded_sextic_leading_magnitude
    (coefficients : Vector.t nat 7) : nat :=
  zigzag_magnitude (vec_pos coefficients pos6).

Definition encoded_sextic_numerator_value
    (coefficients : Vector.t nat 7) (index : nat) : Z :=
  (Z.of_nat index -
   Z.of_nat (encoded_sextic_constant_magnitude coefficients))%Z.

Definition encoded_sextic_denominator_value (index : nat) : Z :=
  Z.of_nat (S index).

Definition encoded_sextic_homogeneous_value
    (coefficients : Vector.t nat 7)
    (numerator_index denominator_index : nat) : Z :=
  homogeneous_sextic_value
    (zigzag_decode (vec_pos coefficients pos0))
    (zigzag_decode (vec_pos coefficients pos1))
    (zigzag_decode (vec_pos coefficients pos2))
    (zigzag_decode (vec_pos coefficients pos3))
    (zigzag_decode (vec_pos coefficients pos4))
    (zigzag_decode (vec_pos coefficients pos5))
    (zigzag_decode (vec_pos coefficients pos6))
    (encoded_sextic_numerator_value coefficients numerator_index)
    (encoded_sextic_denominator_value denominator_index).

(* The denominator-search body receives
   [denominator index, numerator index, a0, ..., a6]. *)
Definition encoded_sextic_numerator_expression : signed_expression 9 :=
  signed_minus
    (signed_of_nat_expression (NatVar pos1))
    (signed_of_nat_expression
      (signed_coefficient_magnitude_expression pos2)).

Definition encoded_sextic_denominator_expression : signed_expression 9 :=
  signed_of_nat_expression (NatSucc (NatVar pos0)).

Definition encoded_sextic_homogeneous_expression : signed_expression 9 :=
  signed_homogeneous_sextic_expression
    (signed_coefficient pos2)
    (signed_coefficient pos3)
    (signed_coefficient pos4)
    (signed_coefficient pos5)
    (signed_coefficient pos6)
    (signed_coefficient pos7)
    (signed_coefficient pos8)
    encoded_sextic_numerator_expression
    encoded_sextic_denominator_expression.

Lemma eval_encoded_sextic_numerator_expression denominator_index
    numerator_index coefficients :
  eval_signed_expression encoded_sextic_numerator_expression
    (denominator_index ## numerator_index ## coefficients) =
  encoded_sextic_numerator_value coefficients numerator_index.
Proof.
  unfold encoded_sextic_numerator_expression,
    encoded_sextic_numerator_value, encoded_sextic_constant_magnitude.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression,
    eval_signed_coefficient_magnitude_expression.
  reflexivity.
Qed.

Lemma eval_encoded_sextic_denominator_expression denominator_index
    numerator_index coefficients :
  eval_signed_expression encoded_sextic_denominator_expression
    (denominator_index ## numerator_index ## coefficients) =
  encoded_sextic_denominator_value denominator_index.
Proof.
  unfold encoded_sextic_denominator_expression,
    encoded_sextic_denominator_value.
  rewrite eval_signed_of_nat_expression. reflexivity.
Qed.

Theorem eval_encoded_sextic_homogeneous_expression denominator_index
    numerator_index coefficients :
  eval_signed_expression encoded_sextic_homogeneous_expression
    (denominator_index ## numerator_index ## coefficients) =
  encoded_sextic_homogeneous_value
    coefficients numerator_index denominator_index.
Proof.
  unfold encoded_sextic_homogeneous_expression,
    encoded_sextic_homogeneous_value.
  rewrite eval_signed_homogeneous_sextic_expression.
  repeat rewrite eval_signed_coefficient.
  rewrite eval_encoded_sextic_numerator_expression,
    eval_encoded_sextic_denominator_expression.
  reflexivity.
Qed.

Definition encoded_sextic_homogeneous_zero_expression : nat_expression 9 :=
  signed_zero_indicator_expression encoded_sextic_homogeneous_expression.

Lemma eval_encoded_sextic_homogeneous_zero_true_iff denominator_index
    numerator_index coefficients :
  eval_nat_expression encoded_sextic_homogeneous_zero_expression
    (denominator_index ## numerator_index ## coefficients) = 1 <->
  encoded_sextic_homogeneous_value
    coefficients numerator_index denominator_index = 0%Z.
Proof.
  unfold encoded_sextic_homogeneous_zero_expression.
  rewrite eval_signed_zero_indicator_expression,
    eval_encoded_sextic_homogeneous_expression.
  reflexivity.
Qed.

Lemma eval_encoded_sextic_homogeneous_zero_nonzero_iff denominator_index
    numerator_index coefficients :
  eval_nat_expression encoded_sextic_homogeneous_zero_expression
    (denominator_index ## numerator_index ## coefficients) <> 0 <->
  encoded_sextic_homogeneous_value
    coefficients numerator_index denominator_index = 0%Z.
Proof.
  unfold encoded_sextic_homogeneous_zero_expression.
  rewrite eval_signed_zero_indicator_nonzero_iff,
    eval_encoded_sextic_homogeneous_expression.
  reflexivity.
Qed.

(* With a numerator index already prepended, [pos7] is the encoded leading
   coefficient [a6]. *)
Definition encoded_sextic_denominator_count_expression : nat_expression 8 :=
  signed_coefficient_magnitude_expression pos7.

Definition encoded_sextic_numerator_predicate : nat_expression 8 :=
  NatBoundedExists encoded_sextic_denominator_count_expression
    encoded_sextic_homogeneous_zero_expression.

Definition encoded_sextic_constant_magnitude_expression : nat_expression 7 :=
  signed_coefficient_magnitude_expression pos0.

Definition encoded_sextic_numerator_count_expression : nat_expression 7 :=
  NatSucc
    (NatMult (NatConst 2) encoded_sextic_constant_magnitude_expression).

Definition encoded_sextic_bounded_root_expression : nat_expression 7 :=
  NatIfZero encoded_sextic_constant_magnitude_expression
    (NatConst 1)
    (NatBoundedExists encoded_sextic_numerator_count_expression
      encoded_sextic_numerator_predicate).

Lemma eval_encoded_sextic_denominator_count_expression numerator_index
    coefficients :
  eval_nat_expression encoded_sextic_denominator_count_expression
    (numerator_index ## coefficients) =
  encoded_sextic_leading_magnitude coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_sextic_constant_magnitude_expression coefficients :
  eval_nat_expression encoded_sextic_constant_magnitude_expression
    coefficients = encoded_sextic_constant_magnitude coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_sextic_numerator_count_expression coefficients :
  eval_nat_expression encoded_sextic_numerator_count_expression coefficients =
  2 * encoded_sextic_constant_magnitude coefficients + 1.
Proof.
  unfold encoded_sextic_numerator_count_expression.
  cbn [eval_nat_expression].
  rewrite eval_encoded_sextic_constant_magnitude_expression. lia.
Qed.

Lemma eval_encoded_sextic_numerator_predicate_true_iff numerator_index
    coefficients :
  eval_nat_expression encoded_sextic_numerator_predicate
    (numerator_index ## coefficients) = 1 <->
  exists denominator_index,
    denominator_index < encoded_sextic_leading_magnitude coefficients /\
    encoded_sextic_homogeneous_value
      coefficients numerator_index denominator_index = 0%Z.
Proof.
  unfold encoded_sextic_numerator_predicate.
  rewrite eval_nat_bounded_exists_true_iff.
  split.
  - intros (denominator_index & Hbound & Hzero).
    exists denominator_index; split.
    + rewrite eval_encoded_sextic_denominator_count_expression in Hbound.
      exact Hbound.
    + apply (proj1
        (eval_encoded_sextic_homogeneous_zero_nonzero_iff
          denominator_index numerator_index coefficients)).
      exact Hzero.
  - intros (denominator_index & Hbound & Hzero).
    exists denominator_index; split.
    + rewrite eval_encoded_sextic_denominator_count_expression.
      exact Hbound.
    + apply (proj2
        (eval_encoded_sextic_homogeneous_zero_nonzero_iff
          denominator_index numerator_index coefficients)).
      exact Hzero.
Qed.

Lemma eval_encoded_sextic_numerator_predicate_nonzero_iff numerator_index
    coefficients :
  eval_nat_expression encoded_sextic_numerator_predicate
    (numerator_index ## coefficients) <> 0 <->
  exists denominator_index,
    denominator_index < encoded_sextic_leading_magnitude coefficients /\
    encoded_sextic_homogeneous_value
      coefficients numerator_index denominator_index = 0%Z.
Proof.
  unfold encoded_sextic_numerator_predicate.
  rewrite eval_nat_bounded_exists_nonzero_iff.
  split.
  - intros (denominator_index & Hbound & Hzero).
    exists denominator_index; split.
    + rewrite eval_encoded_sextic_denominator_count_expression in Hbound.
      exact Hbound.
    + apply (proj1
        (eval_encoded_sextic_homogeneous_zero_nonzero_iff
          denominator_index numerator_index coefficients)).
      exact Hzero.
  - intros (denominator_index & Hbound & Hzero).
    exists denominator_index; split.
    + rewrite eval_encoded_sextic_denominator_count_expression.
      exact Hbound.
    + apply (proj2
        (eval_encoded_sextic_homogeneous_zero_nonzero_iff
          denominator_index numerator_index coefficients)).
      exact Hzero.
Qed.

Definition encoded_sextic_has_bounded_homogeneous_root
    (coefficients : Vector.t nat 7) : Prop :=
  zigzag_decode (vec_pos coefficients pos0) = 0%Z \/
  exists numerator_index,
    numerator_index <
      2 * encoded_sextic_constant_magnitude coefficients + 1 /\
    exists denominator_index,
      denominator_index < encoded_sextic_leading_magnitude coefficients /\
      encoded_sextic_homogeneous_value
        coefficients numerator_index denominator_index = 0%Z.

Theorem eval_encoded_sextic_bounded_root_true_iff coefficients :
  eval_nat_expression encoded_sextic_bounded_root_expression coefficients = 1
  <-> encoded_sextic_has_bounded_homogeneous_root coefficients.
Proof.
  unfold encoded_sextic_bounded_root_expression.
  change
    (ite_rel (encoded_sextic_constant_magnitude coefficients) 1
      (eval_nat_expression
        (NatBoundedExists encoded_sextic_numerator_count_expression
          encoded_sextic_numerator_predicate) coefficients) = 1 <->
      encoded_sextic_has_bounded_homogeneous_root coefficients).
  unfold ite_rel.
  destruct (encoded_sextic_constant_magnitude coefficients)
    as [|constant_magnitude] eqn:Hconstant.
  - split; intro.
    + left. apply zigzag_magnitude_zero_iff.
      exact Hconstant.
    + reflexivity.
  - rewrite eval_nat_bounded_exists_true_iff.
    split.
    + intros (numerator_index & Hbound & Hroot).
      right; exists numerator_index; split.
      * rewrite eval_encoded_sextic_numerator_count_expression in Hbound.
        exact Hbound.
      * apply (proj1
          (eval_encoded_sextic_numerator_predicate_nonzero_iff
            numerator_index coefficients)).
        exact Hroot.
    + intros [Hconstant_zero|
        (numerator_index & Hbound & denominator_index &
          Hdenominator & Hzero)].
      * exfalso.
        assert (Hmagnitude_zero :
            encoded_sextic_constant_magnitude coefficients = 0).
        { unfold encoded_sextic_constant_magnitude.
          apply (proj2 (zigzag_magnitude_zero_iff
            (vec_pos coefficients pos0))).
          exact Hconstant_zero. }
        rewrite Hmagnitude_zero in Hconstant. discriminate.
      * exists numerator_index; split.
        -- rewrite eval_encoded_sextic_numerator_count_expression.
           exact Hbound.
        -- apply (proj2
            (eval_encoded_sextic_numerator_predicate_nonzero_iff
              numerator_index coefficients)).
           exists denominator_index; auto.
Qed.

Lemma encoded_sextic_constant_magnitude_spec coefficients :
  Z.of_nat (encoded_sextic_constant_magnitude coefficients) =
  Z.abs (zigzag_decode (vec_pos coefficients pos0)).
Proof.
  unfold encoded_sextic_constant_magnitude.
  apply zigzag_magnitude_spec.
Qed.

Lemma encoded_sextic_leading_magnitude_spec coefficients :
  Z.of_nat (encoded_sextic_leading_magnitude coefficients) =
  Z.abs (zigzag_decode (vec_pos coefficients pos6)).
Proof.
  unfold encoded_sextic_leading_magnitude.
  apply zigzag_magnitude_spec.
Qed.

Lemma encoded_sextic_numerator_value_spec coefficients index :
  encoded_sextic_numerator_value coefficients index =
  (Z.of_nat index -
   Z.abs (zigzag_decode (vec_pos coefficients pos0)))%Z.
Proof.
  unfold encoded_sextic_numerator_value.
  rewrite encoded_sextic_constant_magnitude_spec. reflexivity.
Qed.

Lemma eval_nat_nonzero_indicator_zero_or_one {arity}
    (expression : nat_expression arity) v :
  eval_nat_expression (NatNonzeroIndicator expression) v = 0 \/
  eval_nat_expression (NatNonzeroIndicator expression) v = 1.
Proof.
  unfold NatNonzeroIndicator.
  cbn [eval_nat_expression]. unfold ite_rel.
  destruct (eval_nat_expression expression v).
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma eval_nat_bounded_exists_zero_or_one {arity}
    (upper : nat_expression arity)
    (predicate : nat_expression (S arity)) v :
  eval_nat_expression (NatBoundedExists upper predicate) v = 0 \/
  eval_nat_expression (NatBoundedExists upper predicate) v = 1.
Proof.
  unfold NatBoundedExists.
  apply eval_nat_nonzero_indicator_zero_or_one.
Qed.

Lemma eval_encoded_sextic_bounded_root_zero_or_one coefficients :
  eval_nat_expression encoded_sextic_bounded_root_expression coefficients = 0
  \/
  eval_nat_expression encoded_sextic_bounded_root_expression coefficients = 1.
Proof.
  unfold encoded_sextic_bounded_root_expression.
  change
    (ite_rel
      (eval_nat_expression encoded_sextic_constant_magnitude_expression
        coefficients)
      1
      (eval_nat_expression
        (NatBoundedExists encoded_sextic_numerator_count_expression
          encoded_sextic_numerator_predicate) coefficients) = 0 \/
     ite_rel
      (eval_nat_expression encoded_sextic_constant_magnitude_expression
        coefficients)
      1
      (eval_nat_expression
        (NatBoundedExists encoded_sextic_numerator_count_expression
          encoded_sextic_numerator_predicate) coefficients) = 1).
  unfold ite_rel.
  destruct
    (eval_nat_expression encoded_sextic_constant_magnitude_expression
      coefficients).
  - right; reflexivity.
  - apply eval_nat_bounded_exists_zero_or_one.
Qed.

Definition encoded_sextic_bounded_rootb
    (coefficients : Vector.t nat 7) : bool :=
  Nat.eqb
    (eval_nat_expression encoded_sextic_bounded_root_expression coefficients)
    1.

Lemma encoded_sextic_bounded_root_indicator coefficients :
  eval_nat_expression encoded_sextic_bounded_root_expression coefficients =
  bool_to_nat (encoded_sextic_bounded_rootb coefficients).
Proof.
  destruct (eval_encoded_sextic_bounded_root_zero_or_one coefficients)
    as [Hzero|Hone].
  - unfold encoded_sextic_bounded_rootb, bool_to_nat.
    rewrite Hzero. reflexivity.
  - unfold encoded_sextic_bounded_rootb, bool_to_nat.
    rewrite Hone. reflexivity.
Qed.

Theorem encoded_sextic_bounded_rootb_true_iff coefficients :
  encoded_sextic_bounded_rootb coefficients = true <->
  encoded_sextic_has_bounded_homogeneous_root coefficients.
Proof.
  unfold encoded_sextic_bounded_rootb.
  rewrite Nat.eqb_eq.
  apply eval_encoded_sextic_bounded_root_true_iff.
Qed.

Definition ra_encoded_sextic_bounded_root : recalg 7 :=
  compile_nat_expression encoded_sextic_bounded_root_expression.

Theorem ra_encoded_sextic_bounded_root_primitive_recursive :
  prim_rec ra_encoded_sextic_bounded_root.
Proof. apply compile_nat_expression_primitive_recursive. Qed.

Lemma ra_encoded_sextic_bounded_root_correct coefficients :
  ⟦ra_encoded_sextic_bounded_root⟧ coefficients
    (bool_to_nat (encoded_sextic_bounded_rootb coefficients)).
Proof.
  unfold ra_encoded_sextic_bounded_root.
  rewrite <- encoded_sextic_bounded_root_indicator.
  apply compile_nat_expression_correct.
Qed.

Definition encoded_sextic_bounded_root_relation
    (coefficients : Vector.t nat 7) (out : nat) : Prop :=
  out = bool_to_nat (encoded_sextic_bounded_rootb coefficients).

Theorem encoded_sextic_bounded_root_relation_murec :
  MuRec_computable encoded_sextic_bounded_root_relation.
Proof.
  unfold encoded_sextic_bounded_root_relation.
  refine (@recalg_graph_murec 7
    (fun coefficients =>
      bool_to_nat (encoded_sextic_bounded_rootb coefficients))
    ra_encoded_sextic_bounded_root _).
  apply ra_encoded_sextic_bounded_root_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* Concrete arithmetic linear-factor search for a monic sextic.          *)

Definition encoded_monic_sextic_height
    (coefficients : Vector.t nat 6) : nat :=
  zigzag_magnitude (vec_pos coefficients pos0) +
  (zigzag_magnitude (vec_pos coefficients pos1) +
  (zigzag_magnitude (vec_pos coefficients pos2) +
  (zigzag_magnitude (vec_pos coefficients pos3) +
  (zigzag_magnitude (vec_pos coefficients pos4) +
   zigzag_magnitude (vec_pos coefficients pos5))))).

Definition encoded_monic_sextic_root_bound
    (coefficients : Vector.t nat 6) : nat :=
  encoded_monic_sextic_height coefficients + 2.

Definition encoded_monic_linear_candidate
    (coefficients : Vector.t nat 6) (index : nat) : Z :=
  (Z.of_nat index -
   Z.of_nat (encoded_monic_sextic_root_bound coefficients))%Z.

Definition encoded_monic_linear_q4 coefficients index : Z :=
  (zigzag_decode (vec_pos coefficients pos5) -
   encoded_monic_linear_candidate coefficients index)%Z.

Definition encoded_monic_linear_q3 coefficients index : Z :=
  (zigzag_decode (vec_pos coefficients pos4) -
   encoded_monic_linear_candidate coefficients index *
     encoded_monic_linear_q4 coefficients index)%Z.

Definition encoded_monic_linear_q2 coefficients index : Z :=
  (zigzag_decode (vec_pos coefficients pos3) -
   encoded_monic_linear_candidate coefficients index *
     encoded_monic_linear_q3 coefficients index)%Z.

Definition encoded_monic_linear_q1 coefficients index : Z :=
  (zigzag_decode (vec_pos coefficients pos2) -
   encoded_monic_linear_candidate coefficients index *
     encoded_monic_linear_q2 coefficients index)%Z.

Definition encoded_monic_linear_q0 coefficients index : Z :=
  (zigzag_decode (vec_pos coefficients pos1) -
   encoded_monic_linear_candidate coefficients index *
     encoded_monic_linear_q1 coefficients index)%Z.

Definition encoded_monic_linear_remainder coefficients index : Z :=
  (zigzag_decode (vec_pos coefficients pos0) -
   encoded_monic_linear_candidate coefficients index *
     encoded_monic_linear_q0 coefficients index)%Z.

Definition encoded_monic_height_expression : nat_expression 6 :=
  NatPlus (signed_coefficient_magnitude_expression pos0)
    (NatPlus (signed_coefficient_magnitude_expression pos1)
      (NatPlus (signed_coefficient_magnitude_expression pos2)
        (NatPlus (signed_coefficient_magnitude_expression pos3)
          (NatPlus (signed_coefficient_magnitude_expression pos4)
            (signed_coefficient_magnitude_expression pos5))))).

Definition encoded_monic_root_bound_expression : nat_expression 6 :=
  NatPlus encoded_monic_height_expression (NatConst 2).

Definition encoded_monic_linear_candidate_count_expression :
    nat_expression 6 :=
  NatSucc (NatMult (NatConst 2) encoded_monic_root_bound_expression).

(* The linear-search body receives [candidate index, f0, ..., f5]. *)
Definition encoded_monic_linear_body_height_expression : nat_expression 7 :=
  NatPlus (signed_coefficient_magnitude_expression pos1)
    (NatPlus (signed_coefficient_magnitude_expression pos2)
      (NatPlus (signed_coefficient_magnitude_expression pos3)
        (NatPlus (signed_coefficient_magnitude_expression pos4)
          (NatPlus (signed_coefficient_magnitude_expression pos5)
            (signed_coefficient_magnitude_expression pos6))))).

Definition encoded_monic_linear_body_root_bound_expression :
    nat_expression 7 :=
  NatPlus encoded_monic_linear_body_height_expression (NatConst 2).

Definition encoded_monic_linear_candidate_expression : signed_expression 7 :=
  signed_minus
    (signed_of_nat_expression (NatVar pos0))
    (signed_of_nat_expression
      encoded_monic_linear_body_root_bound_expression).

Definition encoded_monic_linear_q4_expression : signed_expression 7 :=
  signed_minus (signed_coefficient pos6)
    encoded_monic_linear_candidate_expression.

Definition encoded_monic_linear_q3_expression : signed_expression 7 :=
  signed_minus (signed_coefficient pos5)
    (signed_mult encoded_monic_linear_candidate_expression
      encoded_monic_linear_q4_expression).

Definition encoded_monic_linear_q2_expression : signed_expression 7 :=
  signed_minus (signed_coefficient pos4)
    (signed_mult encoded_monic_linear_candidate_expression
      encoded_monic_linear_q3_expression).

Definition encoded_monic_linear_q1_expression : signed_expression 7 :=
  signed_minus (signed_coefficient pos3)
    (signed_mult encoded_monic_linear_candidate_expression
      encoded_monic_linear_q2_expression).

Definition encoded_monic_linear_q0_expression : signed_expression 7 :=
  signed_minus (signed_coefficient pos2)
    (signed_mult encoded_monic_linear_candidate_expression
      encoded_monic_linear_q1_expression).

Definition encoded_monic_linear_remainder_expression :
    signed_expression 7 :=
  signed_minus (signed_coefficient pos1)
    (signed_mult encoded_monic_linear_candidate_expression
      encoded_monic_linear_q0_expression).

Definition encoded_monic_linear_remainder_zero_expression :
    nat_expression 7 :=
  signed_zero_indicator_expression encoded_monic_linear_remainder_expression.

Definition encoded_monic_has_linear_factor_expression : nat_expression 6 :=
  NatBoundedExists encoded_monic_linear_candidate_count_expression
    encoded_monic_linear_remainder_zero_expression.

Lemma eval_encoded_monic_height_expression coefficients :
  eval_nat_expression encoded_monic_height_expression coefficients =
  encoded_monic_sextic_height coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_monic_root_bound_expression coefficients :
  eval_nat_expression encoded_monic_root_bound_expression coefficients =
  encoded_monic_sextic_root_bound coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_monic_linear_candidate_count_expression coefficients :
  eval_nat_expression encoded_monic_linear_candidate_count_expression
    coefficients =
  2 * encoded_monic_sextic_root_bound coefficients + 1.
Proof.
  unfold encoded_monic_linear_candidate_count_expression.
  cbn [eval_nat_expression].
  rewrite eval_encoded_monic_root_bound_expression. lia.
Qed.

Lemma eval_encoded_monic_linear_body_root_bound_expression index
    coefficients :
  eval_nat_expression encoded_monic_linear_body_root_bound_expression
    (index ## coefficients) =
  encoded_monic_sextic_root_bound coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_monic_linear_candidate_expression index coefficients :
  eval_signed_expression encoded_monic_linear_candidate_expression
    (index ## coefficients) =
  encoded_monic_linear_candidate coefficients index.
Proof.
  unfold encoded_monic_linear_candidate_expression,
    encoded_monic_linear_candidate.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression,
    eval_encoded_monic_linear_body_root_bound_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_linear_q4_expression index coefficients :
  eval_signed_expression encoded_monic_linear_q4_expression
    (index ## coefficients) = encoded_monic_linear_q4 coefficients index.
Proof.
  unfold encoded_monic_linear_q4_expression,
    encoded_monic_linear_q4.
  rewrite eval_signed_minus, eval_signed_coefficient,
    eval_encoded_monic_linear_candidate_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_linear_q3_expression index coefficients :
  eval_signed_expression encoded_monic_linear_q3_expression
    (index ## coefficients) = encoded_monic_linear_q3 coefficients index.
Proof.
  unfold encoded_monic_linear_q3_expression,
    encoded_monic_linear_q3.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_linear_candidate_expression,
    eval_encoded_monic_linear_q4_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_linear_q2_expression index coefficients :
  eval_signed_expression encoded_monic_linear_q2_expression
    (index ## coefficients) = encoded_monic_linear_q2 coefficients index.
Proof.
  unfold encoded_monic_linear_q2_expression,
    encoded_monic_linear_q2.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_linear_candidate_expression,
    eval_encoded_monic_linear_q3_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_linear_q1_expression index coefficients :
  eval_signed_expression encoded_monic_linear_q1_expression
    (index ## coefficients) = encoded_monic_linear_q1 coefficients index.
Proof.
  unfold encoded_monic_linear_q1_expression,
    encoded_monic_linear_q1.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_linear_candidate_expression,
    eval_encoded_monic_linear_q2_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_linear_q0_expression index coefficients :
  eval_signed_expression encoded_monic_linear_q0_expression
    (index ## coefficients) = encoded_monic_linear_q0 coefficients index.
Proof.
  unfold encoded_monic_linear_q0_expression,
    encoded_monic_linear_q0.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_linear_candidate_expression,
    eval_encoded_monic_linear_q1_expression.
  reflexivity.
Qed.

Theorem eval_encoded_monic_linear_remainder_expression index coefficients :
  eval_signed_expression encoded_monic_linear_remainder_expression
    (index ## coefficients) =
  encoded_monic_linear_remainder coefficients index.
Proof.
  unfold encoded_monic_linear_remainder_expression,
    encoded_monic_linear_remainder.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_linear_candidate_expression,
    eval_encoded_monic_linear_q0_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_linear_remainder_zero_nonzero_iff index
    coefficients :
  eval_nat_expression encoded_monic_linear_remainder_zero_expression
    (index ## coefficients) <> 0 <->
  encoded_monic_linear_remainder coefficients index = 0%Z.
Proof.
  unfold encoded_monic_linear_remainder_zero_expression.
  rewrite eval_signed_zero_indicator_nonzero_iff,
    eval_encoded_monic_linear_remainder_expression.
  reflexivity.
Qed.

Definition encoded_monic_has_bounded_linear_factor
    (coefficients : Vector.t nat 6) : Prop :=
  exists index,
    index < 2 * encoded_monic_sextic_root_bound coefficients + 1 /\
    encoded_monic_linear_remainder coefficients index = 0%Z.

Theorem eval_encoded_monic_has_linear_factor_true_iff coefficients :
  eval_nat_expression encoded_monic_has_linear_factor_expression
    coefficients = 1 <->
  encoded_monic_has_bounded_linear_factor coefficients.
Proof.
  unfold encoded_monic_has_linear_factor_expression.
  rewrite eval_nat_bounded_exists_true_iff.
  split.
  - intros (index & Hbound & Hzero).
    exists index; split.
    + rewrite eval_encoded_monic_linear_candidate_count_expression in Hbound.
      exact Hbound.
    + apply (proj1
        (eval_encoded_monic_linear_remainder_zero_nonzero_iff
          index coefficients)).
      exact Hzero.
  - intros (index & Hbound & Hzero).
    exists index; split.
    + rewrite eval_encoded_monic_linear_candidate_count_expression.
      exact Hbound.
    + apply (proj2
        (eval_encoded_monic_linear_remainder_zero_nonzero_iff
          index coefficients)).
      exact Hzero.
Qed.

Definition encoded_monic_has_linear_factorb
    (coefficients : Vector.t nat 6) : bool :=
  Nat.eqb
    (eval_nat_expression encoded_monic_has_linear_factor_expression
      coefficients) 1.

Lemma encoded_monic_has_linear_factor_indicator coefficients :
  eval_nat_expression encoded_monic_has_linear_factor_expression
    coefficients =
  bool_to_nat (encoded_monic_has_linear_factorb coefficients).
Proof.
  unfold encoded_monic_has_linear_factorb,
    encoded_monic_has_linear_factor_expression, bool_to_nat.
  destruct
    (eval_nat_bounded_exists_zero_or_one
      encoded_monic_linear_candidate_count_expression
      encoded_monic_linear_remainder_zero_expression coefficients)
    as [Hzero|Hone].
  - rewrite Hzero. reflexivity.
  - rewrite Hone. reflexivity.
Qed.

Theorem encoded_monic_has_linear_factorb_true_iff coefficients :
  encoded_monic_has_linear_factorb coefficients = true <->
  encoded_monic_has_bounded_linear_factor coefficients.
Proof.
  unfold encoded_monic_has_linear_factorb.
  rewrite Nat.eqb_eq.
  apply eval_encoded_monic_has_linear_factor_true_iff.
Qed.

Definition ra_encoded_monic_has_linear_factor : recalg 6 :=
  compile_nat_expression encoded_monic_has_linear_factor_expression.

Theorem ra_encoded_monic_has_linear_factor_primitive_recursive :
  prim_rec ra_encoded_monic_has_linear_factor.
Proof. apply compile_nat_expression_primitive_recursive. Qed.

Definition encoded_monic_linear_factor_relation
    (coefficients : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat (encoded_monic_has_linear_factorb coefficients).

Theorem encoded_monic_linear_factor_relation_murec :
  MuRec_computable encoded_monic_linear_factor_relation.
Proof.
  unfold encoded_monic_linear_factor_relation.
  refine (@recalg_graph_murec 6
    (fun coefficients =>
      bool_to_nat (encoded_monic_has_linear_factorb coefficients))
    ra_encoded_monic_has_linear_factor _).
  intro coefficients.
  unfold ra_encoded_monic_has_linear_factor.
  rewrite <- encoded_monic_has_linear_factor_indicator.
  apply compile_nat_expression_correct.
Qed.

(* Quadratic-factor search.  Its nested body receives
   [c index, b index, f0, ..., f5]. *)
Definition encoded_monic_quadratic_b_value coefficients b_index : Z :=
  (Z.of_nat b_index -
   Z.of_nat (2 * encoded_monic_sextic_root_bound coefficients))%Z.

Definition encoded_monic_quadratic_c_value coefficients c_index : Z :=
  (Z.of_nat c_index -
   Z.of_nat
     (encoded_monic_sextic_root_bound coefficients *
      encoded_monic_sextic_root_bound coefficients))%Z.

Definition encoded_monic_quadratic_q3 coefficients b_index : Z :=
  (zigzag_decode (vec_pos coefficients pos5) -
   encoded_monic_quadratic_b_value coefficients b_index)%Z.

Definition encoded_monic_quadratic_q2 coefficients b_index c_index : Z :=
  (zigzag_decode (vec_pos coefficients pos4) -
   encoded_monic_quadratic_c_value coefficients c_index -
   encoded_monic_quadratic_b_value coefficients b_index *
     encoded_monic_quadratic_q3 coefficients b_index)%Z.

Definition encoded_monic_quadratic_q1 coefficients b_index c_index : Z :=
  (zigzag_decode (vec_pos coefficients pos3) -
   encoded_monic_quadratic_b_value coefficients b_index *
     encoded_monic_quadratic_q2 coefficients b_index c_index -
   encoded_monic_quadratic_c_value coefficients c_index *
     encoded_monic_quadratic_q3 coefficients b_index)%Z.

Definition encoded_monic_quadratic_q0 coefficients b_index c_index : Z :=
  (zigzag_decode (vec_pos coefficients pos2) -
   encoded_monic_quadratic_b_value coefficients b_index *
     encoded_monic_quadratic_q1 coefficients b_index c_index -
   encoded_monic_quadratic_c_value coefficients c_index *
     encoded_monic_quadratic_q2 coefficients b_index c_index)%Z.

Definition encoded_monic_quadratic_remainder1 coefficients b_index c_index :
    Z :=
  (zigzag_decode (vec_pos coefficients pos1) -
   (encoded_monic_quadratic_b_value coefficients b_index *
      encoded_monic_quadratic_q0 coefficients b_index c_index +
    encoded_monic_quadratic_c_value coefficients c_index *
      encoded_monic_quadratic_q1 coefficients b_index c_index))%Z.

Definition encoded_monic_quadratic_remainder0 coefficients b_index c_index :
    Z :=
  (zigzag_decode (vec_pos coefficients pos0) -
   encoded_monic_quadratic_c_value coefficients c_index *
     encoded_monic_quadratic_q0 coefficients b_index c_index)%Z.

Definition NatSymmetricCount {arity} (radius : nat_expression arity) :
    nat_expression arity :=
  NatSucc (NatMult (NatConst 2) radius).

Definition signed_symmetric_candidate {arity} (index : pos arity)
    (radius : nat_expression arity) : signed_expression arity :=
  signed_minus (signed_of_nat_expression (NatVar index))
    (signed_of_nat_expression radius).

Definition encoded_monic_quadratic_b_count_expression : nat_expression 6 :=
  NatSymmetricCount
    (NatMult (NatConst 2) encoded_monic_root_bound_expression).

(* After [b_index] is prepended, coefficients occupy [pos1..pos6]. *)
Definition encoded_monic_quadratic_outer_height_expression :
    nat_expression 7 :=
  encoded_monic_linear_body_height_expression.

Definition encoded_monic_quadratic_outer_root_bound_expression :
    nat_expression 7 :=
  NatPlus encoded_monic_quadratic_outer_height_expression (NatConst 2).

Definition encoded_monic_quadratic_c_radius_outer_expression :
    nat_expression 7 :=
  NatMult encoded_monic_quadratic_outer_root_bound_expression
    encoded_monic_quadratic_outer_root_bound_expression.

Definition encoded_monic_quadratic_c_count_expression : nat_expression 7 :=
  NatSymmetricCount encoded_monic_quadratic_c_radius_outer_expression.

(* Inside the second bound, coefficients occupy [pos2..pos7]. *)
Definition encoded_monic_quadratic_body_height_expression : nat_expression 8 :=
  NatPlus (signed_coefficient_magnitude_expression pos2)
    (NatPlus (signed_coefficient_magnitude_expression pos3)
      (NatPlus (signed_coefficient_magnitude_expression pos4)
        (NatPlus (signed_coefficient_magnitude_expression pos5)
          (NatPlus (signed_coefficient_magnitude_expression pos6)
            (signed_coefficient_magnitude_expression pos7))))).

Definition encoded_monic_quadratic_body_root_bound_expression :
    nat_expression 8 :=
  NatPlus encoded_monic_quadratic_body_height_expression (NatConst 2).

Definition encoded_monic_quadratic_b_radius_body_expression :
    nat_expression 8 :=
  NatMult (NatConst 2) encoded_monic_quadratic_body_root_bound_expression.

Definition encoded_monic_quadratic_c_radius_body_expression :
    nat_expression 8 :=
  NatMult encoded_monic_quadratic_body_root_bound_expression
    encoded_monic_quadratic_body_root_bound_expression.

Definition encoded_monic_quadratic_b_expression : signed_expression 8 :=
  signed_symmetric_candidate pos1
    encoded_monic_quadratic_b_radius_body_expression.

Definition encoded_monic_quadratic_c_expression : signed_expression 8 :=
  signed_symmetric_candidate pos0
    encoded_monic_quadratic_c_radius_body_expression.

Definition encoded_monic_quadratic_q3_expression : signed_expression 8 :=
  signed_minus (signed_coefficient pos7)
    encoded_monic_quadratic_b_expression.

Definition encoded_monic_quadratic_q2_expression : signed_expression 8 :=
  signed_minus
    (signed_minus (signed_coefficient pos6)
      encoded_monic_quadratic_c_expression)
    (signed_mult encoded_monic_quadratic_b_expression
      encoded_monic_quadratic_q3_expression).

Definition encoded_monic_quadratic_q1_expression : signed_expression 8 :=
  signed_minus
    (signed_minus (signed_coefficient pos5)
      (signed_mult encoded_monic_quadratic_b_expression
        encoded_monic_quadratic_q2_expression))
    (signed_mult encoded_monic_quadratic_c_expression
      encoded_monic_quadratic_q3_expression).

Definition encoded_monic_quadratic_q0_expression : signed_expression 8 :=
  signed_minus
    (signed_minus (signed_coefficient pos4)
      (signed_mult encoded_monic_quadratic_b_expression
        encoded_monic_quadratic_q1_expression))
    (signed_mult encoded_monic_quadratic_c_expression
      encoded_monic_quadratic_q2_expression).

Definition encoded_monic_quadratic_remainder1_expression :
    signed_expression 8 :=
  signed_minus (signed_coefficient pos3)
    (signed_plus
      (signed_mult encoded_monic_quadratic_b_expression
        encoded_monic_quadratic_q0_expression)
      (signed_mult encoded_monic_quadratic_c_expression
        encoded_monic_quadratic_q1_expression)).

Definition encoded_monic_quadratic_remainder0_expression :
    signed_expression 8 :=
  signed_minus (signed_coefficient pos2)
    (signed_mult encoded_monic_quadratic_c_expression
      encoded_monic_quadratic_q0_expression).

Definition encoded_monic_quadratic_remainders_zero_expression :
    nat_expression 8 :=
  NatMult
    (signed_zero_indicator_expression
      encoded_monic_quadratic_remainder1_expression)
    (signed_zero_indicator_expression
      encoded_monic_quadratic_remainder0_expression).

Definition encoded_monic_quadratic_outer_predicate : nat_expression 7 :=
  NatBoundedExists encoded_monic_quadratic_c_count_expression
    encoded_monic_quadratic_remainders_zero_expression.

Definition encoded_monic_has_quadratic_factor_expression : nat_expression 6 :=
  NatBoundedExists encoded_monic_quadratic_b_count_expression
    encoded_monic_quadratic_outer_predicate.

Lemma eval_encoded_monic_quadratic_b_count_expression coefficients :
  eval_nat_expression encoded_monic_quadratic_b_count_expression
    coefficients =
  2 * (2 * encoded_monic_sextic_root_bound coefficients) + 1.
Proof.
  unfold encoded_monic_quadratic_b_count_expression, NatSymmetricCount.
  cbn [eval_nat_expression].
  rewrite eval_encoded_monic_root_bound_expression. lia.
Qed.

Lemma eval_encoded_monic_quadratic_outer_root_bound_expression b_index
    coefficients :
  eval_nat_expression encoded_monic_quadratic_outer_root_bound_expression
    (b_index ## coefficients) =
  encoded_monic_sextic_root_bound coefficients.
Proof.
  change
    (eval_nat_expression encoded_monic_linear_body_root_bound_expression
      (b_index ## coefficients) =
     encoded_monic_sextic_root_bound coefficients).
  apply eval_encoded_monic_linear_body_root_bound_expression.
Qed.

Lemma eval_encoded_monic_quadratic_c_count_expression b_index coefficients :
  eval_nat_expression encoded_monic_quadratic_c_count_expression
    (b_index ## coefficients) =
  2 * (encoded_monic_sextic_root_bound coefficients *
       encoded_monic_sextic_root_bound coefficients) + 1.
Proof.
  unfold encoded_monic_quadratic_c_count_expression,
    encoded_monic_quadratic_c_radius_outer_expression, NatSymmetricCount.
  cbn [eval_nat_expression].
  rewrite !eval_encoded_monic_quadratic_outer_root_bound_expression. lia.
Qed.

Lemma eval_encoded_monic_quadratic_b_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_b_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_b_value coefficients b_index.
Proof.
  unfold encoded_monic_quadratic_b_expression,
    signed_symmetric_candidate, encoded_monic_quadratic_b_value.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_quadratic_c_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_c_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_c_value coefficients c_index.
Proof.
  unfold encoded_monic_quadratic_c_expression,
    signed_symmetric_candidate, encoded_monic_quadratic_c_value.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_quadratic_q3_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_q3_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_q3 coefficients b_index.
Proof.
  unfold encoded_monic_quadratic_q3_expression,
    encoded_monic_quadratic_q3.
  rewrite eval_signed_minus, eval_signed_coefficient,
    eval_encoded_monic_quadratic_b_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_quadratic_q2_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_q2_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_q2 coefficients b_index c_index.
Proof.
  unfold encoded_monic_quadratic_q2_expression,
    encoded_monic_quadratic_q2.
  rewrite !eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_quadratic_b_expression,
    eval_encoded_monic_quadratic_c_expression,
    eval_encoded_monic_quadratic_q3_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_quadratic_q1_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_q1_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_q1 coefficients b_index c_index.
Proof.
  unfold encoded_monic_quadratic_q1_expression,
    encoded_monic_quadratic_q1.
  rewrite !eval_signed_minus, eval_signed_coefficient, !eval_signed_mult,
    eval_encoded_monic_quadratic_b_expression,
    eval_encoded_monic_quadratic_c_expression,
    eval_encoded_monic_quadratic_q2_expression,
    eval_encoded_monic_quadratic_q3_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_quadratic_q0_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_q0_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_q0 coefficients b_index c_index.
Proof.
  unfold encoded_monic_quadratic_q0_expression,
    encoded_monic_quadratic_q0.
  rewrite !eval_signed_minus, eval_signed_coefficient, !eval_signed_mult,
    eval_encoded_monic_quadratic_b_expression,
    eval_encoded_monic_quadratic_c_expression,
    eval_encoded_monic_quadratic_q1_expression,
    eval_encoded_monic_quadratic_q2_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_quadratic_remainder1_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_remainder1_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_remainder1 coefficients b_index c_index.
Proof.
  unfold encoded_monic_quadratic_remainder1_expression,
    encoded_monic_quadratic_remainder1.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_plus,
    !eval_signed_mult, eval_encoded_monic_quadratic_b_expression,
    eval_encoded_monic_quadratic_c_expression,
    eval_encoded_monic_quadratic_q0_expression,
    eval_encoded_monic_quadratic_q1_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_quadratic_remainder0_expression c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_quadratic_remainder0_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_quadratic_remainder0 coefficients b_index c_index.
Proof.
  unfold encoded_monic_quadratic_remainder0_expression,
    encoded_monic_quadratic_remainder0.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_quadratic_c_expression,
    eval_encoded_monic_quadratic_q0_expression.
  reflexivity.
Qed.

Lemma nat_product_nonzero_iff left right :
  left * right <> 0 <-> left <> 0 /\ right <> 0.
Proof. rewrite Nat.mul_eq_0. tauto. Qed.

Lemma eval_encoded_monic_quadratic_remainders_zero_nonzero_iff
    c_index b_index coefficients :
  eval_nat_expression encoded_monic_quadratic_remainders_zero_expression
    (c_index ## b_index ## coefficients) <> 0 <->
  encoded_monic_quadratic_remainder1 coefficients b_index c_index = 0%Z /\
  encoded_monic_quadratic_remainder0 coefficients b_index c_index = 0%Z.
Proof.
  unfold encoded_monic_quadratic_remainders_zero_expression.
  cbn [eval_nat_expression]. rewrite nat_product_nonzero_iff.
  rewrite !eval_signed_zero_indicator_nonzero_iff,
    eval_encoded_monic_quadratic_remainder1_expression,
    eval_encoded_monic_quadratic_remainder0_expression.
  reflexivity.
Qed.

Definition encoded_monic_has_bounded_quadratic_factor
    (coefficients : Vector.t nat 6) : Prop :=
  exists b_index,
    b_index < 2 * (2 * encoded_monic_sextic_root_bound coefficients) + 1 /\
  exists c_index,
    c_index <
      2 * (encoded_monic_sextic_root_bound coefficients *
           encoded_monic_sextic_root_bound coefficients) + 1 /\
    encoded_monic_quadratic_remainder1 coefficients b_index c_index = 0%Z /\
    encoded_monic_quadratic_remainder0 coefficients b_index c_index = 0%Z.

Theorem eval_encoded_monic_has_quadratic_factor_true_iff coefficients :
  eval_nat_expression encoded_monic_has_quadratic_factor_expression
    coefficients = 1 <->
  encoded_monic_has_bounded_quadratic_factor coefficients.
Proof.
  unfold encoded_monic_has_quadratic_factor_expression.
  rewrite eval_nat_bounded_exists_true_iff.
  split.
  - intros (b_index & Hb & Houter).
    unfold encoded_monic_quadratic_outer_predicate in Houter.
    rewrite eval_nat_bounded_exists_nonzero_iff in Houter.
    destruct Houter as (c_index & Hc & Hremainders).
    exists b_index; split.
    + rewrite eval_encoded_monic_quadratic_b_count_expression in Hb.
      exact Hb.
    + exists c_index; split.
      * rewrite eval_encoded_monic_quadratic_c_count_expression in Hc.
        exact Hc.
      * apply (proj1
          (eval_encoded_monic_quadratic_remainders_zero_nonzero_iff
            c_index b_index coefficients)). exact Hremainders.
  - intros (b_index & Hb & c_index & Hc & Hremainder1 & Hremainder0).
    exists b_index; split.
    + rewrite eval_encoded_monic_quadratic_b_count_expression. exact Hb.
    + unfold encoded_monic_quadratic_outer_predicate.
      rewrite eval_nat_bounded_exists_nonzero_iff.
      exists c_index; split.
      * rewrite eval_encoded_monic_quadratic_c_count_expression. exact Hc.
      * apply (proj2
          (eval_encoded_monic_quadratic_remainders_zero_nonzero_iff
            c_index b_index coefficients)). auto.
Qed.

Definition ra_encoded_monic_has_quadratic_factor : recalg 6 :=
  compile_nat_expression encoded_monic_has_quadratic_factor_expression.

Theorem ra_encoded_monic_has_quadratic_factor_primitive_recursive :
  prim_rec ra_encoded_monic_has_quadratic_factor.
Proof. apply compile_nat_expression_primitive_recursive. Qed.

(* Cubic-factor search.  Its innermost body receives
   [d index, c index, b index, f0, ..., f5]. *)
Definition encoded_monic_cubic_b_value coefficients b_index : Z :=
  (Z.of_nat b_index -
   Z.of_nat (3 * encoded_monic_sextic_root_bound coefficients))%Z.

Definition encoded_monic_cubic_c_value coefficients c_index : Z :=
  (Z.of_nat c_index -
   Z.of_nat
     (3 * encoded_monic_sextic_root_bound coefficients *
      encoded_monic_sextic_root_bound coefficients))%Z.

Definition encoded_monic_cubic_d_value coefficients d_index : Z :=
  (Z.of_nat d_index -
   Z.of_nat
     (encoded_monic_sextic_root_bound coefficients *
      encoded_monic_sextic_root_bound coefficients *
      encoded_monic_sextic_root_bound coefficients))%Z.

Definition encoded_monic_cubic_q2 coefficients b_index : Z :=
  (zigzag_decode (vec_pos coefficients pos5) -
   encoded_monic_cubic_b_value coefficients b_index)%Z.

Definition encoded_monic_cubic_q1 coefficients b_index c_index : Z :=
  (zigzag_decode (vec_pos coefficients pos4) -
   encoded_monic_cubic_c_value coefficients c_index -
   encoded_monic_cubic_b_value coefficients b_index *
     encoded_monic_cubic_q2 coefficients b_index)%Z.

Definition encoded_monic_cubic_q0 coefficients b_index c_index d_index : Z :=
  (zigzag_decode (vec_pos coefficients pos3) -
   encoded_monic_cubic_d_value coefficients d_index -
   encoded_monic_cubic_b_value coefficients b_index *
     encoded_monic_cubic_q1 coefficients b_index c_index -
   encoded_monic_cubic_c_value coefficients c_index *
     encoded_monic_cubic_q2 coefficients b_index)%Z.

Definition encoded_monic_cubic_remainder2 coefficients b_index c_index
    d_index : Z :=
  (zigzag_decode (vec_pos coefficients pos2) -
   (encoded_monic_cubic_b_value coefficients b_index *
      encoded_monic_cubic_q0 coefficients b_index c_index d_index +
    encoded_monic_cubic_c_value coefficients c_index *
      encoded_monic_cubic_q1 coefficients b_index c_index +
    encoded_monic_cubic_d_value coefficients d_index *
      encoded_monic_cubic_q2 coefficients b_index))%Z.

Definition encoded_monic_cubic_remainder1 coefficients b_index c_index
    d_index : Z :=
  (zigzag_decode (vec_pos coefficients pos1) -
   (encoded_monic_cubic_c_value coefficients c_index *
      encoded_monic_cubic_q0 coefficients b_index c_index d_index +
    encoded_monic_cubic_d_value coefficients d_index *
      encoded_monic_cubic_q1 coefficients b_index c_index))%Z.

Definition encoded_monic_cubic_remainder0 coefficients b_index c_index
    d_index : Z :=
  (zigzag_decode (vec_pos coefficients pos0) -
   encoded_monic_cubic_d_value coefficients d_index *
     encoded_monic_cubic_q0 coefficients b_index c_index d_index)%Z.

Definition encoded_monic_cubic_b_count_expression : nat_expression 6 :=
  NatSymmetricCount
    (NatMult (NatConst 3) encoded_monic_root_bound_expression).

Definition encoded_monic_cubic_c_radius_outer_expression : nat_expression 7 :=
  NatMult
    (NatMult (NatConst 3)
      encoded_monic_quadratic_outer_root_bound_expression)
    encoded_monic_quadratic_outer_root_bound_expression.

Definition encoded_monic_cubic_c_count_expression : nat_expression 7 :=
  NatSymmetricCount encoded_monic_cubic_c_radius_outer_expression.

(* After [c_index,b_index], the root-bound expression is the quadratic-body
   one, since coefficients again occupy [pos2..pos7]. *)
Definition encoded_monic_cubic_d_radius_middle_expression : nat_expression 8 :=
  NatMult
    (NatMult encoded_monic_quadratic_body_root_bound_expression
      encoded_monic_quadratic_body_root_bound_expression)
    encoded_monic_quadratic_body_root_bound_expression.

Definition encoded_monic_cubic_d_count_expression : nat_expression 8 :=
  NatSymmetricCount encoded_monic_cubic_d_radius_middle_expression.

Definition encoded_monic_cubic_body_height_expression : nat_expression 9 :=
  NatPlus (signed_coefficient_magnitude_expression pos3)
    (NatPlus (signed_coefficient_magnitude_expression pos4)
      (NatPlus (signed_coefficient_magnitude_expression pos5)
        (NatPlus (signed_coefficient_magnitude_expression pos6)
          (NatPlus (signed_coefficient_magnitude_expression pos7)
            (signed_coefficient_magnitude_expression pos8))))).

Definition encoded_monic_cubic_body_root_bound_expression : nat_expression 9 :=
  NatPlus encoded_monic_cubic_body_height_expression (NatConst 2).

Definition encoded_monic_cubic_b_radius_body_expression : nat_expression 9 :=
  NatMult (NatConst 3) encoded_monic_cubic_body_root_bound_expression.

Definition encoded_monic_cubic_c_radius_body_expression : nat_expression 9 :=
  NatMult
    (NatMult (NatConst 3) encoded_monic_cubic_body_root_bound_expression)
    encoded_monic_cubic_body_root_bound_expression.

Definition encoded_monic_cubic_d_radius_body_expression : nat_expression 9 :=
  NatMult
    (NatMult encoded_monic_cubic_body_root_bound_expression
      encoded_monic_cubic_body_root_bound_expression)
    encoded_monic_cubic_body_root_bound_expression.

Definition encoded_monic_cubic_b_expression : signed_expression 9 :=
  signed_symmetric_candidate pos2 encoded_monic_cubic_b_radius_body_expression.

Definition encoded_monic_cubic_c_expression : signed_expression 9 :=
  signed_symmetric_candidate pos1 encoded_monic_cubic_c_radius_body_expression.

Definition encoded_monic_cubic_d_expression : signed_expression 9 :=
  signed_symmetric_candidate pos0 encoded_monic_cubic_d_radius_body_expression.

Definition encoded_monic_cubic_q2_expression : signed_expression 9 :=
  signed_minus (signed_coefficient pos8) encoded_monic_cubic_b_expression.

Definition encoded_monic_cubic_q1_expression : signed_expression 9 :=
  signed_minus
    (signed_minus (signed_coefficient pos7) encoded_monic_cubic_c_expression)
    (signed_mult encoded_monic_cubic_b_expression
      encoded_monic_cubic_q2_expression).

Definition encoded_monic_cubic_q0_expression : signed_expression 9 :=
  signed_minus
    (signed_minus
      (signed_minus (signed_coefficient pos6) encoded_monic_cubic_d_expression)
      (signed_mult encoded_monic_cubic_b_expression
        encoded_monic_cubic_q1_expression))
    (signed_mult encoded_monic_cubic_c_expression
      encoded_monic_cubic_q2_expression).

Definition encoded_monic_cubic_remainder2_expression : signed_expression 9 :=
  signed_minus (signed_coefficient pos5)
    (signed_plus
      (signed_plus
        (signed_mult encoded_monic_cubic_b_expression
          encoded_monic_cubic_q0_expression)
        (signed_mult encoded_monic_cubic_c_expression
          encoded_monic_cubic_q1_expression))
      (signed_mult encoded_monic_cubic_d_expression
        encoded_monic_cubic_q2_expression)).

Definition encoded_monic_cubic_remainder1_expression : signed_expression 9 :=
  signed_minus (signed_coefficient pos4)
    (signed_plus
      (signed_mult encoded_monic_cubic_c_expression
        encoded_monic_cubic_q0_expression)
      (signed_mult encoded_monic_cubic_d_expression
        encoded_monic_cubic_q1_expression)).

Definition encoded_monic_cubic_remainder0_expression : signed_expression 9 :=
  signed_minus (signed_coefficient pos3)
    (signed_mult encoded_monic_cubic_d_expression
      encoded_monic_cubic_q0_expression).

Definition encoded_monic_cubic_remainders_zero_expression : nat_expression 9 :=
  NatMult
    (NatMult
      (signed_zero_indicator_expression encoded_monic_cubic_remainder2_expression)
      (signed_zero_indicator_expression encoded_monic_cubic_remainder1_expression))
    (signed_zero_indicator_expression encoded_monic_cubic_remainder0_expression).

Definition encoded_monic_cubic_middle_predicate : nat_expression 8 :=
  NatBoundedExists encoded_monic_cubic_d_count_expression
    encoded_monic_cubic_remainders_zero_expression.

Definition encoded_monic_cubic_outer_predicate : nat_expression 7 :=
  NatBoundedExists encoded_monic_cubic_c_count_expression
    encoded_monic_cubic_middle_predicate.

Definition encoded_monic_has_cubic_factor_expression : nat_expression 6 :=
  NatBoundedExists encoded_monic_cubic_b_count_expression
    encoded_monic_cubic_outer_predicate.

Lemma eval_encoded_monic_cubic_b_count_expression coefficients :
  eval_nat_expression encoded_monic_cubic_b_count_expression coefficients =
  2 * (3 * encoded_monic_sextic_root_bound coefficients) + 1.
Proof.
  unfold encoded_monic_cubic_b_count_expression, NatSymmetricCount.
  cbn [eval_nat_expression].
  rewrite eval_encoded_monic_root_bound_expression. lia.
Qed.

Lemma eval_encoded_monic_cubic_c_count_expression b_index coefficients :
  eval_nat_expression encoded_monic_cubic_c_count_expression
    (b_index ## coefficients) =
  2 * (3 * encoded_monic_sextic_root_bound coefficients *
       encoded_monic_sextic_root_bound coefficients) + 1.
Proof.
  unfold encoded_monic_cubic_c_count_expression,
    encoded_monic_cubic_c_radius_outer_expression, NatSymmetricCount.
  cbn [eval_nat_expression].
  rewrite !eval_encoded_monic_quadratic_outer_root_bound_expression. lia.
Qed.

Lemma eval_encoded_monic_quadratic_body_root_bound_expression c_index b_index
    coefficients :
  eval_nat_expression encoded_monic_quadratic_body_root_bound_expression
    (c_index ## b_index ## coefficients) =
  encoded_monic_sextic_root_bound coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_monic_cubic_d_count_expression c_index b_index
    coefficients :
  eval_nat_expression encoded_monic_cubic_d_count_expression
    (c_index ## b_index ## coefficients) =
  2 * (encoded_monic_sextic_root_bound coefficients *
       encoded_monic_sextic_root_bound coefficients *
       encoded_monic_sextic_root_bound coefficients) + 1.
Proof.
  unfold encoded_monic_cubic_d_count_expression,
    encoded_monic_cubic_d_radius_middle_expression, NatSymmetricCount.
  cbn [eval_nat_expression].
  rewrite !eval_encoded_monic_quadratic_body_root_bound_expression. lia.
Qed.

Lemma eval_encoded_monic_cubic_body_root_bound_expression d_index c_index
    b_index coefficients :
  eval_nat_expression encoded_monic_cubic_body_root_bound_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_sextic_root_bound coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_monic_cubic_b_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_b_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_b_value coefficients b_index.
Proof.
  unfold encoded_monic_cubic_b_expression, signed_symmetric_candidate,
    encoded_monic_cubic_b_value,
    encoded_monic_cubic_b_radius_body_expression.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression.
  cbn [eval_nat_expression].
  rewrite eval_encoded_monic_cubic_body_root_bound_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_c_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_c_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_c_value coefficients c_index.
Proof.
  unfold encoded_monic_cubic_c_expression, signed_symmetric_candidate,
    encoded_monic_cubic_c_value,
    encoded_monic_cubic_c_radius_body_expression.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression.
  cbn [eval_nat_expression].
  rewrite !eval_encoded_monic_cubic_body_root_bound_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_d_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_d_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_d_value coefficients d_index.
Proof.
  unfold encoded_monic_cubic_d_expression, signed_symmetric_candidate,
    encoded_monic_cubic_d_value,
    encoded_monic_cubic_d_radius_body_expression.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression.
  cbn [eval_nat_expression].
  rewrite !eval_encoded_monic_cubic_body_root_bound_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_q2_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_q2_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_q2 coefficients b_index.
Proof.
  unfold encoded_monic_cubic_q2_expression, encoded_monic_cubic_q2.
  rewrite eval_signed_minus, eval_signed_coefficient,
    eval_encoded_monic_cubic_b_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_q1_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_q1_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_q1 coefficients b_index c_index.
Proof.
  unfold encoded_monic_cubic_q1_expression, encoded_monic_cubic_q1.
  rewrite !eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_cubic_b_expression,
    eval_encoded_monic_cubic_c_expression,
    eval_encoded_monic_cubic_q2_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_q0_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_q0_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_q0 coefficients b_index c_index d_index.
Proof.
  unfold encoded_monic_cubic_q0_expression, encoded_monic_cubic_q0.
  rewrite !eval_signed_minus, eval_signed_coefficient, !eval_signed_mult,
    eval_encoded_monic_cubic_b_expression,
    eval_encoded_monic_cubic_c_expression,
    eval_encoded_monic_cubic_d_expression,
    eval_encoded_monic_cubic_q1_expression,
    eval_encoded_monic_cubic_q2_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_remainder2_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_remainder2_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_remainder2 coefficients b_index c_index d_index.
Proof.
  unfold encoded_monic_cubic_remainder2_expression,
    encoded_monic_cubic_remainder2.
  rewrite eval_signed_minus, eval_signed_coefficient, !eval_signed_plus,
    !eval_signed_mult, eval_encoded_monic_cubic_b_expression,
    eval_encoded_monic_cubic_c_expression,
    eval_encoded_monic_cubic_d_expression,
    eval_encoded_monic_cubic_q0_expression,
    eval_encoded_monic_cubic_q1_expression,
    eval_encoded_monic_cubic_q2_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_remainder1_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_remainder1_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_remainder1 coefficients b_index c_index d_index.
Proof.
  unfold encoded_monic_cubic_remainder1_expression,
    encoded_monic_cubic_remainder1.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_plus,
    !eval_signed_mult, eval_encoded_monic_cubic_c_expression,
    eval_encoded_monic_cubic_d_expression,
    eval_encoded_monic_cubic_q0_expression,
    eval_encoded_monic_cubic_q1_expression.
  reflexivity.
Qed.

Lemma eval_encoded_monic_cubic_remainder0_expression d_index c_index b_index
    coefficients :
  eval_signed_expression encoded_monic_cubic_remainder0_expression
    (d_index ## c_index ## b_index ## coefficients) =
  encoded_monic_cubic_remainder0 coefficients b_index c_index d_index.
Proof.
  unfold encoded_monic_cubic_remainder0_expression,
    encoded_monic_cubic_remainder0.
  rewrite eval_signed_minus, eval_signed_coefficient, eval_signed_mult,
    eval_encoded_monic_cubic_d_expression,
    eval_encoded_monic_cubic_q0_expression.
  reflexivity.
Qed.

Lemma nat_product3_nonzero_iff first second third :
  (first * second) * third <> 0 <->
  first <> 0 /\ second <> 0 /\ third <> 0.
Proof. repeat rewrite nat_product_nonzero_iff. tauto. Qed.

Lemma eval_encoded_monic_cubic_remainders_zero_nonzero_iff
    d_index c_index b_index coefficients :
  eval_nat_expression encoded_monic_cubic_remainders_zero_expression
    (d_index ## c_index ## b_index ## coefficients) <> 0 <->
  encoded_monic_cubic_remainder2 coefficients b_index c_index d_index = 0%Z
  /\ encoded_monic_cubic_remainder1 coefficients b_index c_index d_index = 0%Z
  /\ encoded_monic_cubic_remainder0 coefficients b_index c_index d_index = 0%Z.
Proof.
  unfold encoded_monic_cubic_remainders_zero_expression.
  cbn [eval_nat_expression]. rewrite nat_product3_nonzero_iff.
  rewrite !eval_signed_zero_indicator_nonzero_iff,
    eval_encoded_monic_cubic_remainder2_expression,
    eval_encoded_monic_cubic_remainder1_expression,
    eval_encoded_monic_cubic_remainder0_expression.
  reflexivity.
Qed.

Definition encoded_monic_has_bounded_cubic_factor
    (coefficients : Vector.t nat 6) : Prop :=
  exists b_index,
    b_index < 2 * (3 * encoded_monic_sextic_root_bound coefficients) + 1 /\
  exists c_index,
    c_index <
      2 * (3 * encoded_monic_sextic_root_bound coefficients *
           encoded_monic_sextic_root_bound coefficients) + 1 /\
  exists d_index,
    d_index <
      2 * (encoded_monic_sextic_root_bound coefficients *
           encoded_monic_sextic_root_bound coefficients *
           encoded_monic_sextic_root_bound coefficients) + 1 /\
    encoded_monic_cubic_remainder2
      coefficients b_index c_index d_index = 0%Z /\
    encoded_monic_cubic_remainder1
      coefficients b_index c_index d_index = 0%Z /\
    encoded_monic_cubic_remainder0
      coefficients b_index c_index d_index = 0%Z.

Theorem eval_encoded_monic_has_cubic_factor_true_iff coefficients :
  eval_nat_expression encoded_monic_has_cubic_factor_expression
    coefficients = 1 <->
  encoded_monic_has_bounded_cubic_factor coefficients.
Proof.
  unfold encoded_monic_has_cubic_factor_expression.
  rewrite eval_nat_bounded_exists_true_iff.
  split.
  - intros (b_index & Hb & Houter).
    unfold encoded_monic_cubic_outer_predicate in Houter.
    rewrite eval_nat_bounded_exists_nonzero_iff in Houter.
    destruct Houter as (c_index & Hc & Hmiddle).
    unfold encoded_monic_cubic_middle_predicate in Hmiddle.
    rewrite eval_nat_bounded_exists_nonzero_iff in Hmiddle.
    destruct Hmiddle as (d_index & Hd & Hremainders).
    exists b_index; split.
    + rewrite eval_encoded_monic_cubic_b_count_expression in Hb. exact Hb.
    + exists c_index; split.
      * rewrite eval_encoded_monic_cubic_c_count_expression in Hc. exact Hc.
      * exists d_index; split.
        -- rewrite eval_encoded_monic_cubic_d_count_expression in Hd. exact Hd.
        -- apply (proj1
            (eval_encoded_monic_cubic_remainders_zero_nonzero_iff
              d_index c_index b_index coefficients)). exact Hremainders.
  - intros (b_index & Hb & c_index & Hc & d_index & Hd &
      Hremainder2 & Hremainder1 & Hremainder0).
    exists b_index; split.
    + rewrite eval_encoded_monic_cubic_b_count_expression. exact Hb.
    + unfold encoded_monic_cubic_outer_predicate.
      rewrite eval_nat_bounded_exists_nonzero_iff.
      exists c_index; split.
      * rewrite eval_encoded_monic_cubic_c_count_expression. exact Hc.
      * unfold encoded_monic_cubic_middle_predicate.
        rewrite eval_nat_bounded_exists_nonzero_iff.
        exists d_index; split.
        -- rewrite eval_encoded_monic_cubic_d_count_expression. exact Hd.
        -- apply (proj2
            (eval_encoded_monic_cubic_remainders_zero_nonzero_iff
              d_index c_index b_index coefficients)). auto.
Qed.

Definition ra_encoded_monic_has_cubic_factor : recalg 6 :=
  compile_nat_expression encoded_monic_has_cubic_factor_expression.

Theorem ra_encoded_monic_has_cubic_factor_primitive_recursive :
  prim_rec ra_encoded_monic_has_cubic_factor.
Proof. apply compile_nat_expression_primitive_recursive. Qed.

Lemma eval_nat_bounded_exists_nonzero_iff_one {arity}
    (upper : nat_expression arity)
    (predicate : nat_expression (S arity)) values :
  eval_nat_expression (NatBoundedExists upper predicate) values <> 0 <->
  eval_nat_expression (NatBoundedExists upper predicate) values = 1.
Proof.
  destruct (eval_nat_bounded_exists_zero_or_one upper predicate values)
    as [Hzero|Hone]; rewrite Hzero || rewrite Hone; lia.
Qed.

Lemma eval_encoded_monic_has_linear_factor_nonzero_iff coefficients :
  eval_nat_expression encoded_monic_has_linear_factor_expression
    coefficients <> 0 <->
  encoded_monic_has_bounded_linear_factor coefficients.
Proof.
  unfold encoded_monic_has_linear_factor_expression.
  rewrite eval_nat_bounded_exists_nonzero_iff_one.
  apply eval_encoded_monic_has_linear_factor_true_iff.
Qed.

Lemma eval_encoded_monic_has_quadratic_factor_nonzero_iff coefficients :
  eval_nat_expression encoded_monic_has_quadratic_factor_expression
    coefficients <> 0 <->
  encoded_monic_has_bounded_quadratic_factor coefficients.
Proof.
  unfold encoded_monic_has_quadratic_factor_expression.
  rewrite eval_nat_bounded_exists_nonzero_iff_one.
  apply eval_encoded_monic_has_quadratic_factor_true_iff.
Qed.

Lemma eval_encoded_monic_has_cubic_factor_nonzero_iff coefficients :
  eval_nat_expression encoded_monic_has_cubic_factor_expression
    coefficients <> 0 <->
  encoded_monic_has_bounded_cubic_factor coefficients.
Proof.
  unfold encoded_monic_has_cubic_factor_expression.
  rewrite eval_nat_bounded_exists_nonzero_iff_one.
  apply eval_encoded_monic_has_cubic_factor_true_iff.
Qed.

Lemma nat_sum3_nonzero_iff first second third :
  first + (second + third) <> 0 <->
  first <> 0 \/ second <> 0 \/ third <> 0.
Proof. lia. Qed.

Definition encoded_monic_has_proper_factor_expression : nat_expression 6 :=
  NatNonzeroIndicator
    (NatPlus encoded_monic_has_linear_factor_expression
      (NatPlus encoded_monic_has_quadratic_factor_expression
        encoded_monic_has_cubic_factor_expression)).

Definition encoded_monic_has_bounded_proper_factor
    (coefficients : Vector.t nat 6) : Prop :=
  encoded_monic_has_bounded_linear_factor coefficients \/
  encoded_monic_has_bounded_quadratic_factor coefficients \/
  encoded_monic_has_bounded_cubic_factor coefficients.

Theorem eval_encoded_monic_has_proper_factor_true_iff coefficients :
  eval_nat_expression encoded_monic_has_proper_factor_expression
    coefficients = 1 <->
  encoded_monic_has_bounded_proper_factor coefficients.
Proof.
  unfold encoded_monic_has_proper_factor_expression,
    encoded_monic_has_bounded_proper_factor.
  rewrite eval_nat_nonzero_indicator.
  cbn [eval_nat_expression]. rewrite nat_sum3_nonzero_iff.
  rewrite eval_encoded_monic_has_linear_factor_nonzero_iff,
    eval_encoded_monic_has_quadratic_factor_nonzero_iff,
    eval_encoded_monic_has_cubic_factor_nonzero_iff.
  reflexivity.
Qed.

Definition encoded_monic_has_proper_factorb
    (coefficients : Vector.t nat 6) : bool :=
  Nat.eqb
    (eval_nat_expression encoded_monic_has_proper_factor_expression
      coefficients) 1.

Lemma encoded_monic_has_proper_factor_indicator coefficients :
  eval_nat_expression encoded_monic_has_proper_factor_expression
    coefficients =
  bool_to_nat (encoded_monic_has_proper_factorb coefficients).
Proof.
  unfold encoded_monic_has_proper_factor_expression.
  destruct
    (eval_nat_nonzero_indicator_zero_or_one
      (NatPlus encoded_monic_has_linear_factor_expression
        (NatPlus encoded_monic_has_quadratic_factor_expression
          encoded_monic_has_cubic_factor_expression)) coefficients)
    as [Hzero|Hone].
  - unfold encoded_monic_has_proper_factorb,
      encoded_monic_has_proper_factor_expression, bool_to_nat.
    rewrite Hzero. reflexivity.
  - unfold encoded_monic_has_proper_factorb,
      encoded_monic_has_proper_factor_expression, bool_to_nat.
    rewrite Hone. reflexivity.
Qed.

Theorem encoded_monic_has_proper_factorb_true_iff coefficients :
  encoded_monic_has_proper_factorb coefficients = true <->
  encoded_monic_has_bounded_proper_factor coefficients.
Proof.
  unfold encoded_monic_has_proper_factorb.
  rewrite Nat.eqb_eq.
  apply eval_encoded_monic_has_proper_factor_true_iff.
Qed.

Definition ra_encoded_monic_has_proper_factor : recalg 6 :=
  compile_nat_expression encoded_monic_has_proper_factor_expression.

Theorem ra_encoded_monic_has_proper_factor_primitive_recursive :
  prim_rec ra_encoded_monic_has_proper_factor.
Proof. apply compile_nat_expression_primitive_recursive. Qed.

Definition encoded_monic_proper_factor_relation
    (coefficients : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat (encoded_monic_has_proper_factorb coefficients).

Theorem encoded_monic_proper_factor_relation_murec :
  MuRec_computable encoded_monic_proper_factor_relation.
Proof.
  unfold encoded_monic_proper_factor_relation.
  refine (@recalg_graph_murec 6
    (fun coefficients =>
      bool_to_nat (encoded_monic_has_proper_factorb coefficients))
    ra_encoded_monic_has_proper_factor _).
  intro coefficients.
  unfold ra_encoded_monic_has_proper_factor.
  rewrite <- encoded_monic_has_proper_factor_indicator.
  apply compile_nat_expression_correct.
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

Definition integer_magnitude (value : Z) : nat :=
  Z.to_nat (Z.abs value).

Lemma zigzag_magnitude_encode value :
  zigzag_magnitude (zigzag_encode value) = integer_magnitude value.
Proof.
  apply Nat2Z.inj.
  rewrite zigzag_magnitude_spec, zigzag_decode_encode.
  unfold integer_magnitude.
  rewrite Z2Nat.id.
  - reflexivity.
  - apply Z.abs_nonneg.
Qed.

Lemma encoded_sextic_constant_magnitude_encode coefficients :
  encoded_sextic_constant_magnitude (encode_seven_coefficients coefficients) =
  integer_magnitude (vec_pos coefficients pos0).
Proof.
  unfold encoded_sextic_constant_magnitude,
    encode_seven_coefficients.
  rewrite vec_pos_map, zigzag_magnitude_encode. reflexivity.
Qed.

Lemma encoded_sextic_leading_magnitude_encode coefficients :
  encoded_sextic_leading_magnitude (encode_seven_coefficients coefficients) =
  integer_magnitude (vec_pos coefficients pos6).
Proof.
  unfold encoded_sextic_leading_magnitude,
    encode_seven_coefficients.
  rewrite vec_pos_map, zigzag_magnitude_encode. reflexivity.
Qed.

Definition integer_sextic_homogeneous_value
    (coefficients : Vector.t Z 7)
    (numerator_index denominator_index : nat) : Z :=
  homogeneous_sextic_value
    (vec_pos coefficients pos0)
    (vec_pos coefficients pos1)
    (vec_pos coefficients pos2)
    (vec_pos coefficients pos3)
    (vec_pos coefficients pos4)
    (vec_pos coefficients pos5)
    (vec_pos coefficients pos6)
    (Z.of_nat numerator_index -
      Z.abs (vec_pos coefficients pos0))%Z
    (Z.of_nat (S denominator_index)).

Lemma encoded_sextic_homogeneous_value_encode coefficients numerator_index
    denominator_index :
  encoded_sextic_homogeneous_value
    (encode_seven_coefficients coefficients)
    numerator_index denominator_index =
  integer_sextic_homogeneous_value
    coefficients numerator_index denominator_index.
Proof.
  unfold encoded_sextic_homogeneous_value,
    integer_sextic_homogeneous_value.
  repeat rewrite encode_seven_coefficients_correct.
  rewrite encoded_sextic_numerator_value_spec,
    encode_seven_coefficients_correct.
  reflexivity.
Qed.

Definition integer_sextic_has_bounded_homogeneous_root
    (coefficients : Vector.t Z 7) : Prop :=
  vec_pos coefficients pos0 = 0%Z \/
  exists numerator_index,
    numerator_index <
      2 * integer_magnitude (vec_pos coefficients pos0) + 1 /\
    exists denominator_index,
      denominator_index < integer_magnitude (vec_pos coefficients pos6) /\
      integer_sextic_homogeneous_value
        coefficients numerator_index denominator_index = 0%Z.

Theorem encoded_sextic_bounded_rootb_encoded_true_iff coefficients :
  encoded_sextic_bounded_rootb (encode_seven_coefficients coefficients) = true
  <-> integer_sextic_has_bounded_homogeneous_root coefficients.
Proof.
  rewrite encoded_sextic_bounded_rootb_true_iff.
  unfold encoded_sextic_has_bounded_homogeneous_root,
    integer_sextic_has_bounded_homogeneous_root.
  rewrite encode_seven_coefficients_correct,
    encoded_sextic_constant_magnitude_encode,
    encoded_sextic_leading_magnitude_encode.
  setoid_rewrite encoded_sextic_homogeneous_value_encode.
  reflexivity.
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

Definition ra_encoded_sextic_bounded_root_code : recalg 1 :=
  ra_comp ra_encoded_sextic_bounded_root (ra_vec_project 7).

Lemma ra_encoded_sextic_bounded_root_code_correct code :
  ⟦ra_encoded_sextic_bounded_root_code⟧ (code ## vec_nil)
    (bool_to_nat
      (encoded_sextic_bounded_rootb (project 7 code))).
Proof.
  unfold ra_encoded_sextic_bounded_root_code.
  exists (project 7 code); split.
  - apply ra_encoded_sextic_bounded_root_correct.
  - intro variable. rewrite vec_pos_set.
    apply ra_vec_project_val_at.
Qed.

Definition encoded_sextic_bounded_root_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_sextic_bounded_rootb (project 7 (vec_head code))).

Theorem encoded_sextic_bounded_root_code_relation_murec :
  MuRec_computable encoded_sextic_bounded_root_code_relation.
Proof.
  unfold encoded_sextic_bounded_root_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => bool_to_nat
      (encoded_sextic_bounded_rootb (project 7 (vec_head code))))
    ra_encoded_sextic_bounded_root_code _).
  intro v. vec split v with code. vec nil v.
  apply ra_encoded_sextic_bounded_root_code_correct.
Qed.

Lemma encoded_sextic_bounded_root_code_roundtrip coefficients out :
  encoded_sextic_bounded_root_code_relation
    (inject coefficients ## vec_nil) out <->
  encoded_sextic_bounded_root_relation coefficients out.
Proof.
  unfold encoded_sextic_bounded_root_code_relation,
    encoded_sextic_bounded_root_relation.
  cbn [vec_head]. now rewrite project_inject.
Qed.

Definition ra_encoded_monic_proper_factor_code : recalg 1 :=
  ra_comp ra_encoded_monic_has_proper_factor (ra_vec_project 6).

Lemma ra_encoded_monic_proper_factor_code_correct code :
  ⟦ra_encoded_monic_proper_factor_code⟧ (code ## vec_nil)
    (bool_to_nat
      (encoded_monic_has_proper_factorb (project 6 code))).
Proof.
  unfold ra_encoded_monic_proper_factor_code,
    ra_encoded_monic_has_proper_factor.
  exists (project 6 code); split.
  - rewrite <- encoded_monic_has_proper_factor_indicator.
    apply compile_nat_expression_correct.
  - intro variable. rewrite vec_pos_set.
    apply ra_vec_project_val_at.
Qed.

Definition encoded_monic_proper_factor_code_relation
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_monic_has_proper_factorb (project 6 (vec_head code))).

Theorem encoded_monic_proper_factor_code_relation_murec :
  MuRec_computable encoded_monic_proper_factor_code_relation.
Proof.
  unfold encoded_monic_proper_factor_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => bool_to_nat
      (encoded_monic_has_proper_factorb (project 6 (vec_head code))))
    ra_encoded_monic_proper_factor_code _).
  intro v. vec split v with code. vec nil v.
  apply ra_encoded_monic_proper_factor_code_correct.
Qed.

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

(* --------------------------------------------------------------------- *)
(* One bounded rational-root compiler for every fixed coefficient count. *)

(* The pair and triple resolvents have sixteen and eleven coefficients,
   respectively.  Their finite root searches differ from the seven-entry
   search above only in the length of the ascending coefficient vector.
   Keeping the length abstract avoids two copies of the search proof and,
   more importantly, makes the later sparse-resolvent compiler responsible
   only for producing a vector of signed coefficient codes. *)

Definition encoded_fixed_coefficient_list {count}
    (coefficients : Vector.t nat count) : list Z :=
  List.map zigzag_decode (vec_list coefficients).

Definition encoded_fixed_constant_magnitude {degree}
    (coefficients : Vector.t nat (S degree)) : nat :=
  zigzag_magnitude (vec_pos coefficients pos0).

Fixpoint final_position (degree : nat) : pos (S degree) :=
  match degree with
  | 0 => pos0
  | S degree' => pos_nxt (final_position degree')
  end.

Definition encoded_fixed_leading_magnitude {degree}
    (coefficients : Vector.t nat (S degree)) : nat :=
  zigzag_magnitude (vec_pos coefficients (final_position degree)).

Definition encoded_fixed_numerator_value {degree}
    (coefficients : Vector.t nat (S degree)) (index : nat) : Z :=
  (Z.of_nat index -
   Z.of_nat (encoded_fixed_constant_magnitude coefficients))%Z.

Definition encoded_fixed_denominator_value (index : nat) : Z :=
  Z.of_nat (S index).

Definition encoded_fixed_homogeneous_value {degree}
    (coefficients : Vector.t nat (S degree))
    (numerator_index denominator_index : nat) : Z :=
  z_homogeneous_list_value
    (encoded_fixed_coefficient_list coefficients)
    (encoded_fixed_numerator_value coefficients numerator_index)
    (encoded_fixed_denominator_value denominator_index).

Definition shifted_fixed_coefficient_expressions (degree : nat) :
    list (signed_expression (S (S (S degree)))) :=
  List.map
    (fun variable : pos (S degree) =>
      signed_coefficient (pos_nxt (pos_nxt variable)))
    (pos_list (S degree)).

Definition encoded_fixed_numerator_expression (degree : nat) :
    signed_expression (S (S (S degree))) :=
  signed_minus
    (signed_of_nat_expression (NatVar pos1))
    (signed_of_nat_expression
      (signed_coefficient_magnitude_expression
        (pos_nxt (pos_nxt pos0)))).

Definition encoded_fixed_denominator_expression (degree : nat) :
    signed_expression (S (S (S degree))) :=
  signed_of_nat_expression (NatSucc (NatVar pos0)).

Definition encoded_fixed_homogeneous_expression (degree : nat) :
    signed_expression (S (S (S degree))) :=
  signed_homogeneous_list_expression
    (shifted_fixed_coefficient_expressions degree)
    (encoded_fixed_numerator_expression degree)
    (encoded_fixed_denominator_expression degree).

Lemma eval_shifted_fixed_coefficient_expressions degree denominator_index
    numerator_index (coefficients : Vector.t nat (S degree)) :
  List.map
    (fun expression => eval_signed_expression expression
      (denominator_index ## numerator_index ## coefficients))
    (shifted_fixed_coefficient_expressions degree) =
  encoded_fixed_coefficient_list coefficients.
Proof.
  unfold shifted_fixed_coefficient_expressions,
    encoded_fixed_coefficient_list.
  assert (Hcoefficients :
      vec_set_pos (fun variable => vec_pos coefficients variable) =
      coefficients).
  { apply vec_pos_ext. intro variable. rewrite vec_pos_set. reflexivity. }
  rewrite <- Hcoefficients.
  rewrite vec_list_vec_set_pos, !List.map_map.
  apply List.map_ext.
  intro variable.
  rewrite eval_signed_coefficient.
  change
    (zigzag_decode
      (vec_pos
        (vec_set_pos
          (fun variable => vec_pos coefficients variable)) variable) =
     zigzag_decode (vec_pos coefficients variable)).
  rewrite vec_pos_set.
  reflexivity.
Qed.

Lemma eval_encoded_fixed_numerator_expression degree denominator_index
    numerator_index (coefficients : Vector.t nat (S degree)) :
  eval_signed_expression (encoded_fixed_numerator_expression degree)
    (denominator_index ## numerator_index ## coefficients) =
  encoded_fixed_numerator_value coefficients numerator_index.
Proof.
  unfold encoded_fixed_numerator_expression,
    encoded_fixed_numerator_value, encoded_fixed_constant_magnitude.
  rewrite eval_signed_minus, !eval_signed_of_nat_expression,
    eval_signed_coefficient_magnitude_expression.
  reflexivity.
Qed.

Lemma eval_encoded_fixed_denominator_expression degree denominator_index
    numerator_index (coefficients : Vector.t nat (S degree)) :
  eval_signed_expression (encoded_fixed_denominator_expression degree)
    (denominator_index ## numerator_index ## coefficients) =
  encoded_fixed_denominator_value denominator_index.
Proof.
  unfold encoded_fixed_denominator_expression,
    encoded_fixed_denominator_value.
  rewrite eval_signed_of_nat_expression. reflexivity.
Qed.

Theorem eval_encoded_fixed_homogeneous_expression degree denominator_index
    numerator_index (coefficients : Vector.t nat (S degree)) :
  eval_signed_expression (encoded_fixed_homogeneous_expression degree)
    (denominator_index ## numerator_index ## coefficients) =
  encoded_fixed_homogeneous_value
    coefficients numerator_index denominator_index.
Proof.
  unfold encoded_fixed_homogeneous_expression,
    encoded_fixed_homogeneous_value.
  rewrite eval_signed_homogeneous_list_expression,
    eval_shifted_fixed_coefficient_expressions,
    eval_encoded_fixed_numerator_expression,
    eval_encoded_fixed_denominator_expression.
  reflexivity.
Qed.

Definition encoded_fixed_homogeneous_zero_expression (degree : nat) :
    nat_expression (S (S (S degree))) :=
  signed_zero_indicator_expression
    (encoded_fixed_homogeneous_expression degree).

Lemma eval_encoded_fixed_homogeneous_zero_nonzero_iff degree
    denominator_index numerator_index
    (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_homogeneous_zero_expression degree)
    (denominator_index ## numerator_index ## coefficients) <> 0 <->
  encoded_fixed_homogeneous_value
    coefficients numerator_index denominator_index = 0%Z.
Proof.
  unfold encoded_fixed_homogeneous_zero_expression.
  rewrite eval_signed_zero_indicator_nonzero_iff,
    eval_encoded_fixed_homogeneous_expression.
  reflexivity.
Qed.

Definition encoded_fixed_denominator_count_expression (degree : nat) :
    nat_expression (S (S degree)) :=
  signed_coefficient_magnitude_expression
    (pos_nxt (final_position degree)).

Definition encoded_fixed_numerator_predicate (degree : nat) :
    nat_expression (S (S degree)) :=
  NatBoundedExists (encoded_fixed_denominator_count_expression degree)
    (encoded_fixed_homogeneous_zero_expression degree).

Definition encoded_fixed_constant_magnitude_expression (degree : nat) :
    nat_expression (S degree) :=
  signed_coefficient_magnitude_expression pos0.

Definition encoded_fixed_numerator_count_expression (degree : nat) :
    nat_expression (S degree) :=
  NatSucc
    (NatMult (NatConst 2)
      (encoded_fixed_constant_magnitude_expression degree)).

Definition encoded_fixed_bounded_root_expression (degree : nat) :
    nat_expression (S degree) :=
  NatIfZero (encoded_fixed_constant_magnitude_expression degree)
    (NatConst 1)
    (NatBoundedExists (encoded_fixed_numerator_count_expression degree)
      (encoded_fixed_numerator_predicate degree)).

Lemma eval_encoded_fixed_denominator_count_expression degree numerator_index
    (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_denominator_count_expression degree)
    (numerator_index ## coefficients) =
  encoded_fixed_leading_magnitude coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_fixed_constant_magnitude_expression degree
    (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_constant_magnitude_expression degree)
    coefficients = encoded_fixed_constant_magnitude coefficients.
Proof. reflexivity. Qed.

Lemma eval_encoded_fixed_numerator_count_expression degree
    (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_numerator_count_expression degree)
    coefficients =
  2 * encoded_fixed_constant_magnitude coefficients + 1.
Proof.
  unfold encoded_fixed_numerator_count_expression.
  cbn [eval_nat_expression].
  rewrite eval_encoded_fixed_constant_magnitude_expression. lia.
Qed.

Lemma eval_encoded_fixed_numerator_predicate_nonzero_iff degree
    numerator_index (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_numerator_predicate degree)
    (numerator_index ## coefficients) <> 0 <->
  exists denominator_index,
    denominator_index < encoded_fixed_leading_magnitude coefficients /\
    encoded_fixed_homogeneous_value
      coefficients numerator_index denominator_index = 0%Z.
Proof.
  unfold encoded_fixed_numerator_predicate.
  rewrite eval_nat_bounded_exists_nonzero_iff.
  split.
  - intros (denominator_index & Hbound & Hzero).
    exists denominator_index; split.
    + rewrite eval_encoded_fixed_denominator_count_expression in Hbound.
      exact Hbound.
    + apply (proj1
        (@eval_encoded_fixed_homogeneous_zero_nonzero_iff degree
          denominator_index numerator_index coefficients)).
      exact Hzero.
  - intros (denominator_index & Hbound & Hzero).
    exists denominator_index; split.
    + rewrite eval_encoded_fixed_denominator_count_expression.
      exact Hbound.
    + apply (proj2
        (@eval_encoded_fixed_homogeneous_zero_nonzero_iff degree
          denominator_index numerator_index coefficients)).
      exact Hzero.
Qed.

Definition encoded_fixed_has_bounded_homogeneous_root {degree}
    (coefficients : Vector.t nat (S degree)) : Prop :=
  zigzag_decode (vec_pos coefficients pos0) = 0%Z \/
  exists numerator_index,
    numerator_index <
      2 * encoded_fixed_constant_magnitude coefficients + 1 /\
    exists denominator_index,
      denominator_index < encoded_fixed_leading_magnitude coefficients /\
      encoded_fixed_homogeneous_value
        coefficients numerator_index denominator_index = 0%Z.

Theorem eval_encoded_fixed_bounded_root_true_iff degree
    (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_bounded_root_expression degree)
    coefficients = 1 <->
  encoded_fixed_has_bounded_homogeneous_root coefficients.
Proof.
  unfold encoded_fixed_bounded_root_expression.
  change
    (ite_rel (encoded_fixed_constant_magnitude coefficients) 1
      (eval_nat_expression
        (NatBoundedExists
          (encoded_fixed_numerator_count_expression degree)
          (encoded_fixed_numerator_predicate degree)) coefficients) = 1 <->
      encoded_fixed_has_bounded_homogeneous_root coefficients).
  unfold ite_rel.
  destruct (encoded_fixed_constant_magnitude coefficients)
    as [|constant_magnitude] eqn:Hconstant.
  - split; intro.
    + left. apply zigzag_magnitude_zero_iff. exact Hconstant.
    + reflexivity.
  - rewrite eval_nat_bounded_exists_true_iff.
    split.
    + intros (numerator_index & Hbound & Hroot).
      right; exists numerator_index; split.
      * rewrite eval_encoded_fixed_numerator_count_expression in Hbound.
        exact Hbound.
      * apply (proj1
          (@eval_encoded_fixed_numerator_predicate_nonzero_iff degree
            numerator_index coefficients)).
        exact Hroot.
    + intros [Hconstant_zero|
        (numerator_index & Hbound & denominator_index &
          Hdenominator & Hzero)].
      * exfalso.
        assert (Hmagnitude_zero :
            encoded_fixed_constant_magnitude coefficients = 0).
        { unfold encoded_fixed_constant_magnitude.
          apply (proj2 (zigzag_magnitude_zero_iff
            (vec_pos coefficients pos0))).
          exact Hconstant_zero. }
        rewrite Hmagnitude_zero in Hconstant. discriminate.
      * exists numerator_index; split.
        -- rewrite eval_encoded_fixed_numerator_count_expression.
           exact Hbound.
        -- apply (proj2
            (@eval_encoded_fixed_numerator_predicate_nonzero_iff degree
              numerator_index coefficients)).
           exists denominator_index; auto.
Qed.

Lemma eval_encoded_fixed_bounded_root_zero_or_one degree
    (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_bounded_root_expression degree)
    coefficients = 0 \/
  eval_nat_expression (encoded_fixed_bounded_root_expression degree)
    coefficients = 1.
Proof.
  unfold encoded_fixed_bounded_root_expression.
  change
    (ite_rel
      (eval_nat_expression
        (encoded_fixed_constant_magnitude_expression degree) coefficients)
      1
      (eval_nat_expression
        (NatBoundedExists
          (encoded_fixed_numerator_count_expression degree)
          (encoded_fixed_numerator_predicate degree)) coefficients) = 0 \/
     ite_rel
      (eval_nat_expression
        (encoded_fixed_constant_magnitude_expression degree) coefficients)
      1
      (eval_nat_expression
        (NatBoundedExists
          (encoded_fixed_numerator_count_expression degree)
          (encoded_fixed_numerator_predicate degree)) coefficients) = 1).
  unfold ite_rel.
  destruct (eval_nat_expression
    (encoded_fixed_constant_magnitude_expression degree) coefficients).
  - right; reflexivity.
  - apply eval_nat_bounded_exists_zero_or_one.
Qed.

Definition encoded_fixed_bounded_rootb degree
    (coefficients : Vector.t nat (S degree)) : bool :=
  Nat.eqb
    (eval_nat_expression (encoded_fixed_bounded_root_expression degree)
      coefficients) 1.

Arguments encoded_fixed_bounded_rootb degree coefficients : clear implicits.

Lemma encoded_fixed_bounded_root_indicator degree
    (coefficients : Vector.t nat (S degree)) :
  eval_nat_expression (encoded_fixed_bounded_root_expression degree)
    coefficients =
  bool_to_nat (encoded_fixed_bounded_rootb degree coefficients).
Proof.
  destruct (@eval_encoded_fixed_bounded_root_zero_or_one degree coefficients)
    as [Hzero|Hone].
  - unfold encoded_fixed_bounded_rootb, bool_to_nat.
    rewrite Hzero. reflexivity.
  - unfold encoded_fixed_bounded_rootb, bool_to_nat.
    rewrite Hone. reflexivity.
Qed.

Theorem encoded_fixed_bounded_rootb_true_iff degree
    (coefficients : Vector.t nat (S degree)) :
  encoded_fixed_bounded_rootb degree coefficients = true <->
  encoded_fixed_has_bounded_homogeneous_root coefficients.
Proof.
  unfold encoded_fixed_bounded_rootb.
  rewrite Nat.eqb_eq.
  apply eval_encoded_fixed_bounded_root_true_iff.
Qed.

Definition ra_encoded_fixed_bounded_root degree : recalg (S degree) :=
  compile_nat_expression (encoded_fixed_bounded_root_expression degree).

Theorem ra_encoded_fixed_bounded_root_primitive_recursive degree :
  prim_rec (ra_encoded_fixed_bounded_root degree).
Proof. apply compile_nat_expression_primitive_recursive. Qed.

Lemma ra_encoded_fixed_bounded_root_correct degree
    (coefficients : Vector.t nat (S degree)) :
  ⟦ra_encoded_fixed_bounded_root degree⟧ coefficients
    (bool_to_nat (encoded_fixed_bounded_rootb degree coefficients)).
Proof.
  unfold ra_encoded_fixed_bounded_root.
  rewrite <- encoded_fixed_bounded_root_indicator.
  apply compile_nat_expression_correct.
Qed.

Definition encoded_fixed_bounded_root_relation degree
    (coefficients : Vector.t nat (S degree)) (out : nat) : Prop :=
  out = bool_to_nat (encoded_fixed_bounded_rootb degree coefficients).

Arguments encoded_fixed_bounded_root_relation degree coefficients out
  : clear implicits.

Theorem encoded_fixed_bounded_root_relation_murec degree :
  MuRec_computable (encoded_fixed_bounded_root_relation degree).
Proof.
  unfold encoded_fixed_bounded_root_relation.
  refine (@recalg_graph_murec (S degree)
    (fun coefficients =>
      bool_to_nat (encoded_fixed_bounded_rootb degree coefficients))
    (ra_encoded_fixed_bounded_root degree) _).
  apply ra_encoded_fixed_bounded_root_correct.
Qed.

Definition ra_encoded_fixed_bounded_root_code degree : recalg 1 :=
  ra_comp (ra_encoded_fixed_bounded_root degree)
    (ra_vec_project (S degree)).

Lemma ra_encoded_fixed_bounded_root_code_correct degree code :
  ⟦ra_encoded_fixed_bounded_root_code degree⟧ (code ## vec_nil)
    (bool_to_nat
      (encoded_fixed_bounded_rootb degree (project (S degree) code))).
Proof.
  unfold ra_encoded_fixed_bounded_root_code.
  exists (project (S degree) code); split.
  - apply ra_encoded_fixed_bounded_root_correct.
  - intro variable. rewrite vec_pos_set.
    apply ra_vec_project_val_at.
Qed.

Definition encoded_fixed_bounded_root_code_relation degree
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_fixed_bounded_rootb degree
      (project (S degree) (vec_head code))).

Arguments encoded_fixed_bounded_root_code_relation degree code out
  : clear implicits.

Theorem encoded_fixed_bounded_root_code_relation_murec degree :
  MuRec_computable (encoded_fixed_bounded_root_code_relation degree).
Proof.
  unfold encoded_fixed_bounded_root_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => bool_to_nat
      (encoded_fixed_bounded_rootb degree
        (project (S degree) (vec_head code))))
    (ra_encoded_fixed_bounded_root_code degree) _).
  intro v. vec split v with code. vec nil v.
  apply ra_encoded_fixed_bounded_root_code_correct.
Qed.

Definition encoded_pair_resolvent_bounded_rootb :
    Vector.t nat 16 -> bool :=
  encoded_fixed_bounded_rootb 15.

Definition encoded_triple_resolvent_bounded_rootb :
    Vector.t nat 11 -> bool :=
  encoded_fixed_bounded_rootb 10.

Definition encoded_pair_resolvent_bounded_root_relation :=
  encoded_fixed_bounded_root_relation 15.

Definition encoded_triple_resolvent_bounded_root_relation :=
  encoded_fixed_bounded_root_relation 10.

Corollary encoded_pair_resolvent_bounded_root_relation_murec :
  MuRec_computable encoded_pair_resolvent_bounded_root_relation.
Proof. exact (encoded_fixed_bounded_root_relation_murec 15). Qed.

Corollary encoded_triple_resolvent_bounded_root_relation_murec :
  MuRec_computable encoded_triple_resolvent_bounded_root_relation.
Proof. exact (encoded_fixed_bounded_root_relation_murec 10). Qed.

Definition encoded_pair_resolvent_bounded_root_code_relation :=
  encoded_fixed_bounded_root_code_relation 15.

Definition encoded_triple_resolvent_bounded_root_code_relation :=
  encoded_fixed_bounded_root_code_relation 10.

Corollary encoded_pair_resolvent_bounded_root_code_relation_murec :
  MuRec_computable encoded_pair_resolvent_bounded_root_code_relation.
Proof. exact (encoded_fixed_bounded_root_code_relation_murec 15). Qed.

Corollary encoded_triple_resolvent_bounded_root_code_relation_murec :
  MuRec_computable encoded_triple_resolvent_bounded_root_code_relation.
Proof. exact (encoded_fixed_bounded_root_code_relation_murec 10). Qed.

Definition encode_fixed_coefficients {count}
    (coefficients : Vector.t Z count) : Vector.t nat count :=
  vec_map zigzag_encode coefficients.

Lemma encoded_fixed_coefficient_list_encode count
    (coefficients : Vector.t Z count) :
  encoded_fixed_coefficient_list (encode_fixed_coefficients coefficients) =
  vec_list coefficients.
Proof.
  unfold encoded_fixed_coefficient_list, encode_fixed_coefficients.
  rewrite vec_list_vec_map, List.map_map.
  generalize (vec_list coefficients).
  intro values; induction values as [|value values IHvalues]; cbn.
  - reflexivity.
  - rewrite zigzag_decode_encode, IHvalues. reflexivity.
Qed.

Lemma encoded_fixed_constant_magnitude_encode degree
    (coefficients : Vector.t Z (S degree)) :
  encoded_fixed_constant_magnitude (encode_fixed_coefficients coefficients) =
  integer_magnitude (vec_pos coefficients pos0).
Proof.
  unfold encoded_fixed_constant_magnitude, encode_fixed_coefficients.
  rewrite vec_pos_map, zigzag_magnitude_encode. reflexivity.
Qed.

Lemma encoded_fixed_leading_magnitude_encode degree
    (coefficients : Vector.t Z (S degree)) :
  encoded_fixed_leading_magnitude (encode_fixed_coefficients coefficients) =
  integer_magnitude (vec_pos coefficients (final_position degree)).
Proof.
  unfold encoded_fixed_leading_magnitude, encode_fixed_coefficients.
  rewrite vec_pos_map, zigzag_magnitude_encode. reflexivity.
Qed.

Definition integer_fixed_homogeneous_value {degree}
    (coefficients : Vector.t Z (S degree))
    (numerator_index denominator_index : nat) : Z :=
  z_homogeneous_list_value (vec_list coefficients)
    (Z.of_nat numerator_index -
      Z.abs (vec_pos coefficients pos0))%Z
    (Z.of_nat (S denominator_index)).

Lemma encoded_fixed_homogeneous_value_encode degree
    (coefficients : Vector.t Z (S degree)) numerator_index
    denominator_index :
  encoded_fixed_homogeneous_value (encode_fixed_coefficients coefficients)
    numerator_index denominator_index =
  integer_fixed_homogeneous_value
    coefficients numerator_index denominator_index.
Proof.
  unfold encoded_fixed_homogeneous_value,
    integer_fixed_homogeneous_value,
    encoded_fixed_numerator_value,
    encoded_fixed_denominator_value.
  rewrite encoded_fixed_coefficient_list_encode,
    encoded_fixed_constant_magnitude_encode.
  unfold integer_magnitude.
  rewrite Z2Nat.id by apply Z.abs_nonneg.
  reflexivity.
Qed.

Definition integer_fixed_has_bounded_homogeneous_root {degree}
    (coefficients : Vector.t Z (S degree)) : Prop :=
  vec_pos coefficients pos0 = 0%Z \/
  exists numerator_index,
    numerator_index <
      2 * integer_magnitude (vec_pos coefficients pos0) + 1 /\
    exists denominator_index,
      denominator_index <
        integer_magnitude
          (vec_pos coefficients (final_position degree)) /\
      integer_fixed_homogeneous_value
        coefficients numerator_index denominator_index = 0%Z.

Theorem encoded_fixed_bounded_rootb_encoded_true_iff degree
    (coefficients : Vector.t Z (S degree)) :
  encoded_fixed_bounded_rootb degree
    (encode_fixed_coefficients coefficients) = true <->
  integer_fixed_has_bounded_homogeneous_root coefficients.
Proof.
  rewrite encoded_fixed_bounded_rootb_true_iff.
  unfold encoded_fixed_has_bounded_homogeneous_root,
    integer_fixed_has_bounded_homogeneous_root,
    encode_fixed_coefficients.
  rewrite vec_pos_map, zigzag_decode_encode,
    encoded_fixed_constant_magnitude_encode,
    encoded_fixed_leading_magnitude_encode.
  setoid_rewrite encoded_fixed_homogeneous_value_encode.
  reflexivity.
Qed.

(* The exact MathComp Boolean used by the canonical sextic development is
   imported only for this final extensional bridge.  The Mu-recursive
   programs above remain built solely from [recalg] constructors. *)
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticRationalRootSearch SexticHomogeneousRootSearch.

Module ExistingRootSearch :=
  PolynomialFormulasSexticHomogeneousRootSearch.
Module ExistingRationalRootSearch :=
  PolynomialFormulasSexticRationalRootSearch.
Module ExistingRecursiveCore :=
  PolynomialFormulasSexticRecursiveCore.

Import GRing.Theory.
Local Open Scope ring_scope.

(* Expose MathComp's concrete integer carrier uniformly to Stdlib's [ring]
   tactic.  Packed MathComp projections are definitionally equal, but the
   tactic keys structures by their syntactic carrier. *)
Local Definition mathcomp_int_ring : comPzRingType := int.
Local Definition mathcomp_int_carrier :=
  GRing.PzSemiRing.sort mathcomp_int_ring.
Local Definition mathcomp_int_zero : mathcomp_int_carrier := 0.
Local Definition mathcomp_int_one : mathcomp_int_carrier := 1.
Local Definition mathcomp_int_add :
    mathcomp_int_carrier -> mathcomp_int_carrier -> mathcomp_int_carrier :=
  @GRing.add mathcomp_int_ring.
Local Definition mathcomp_int_mul :
    mathcomp_int_carrier -> mathcomp_int_carrier -> mathcomp_int_carrier :=
  @GRing.mul mathcomp_int_ring.
Local Definition mathcomp_int_sub :
    mathcomp_int_carrier -> mathcomp_int_carrier -> mathcomp_int_carrier :=
  fun x y => x - y.
Local Definition mathcomp_int_opp :
    mathcomp_int_carrier -> mathcomp_int_carrier :=
  @GRing.opp mathcomp_int_ring.
Local Definition mathcomp_int_eq :
    mathcomp_int_carrier -> mathcomp_int_carrier -> Prop := eq.

Lemma mathcomp_int_addE x y : x + y = mathcomp_int_add x y.
Proof. reflexivity. Qed.
Lemma mathcomp_int_mulE x y : x * y = mathcomp_int_mul x y.
Proof. reflexivity. Qed.
Lemma mathcomp_int_subE x y : x - y = mathcomp_int_sub x y.
Proof. reflexivity. Qed.
Lemma mathcomp_int_oppE x : - x = mathcomp_int_opp x.
Proof. reflexivity. Qed.
Lemma mathcomp_int_zeroE : (0 : int) = mathcomp_int_zero.
Proof. reflexivity. Qed.
Lemma mathcomp_int_oneE : (1 : int) = mathcomp_int_one.
Proof. reflexivity. Qed.

Lemma mathcomp_int_ring_theory :
  @ring_theory mathcomp_int_carrier mathcomp_int_zero mathcomp_int_one
    mathcomp_int_add mathcomp_int_mul mathcomp_int_sub mathcomp_int_opp
    mathcomp_int_eq.
Proof.
  constructor; unfold mathcomp_int_zero, mathcomp_int_one,
    mathcomp_int_add, mathcomp_int_mul, mathcomp_int_sub,
    mathcomp_int_opp, mathcomp_int_eq; intros.
  - exact: add0r.
  - exact: addrC.
  - exact: addrA.
  - exact: mul1r.
  - exact: mulrC.
  - exact: mulrA.
  - exact: mulrDl.
  - reflexivity.
  - exact: addrN.
Qed.

Add Ring mathcomp_int_ring_tactic : mathcomp_int_ring_theory.

Ltac finish_mathcomp_int_ring :=
  repeat first
    [ rewrite mathcomp_int_addE | rewrite mathcomp_int_mulE
    | rewrite mathcomp_int_subE | rewrite mathcomp_int_oppE
    | rewrite mathcomp_int_zeroE | rewrite mathcomp_int_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (mathcomp_int_eq lhs rhs)
  end;
  ring.

Definition mathcomp_zigzag_decode (code : nat) : int :=
  (zigzag_positive code)%:Z - (zigzag_negative code)%:Z.

Definition mathcomp_zigzag_encode (value : int) : nat :=
  match value with
  | Posz magnitude => 2 * magnitude
  | Negz magnitude => 2 * magnitude + 1
  end.

Lemma mathcomp_zigzag_decode_encode value :
  mathcomp_zigzag_decode (mathcomp_zigzag_encode value) = value.
Proof.
  case: value=> magnitude.
  - rewrite /mathcomp_zigzag_encode /mathcomp_zigzag_decode
      zigzag_positive_even zigzag_negative_even.
    by rewrite subr0.
  - rewrite /mathcomp_zigzag_encode /mathcomp_zigzag_decode
      zigzag_positive_odd zigzag_negative_odd.
    by rewrite sub0r NegzE.
Qed.

Definition eval_mathcomp_signed_expression {arity}
    (expression : signed_expression arity) v : int :=
  (eval_nat_expression (signed_positive expression) v)%:Z -
  (eval_nat_expression (signed_negative expression) v)%:Z.

Lemma eval_mathcomp_signed_coefficient {arity} (variable : pos arity) v :
  eval_mathcomp_signed_expression (signed_coefficient variable) v =
  mathcomp_zigzag_decode (vec_pos v variable).
Proof. reflexivity. Qed.

Lemma eval_mathcomp_signed_plus {arity}
    (left right : signed_expression arity) v :
  eval_mathcomp_signed_expression (signed_plus left right) v =
  eval_mathcomp_signed_expression left v +
    eval_mathcomp_signed_expression right v.
Proof.
  rewrite /eval_mathcomp_signed_expression /signed_plus /= !PoszD.
  finish_mathcomp_int_ring.
Qed.

Lemma eval_mathcomp_signed_negate {arity}
    (expression : signed_expression arity) v :
  eval_mathcomp_signed_expression (signed_negate expression) v =
  - eval_mathcomp_signed_expression expression v.
Proof.
  rewrite /eval_mathcomp_signed_expression /signed_negate /=.
  finish_mathcomp_int_ring.
Qed.

Lemma eval_mathcomp_signed_mult {arity}
    (left right : signed_expression arity) v :
  eval_mathcomp_signed_expression (signed_mult left right) v =
  eval_mathcomp_signed_expression left v *
    eval_mathcomp_signed_expression right v.
Proof.
  rewrite /eval_mathcomp_signed_expression /signed_mult /= !PoszD !PoszM.
  finish_mathcomp_int_ring.
Qed.

Lemma eval_mathcomp_signed_of_nat_expression {arity}
    (expression : nat_expression arity) v :
  eval_mathcomp_signed_expression (signed_of_nat_expression expression) v =
  (eval_nat_expression expression v)%:Z.
Proof. by rewrite /eval_mathcomp_signed_expression /signed_of_nat_expression /= subr0. Qed.

Lemma eval_mathcomp_signed_power {arity}
    (expression : signed_expression arity) exponent v :
  eval_mathcomp_signed_expression (signed_power expression exponent) v =
  eval_mathcomp_signed_expression expression v ^+ exponent.
Proof.
  elim: exponent=> [|exponent IH] /=.
  - by rewrite eval_mathcomp_signed_of_nat_expression expr0.
  - by rewrite eval_mathcomp_signed_mult IH exprS.
Qed.

Theorem eval_mathcomp_signed_homogeneous_list_expression {arity}
    (coefficients : list (signed_expression arity)) numerator denominator
    values :
  eval_mathcomp_signed_expression
    (signed_homogeneous_list_expression coefficients numerator denominator)
    values =
  ExistingRationalRootSearch.homogeneous_eval
    (List.map (fun coefficient =>
      eval_mathcomp_signed_expression coefficient values) coefficients)
    (eval_mathcomp_signed_expression numerator values)
    (eval_mathcomp_signed_expression denominator values).
Proof.
  elim: coefficients=> [|coefficient coefficients IH] /=.
  - exact: eval_mathcomp_signed_of_nat_expression.
  - rewrite eval_mathcomp_signed_plus !eval_mathcomp_signed_mult
      eval_mathcomp_signed_power IH size_map.
    reflexivity.
Qed.

Lemma signed_zero_mathcomp_iff {arity}
    (expression : signed_expression arity) values :
  eval_signed_expression expression values = Z0 <->
  eval_mathcomp_signed_expression expression values = 0.
Proof.
  unfold eval_signed_expression, eval_mathcomp_signed_expression.
  remember (eval_nat_expression (signed_positive expression) values)
    as positive.
  remember (eval_nat_expression (signed_negative expression) values)
    as negative.
  split.
  - move=> Hzero.
    have -> : positive = negative by lia.
    exact: subrr.
  - move=> Hzero.
    have Hcast : positive%:Z = negative%:Z := subr0_eq Hzero.
    have Hequal : positive = negative.
    { move: (congr1 absz Hcast). by []. }
    by rewrite Hequal Z.sub_diag.
Qed.

Definition encode_mathcomp_fixed_coefficients {count}
    (coefficients : Vector.t int count) : Vector.t nat count :=
  vec_map mathcomp_zigzag_encode coefficients.

Lemma mathcomp_zigzag_magnitude_encode value :
  zigzag_magnitude (mathcomp_zigzag_encode value) = absz value.
Proof.
  case: value=> magnitude.
  - rewrite /mathcomp_zigzag_encode /zigzag_magnitude
      zigzag_positive_even zigzag_negative_even.
    by rewrite Nat.sub_0_r Nat.sub_0_l Nat.add_0_r.
  - rewrite /mathcomp_zigzag_encode /zigzag_magnitude
      zigzag_positive_odd zigzag_negative_odd.
    by rewrite Nat.sub_0_l Nat.sub_0_r Nat.add_0_l.
Qed.

Lemma eval_mathcomp_shifted_fixed_coefficient_expressions degree
    denominator_index numerator_index
    (coefficients : Vector.t int (S degree)) :
  List.map
    (fun expression => eval_mathcomp_signed_expression expression
      (denominator_index ## numerator_index ##
        encode_mathcomp_fixed_coefficients coefficients))
    (shifted_fixed_coefficient_expressions degree) =
  vec_list coefficients.
Proof.
  unfold shifted_fixed_coefficient_expressions,
    encode_mathcomp_fixed_coefficients.
  assert (Hcoefficients :
      vec_set_pos (fun variable => vec_pos coefficients variable) =
      coefficients).
  { apply vec_pos_ext. intro variable. rewrite vec_pos_set. reflexivity. }
  rewrite <- Hcoefficients.
  rewrite vec_list_vec_set_pos !List.map_map.
  apply List.map_ext.
  intro variable.
  rewrite eval_mathcomp_signed_coefficient.
  change
    (mathcomp_zigzag_decode
      (vec_pos
        (vec_map mathcomp_zigzag_encode
          (vec_set_pos
            (fun variable => vec_pos coefficients variable))) variable) =
     vec_pos coefficients variable).
  rewrite vec_pos_map vec_pos_set mathcomp_zigzag_decode_encode.
  reflexivity.
Qed.

Definition mathcomp_fixed_homogeneous_value {degree}
    (coefficients : Vector.t int (S degree))
    (numerator_index denominator_index : nat) : int :=
  ExistingRationalRootSearch.homogeneous_eval (vec_list coefficients)
    (numerator_index%:Z -
      (absz (vec_pos coefficients pos0))%:Z)
    (S denominator_index)%:Z.

Lemma eval_mathcomp_encoded_fixed_numerator_expression degree
    denominator_index numerator_index
    (coefficients : Vector.t int (S degree)) :
  eval_mathcomp_signed_expression
    (encoded_fixed_numerator_expression degree)
    (denominator_index ## numerator_index ##
      encode_mathcomp_fixed_coefficients coefficients) =
  numerator_index%:Z - (absz (vec_pos coefficients pos0))%:Z.
Proof.
  unfold encoded_fixed_numerator_expression, signed_minus.
  rewrite eval_mathcomp_signed_plus eval_mathcomp_signed_negate
    !eval_mathcomp_signed_of_nat_expression.
  have Hmagnitude :
      eval_nat_expression
        (signed_coefficient_magnitude_expression
          (pos_nxt (pos_nxt pos0)))
        (denominator_index ## numerator_index ##
          encode_mathcomp_fixed_coefficients coefficients) =
      absz (vec_pos coefficients pos0).
  { change
      (zigzag_magnitude
        (vec_pos (encode_mathcomp_fixed_coefficients coefficients) pos0) =
       absz (vec_pos coefficients pos0)).
    unfold encode_mathcomp_fixed_coefficients.
    by rewrite vec_pos_map mathcomp_zigzag_magnitude_encode. }
  rewrite Hmagnitude.
  finish_mathcomp_int_ring.
Qed.

Lemma eval_mathcomp_encoded_fixed_denominator_expression degree
    denominator_index numerator_index
    (coefficients : Vector.t int (S degree)) :
  eval_mathcomp_signed_expression
    (encoded_fixed_denominator_expression degree)
    (denominator_index ## numerator_index ##
      encode_mathcomp_fixed_coefficients coefficients) =
  (S denominator_index)%:Z.
Proof.
  unfold encoded_fixed_denominator_expression.
  rewrite eval_mathcomp_signed_of_nat_expression. reflexivity.
Qed.

Theorem eval_mathcomp_encoded_fixed_homogeneous_expression degree
    denominator_index numerator_index
    (coefficients : Vector.t int (S degree)) :
  eval_mathcomp_signed_expression
    (encoded_fixed_homogeneous_expression degree)
    (denominator_index ## numerator_index ##
      encode_mathcomp_fixed_coefficients coefficients) =
  mathcomp_fixed_homogeneous_value
    coefficients numerator_index denominator_index.
Proof.
  unfold encoded_fixed_homogeneous_expression,
    mathcomp_fixed_homogeneous_value.
  rewrite eval_mathcomp_signed_homogeneous_list_expression
    eval_mathcomp_shifted_fixed_coefficient_expressions
    eval_mathcomp_encoded_fixed_numerator_expression
    eval_mathcomp_encoded_fixed_denominator_expression.
  reflexivity.
Qed.

Lemma encoded_fixed_homogeneous_zero_mathcomp_iff degree denominator_index
    numerator_index (coefficients : Vector.t int (S degree)) :
  encoded_fixed_homogeneous_value
    (encode_mathcomp_fixed_coefficients coefficients)
    numerator_index denominator_index = Z0 <->
  mathcomp_fixed_homogeneous_value
    coefficients numerator_index denominator_index = 0.
Proof.
  rewrite -eval_encoded_fixed_homogeneous_expression
    -eval_mathcomp_encoded_fixed_homogeneous_expression.
  apply signed_zero_mathcomp_iff.
Qed.

Lemma zigzag_mathcomp_zero_iff code :
  zigzag_decode code = Z0 <-> mathcomp_zigzag_decode code = 0.
Proof.
  rewrite /zigzag_decode /mathcomp_zigzag_decode.
  remember (zigzag_positive code) as positive.
  remember (zigzag_negative code) as negative.
  split.
  - move=> Hzero.
    have -> : positive = negative by lia.
    exact: subrr.
  - move=> Hzero.
    have Hcast : positive%:Z = negative%:Z := subr0_eq Hzero.
    have Hequal : positive = negative.
    { move: (congr1 absz Hcast). by []. }
    by rewrite Hequal Z.sub_diag.
Qed.

Definition mathcomp_fixed_has_bounded_homogeneous_root {degree}
    (coefficients : Vector.t int (S degree)) : Prop :=
  vec_pos coefficients pos0 = 0 \/
  exists numerator_index,
    Nat.lt numerator_index
      (Nat.add
        (Nat.mul 2 (absz (vec_pos coefficients pos0))) 1) /\
    exists denominator_index,
      Nat.lt denominator_index
        (absz (vec_pos coefficients (final_position degree))) /\
      mathcomp_fixed_homogeneous_value
        coefficients numerator_index denominator_index = 0.

Lemma encoded_fixed_root_semantics_mathcomp_iff degree
    (coefficients : Vector.t int (S degree)) :
  encoded_fixed_has_bounded_homogeneous_root
    (encode_mathcomp_fixed_coefficients coefficients) <->
  mathcomp_fixed_has_bounded_homogeneous_root coefficients.
Proof.
  rewrite /encoded_fixed_has_bounded_homogeneous_root
    /mathcomp_fixed_has_bounded_homogeneous_root
    /encoded_fixed_constant_magnitude /encoded_fixed_leading_magnitude.
  unfold encode_mathcomp_fixed_coefficients.
  rewrite !vec_pos_map zigzag_mathcomp_zero_iff
    mathcomp_zigzag_decode_encode !mathcomp_zigzag_magnitude_encode.
  setoid_rewrite encoded_fixed_homogeneous_zero_mathcomp_iff.
  reflexivity.
Qed.

Theorem encoded_fixed_bounded_rootb_mathcomp_true_iff degree
    (coefficients : Vector.t int (S degree)) :
  encoded_fixed_bounded_rootb degree
    (encode_mathcomp_fixed_coefficients coefficients) = true <->
  mathcomp_fixed_has_bounded_homogeneous_root coefficients.
Proof.
  rewrite encoded_fixed_bounded_rootb_true_iff.
  apply encoded_fixed_root_semantics_mathcomp_iff.
Qed.

Lemma constant_coefficient_vec_list degree
    (coefficients : Vector.t int (S degree)) :
  ExistingRationalRootSearch.constant_coefficient (vec_list coefficients) =
  vec_pos coefficients pos0.
Proof.
  rewrite (vec_head_tail coefficients).
  reflexivity.
Qed.

Lemma mem_positive_interval_index radius value :
  value \in ExistingRationalRootSearch.positive_interval radius <->
  exists index,
    (index < radius)%N /\ value = (S index)%:Z.
Proof.
  rewrite /ExistingRationalRootSearch.positive_interval.
  split.
  - move/mapP=> [offset].
    rewrite mem_iota=> /andP [Hpositive Hupper] ->.
    case: offset Hpositive Hupper=> [|index] //= _ Hupper.
    exists index; split=> //.
  - move=> [index [Hbound ->]].
    apply/mapP; exists (S index)=> //.
    rewrite mem_iota; apply/andP; split=> //.
Qed.

Theorem mathcomp_fixed_root_semantics_existing_iff degree
    (coefficients : Vector.t int (S degree))
    (Hleading :
      ExistingRationalRootSearch.leading_coefficient
        (vec_list coefficients) =
      vec_pos coefficients (final_position degree)) :
  mathcomp_fixed_has_bounded_homogeneous_root coefficients <->
  ExistingRootSearch.bounded_homogeneous_rootb
    (vec_list coefficients) = true.
Proof.
  rewrite /mathcomp_fixed_has_bounded_homogeneous_root
    /ExistingRootSearch.bounded_homogeneous_rootb
    constant_coefficient_vec_list.
  case Hconstant:
    (vec_pos coefficients pos0 == 0).
  - have Hzero : vec_pos coefficients pos0 = 0 := eqP Hconstant.
    split=> // _. by left.
  - rewrite /=.
    split.
    + move=> [Hzero|[numerator_index [Hnumerator
          [denominator_index [Hdenominator Hroot]]]]].
      * move: Hconstant. by rewrite Hzero eqxx.
      * apply/hasP.
        exists (numerator_index%:Z -
          (absz (vec_pos coefficients pos0))%:Z).
        -- rewrite /ExistingRationalRootSearch.numerator_candidates
             constant_coefficient_vec_list.
           apply/(ExistingRecursiveCore.mem_symmetric_interval _ _).
           exists numerator_index; split.
           ++ apply/ltP.
              by rewrite mulnE addnE.
           ++ reflexivity.
        -- apply/hasP.
           exists (S denominator_index)%:Z.
           ++ rewrite /ExistingRationalRootSearch.denominator_candidates
                Hleading.
              apply/(mem_positive_interval_index _ _).
              exists denominator_index; split.
              ** exact/ltP.
              ** reflexivity.
           ++ apply/eqP. exact Hroot.
    + move/hasP=> [numerator Hnumerator /hasP
        [denominator Hdenominator /eqP Hroot]].
      right.
      rewrite /ExistingRationalRootSearch.numerator_candidates
        constant_coefficient_vec_list in Hnumerator.
      move/(ExistingRecursiveCore.mem_symmetric_interval _ _):
        Hnumerator=> [numerator_index [Hnumerator Hnumerator_value]].
      rewrite /ExistingRationalRootSearch.denominator_candidates
        Hleading in Hdenominator.
      move/(mem_positive_interval_index _ _): Hdenominator=>
        [denominator_index [Hdenominator Hdenominator_value]].
      rewrite Hnumerator_value Hdenominator_value in Hroot.
      exists numerator_index; split.
      * exact: (elimT ltP Hnumerator).
      * exists denominator_index; split.
        -- exact: (elimT ltP Hdenominator).
        -- exact Hroot.
Qed.

Corollary encoded_fixed_bounded_rootb_existing_true_iff degree
    (coefficients : Vector.t int (S degree))
    (Hleading :
      ExistingRationalRootSearch.leading_coefficient
        (vec_list coefficients) =
      vec_pos coefficients (final_position degree)) :
  encoded_fixed_bounded_rootb degree
    (encode_mathcomp_fixed_coefficients coefficients) = true <->
  ExistingRationalRootSearch.bounded_rational_rootb
    (vec_list coefficients) = true.
Proof.
  rewrite encoded_fixed_bounded_rootb_mathcomp_true_iff.
  rewrite (@mathcomp_fixed_root_semantics_existing_iff
    degree coefficients Hleading).
  by rewrite ExistingRootSearch.bounded_homogeneous_rootbE.
Qed.

Print Assumptions recalg_graph_murec.
Print Assumptions compile_nat_expression_correct.
Print Assumptions compile_nat_expression_primitive_recursive.
Print Assumptions compile_nat_bounded_exists_outputs_one_iff.
Print Assumptions eval_signed_absolute_magnitude_expression.
Print Assumptions eval_signed_homogeneous_list_expression.
Print Assumptions eval_encoded_sextic_homogeneous_expression.
Print Assumptions encoded_sextic_bounded_rootb_encoded_true_iff.
Print Assumptions encoded_sextic_bounded_root_relation_murec.
Print Assumptions encoded_sextic_bounded_root_code_relation_murec.
Print Assumptions eval_encoded_monic_has_proper_factor_true_iff.
Print Assumptions encoded_monic_proper_factor_relation_murec.
Print Assumptions encoded_monic_proper_factor_code_relation_murec.
Print Assumptions eval_encoded_fixed_homogeneous_expression.
Print Assumptions encoded_fixed_bounded_root_relation_murec.
Print Assumptions encoded_fixed_bounded_root_code_relation_murec.
Print Assumptions encoded_pair_resolvent_bounded_root_relation_murec.
Print Assumptions encoded_triple_resolvent_bounded_root_relation_murec.
Print Assumptions encoded_fixed_bounded_rootb_encoded_true_iff.
Print Assumptions encoded_fixed_bounded_rootb_mathcomp_true_iff.
Print Assumptions mathcomp_fixed_root_semantics_existing_iff.
Print Assumptions encoded_fixed_bounded_rootb_existing_true_iff.
Print Assumptions zigzag_decode_encode.
Print Assumptions seven_signed_relation_murec.
Print Assumptions seven_signed_code_relation_murec.
