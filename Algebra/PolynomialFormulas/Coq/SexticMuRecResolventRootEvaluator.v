(* ===================================================================== *)
(*  Direct Mu-recursive homogeneous tests for the sextic resolvents.     *)
(*                                                                       *)
(*  Materializing all sixteen or eleven coefficients is unnecessary.    *)
(*  We expand the invariant product [prod (u - v * descriptor)] directly *)
(*  and feed every sparse monomial to the checked Newton/Mobius engine.  *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia List Vector ZArith.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From mathcomp Require Import all_ssreflect all_algebra.

From PolynomialFormulas Require Import
  SexticMuRecComputability SexticMuRecSparseEvaluator
  SexticMuRecCollisionEvaluator.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Module PolynomialFormulasSexticMuRecResolventRootEvaluator.

Import PolynomialFormulasSexticMuRecSparseEvaluator.
Import PolynomialFormulasSexticMuRecCollisionEvaluator.

(* --------------------------------------------------------------------- *)
(* One mixed-radix homogeneous evaluator for either descriptor family.  *)

Definition recursive_descriptor_coefficient_builder : Type :=
  forall arity : nat,
    recursive_expression arity -> recursive_expression arity ->
    recursive_expression arity -> recursive_signed_expression arity.

Definition recursive_descriptor_exponent_builder : Type :=
  forall arity : nat,
    recursive_expression arity -> recursive_expression arity -> nat ->
    recursive_expression arity.

Definition resolvent_homogeneous_factor_coefficient_from {arity}
    (descriptor_coefficient : recursive_descriptor_coefficient_builder)
    (digit x0 x1 denominator : recursive_expression arity)
    (numerator : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_if_zero digit numerator
    (recursive_signed_mult
      (recursive_signed_negate
        (recursive_signed_of_nat denominator))
      (descriptor_coefficient arity
        (RecMinus digit (RecConst 1)) x0 x1)).

Definition resolvent_homogeneous_factor_exponent_from {arity}
    (descriptor_exponent : recursive_descriptor_exponent_builder)
    (partition digit : recursive_expression arity)
    (coordinate : nat) : recursive_expression arity :=
  RecIfZero digit (RecConst 0)
    (descriptor_exponent arity partition
      (RecMinus digit (RecConst 1)) coordinate).

Definition resolvent_homogeneous_state_step_from {arity}
    (descriptor_terms : nat)
    (descriptor_coefficient : recursive_descriptor_coefficient_builder)
    (descriptor_exponent : recursive_descriptor_exponent_builder)
    (state x0 x1 denominator : recursive_expression arity)
    (numerator : recursive_signed_expression arity) :
    recursive_expression arity :=
  let factor := recursive_project9 pos0 state in
  let remaining := recursive_project9 pos1 state in
  let coefficient_code := recursive_project9 pos2 state in
  let exponent0 := recursive_project9 pos3 state in
  let exponent1 := recursive_project9 pos4 state in
  let exponent2 := recursive_project9 pos5 state in
  let exponent3 := recursive_project9 pos6 state in
  let exponent4 := recursive_project9 pos7 state in
  let exponent5 := recursive_project9 pos8 state in
  let digit := RecRemSucc remaining descriptor_terms in
  let next_remaining := RecDivSucc remaining descriptor_terms in
  let factor_coefficient :=
    resolvent_homogeneous_factor_coefficient_from
      descriptor_coefficient digit x0 x1 denominator numerator in
  let next_coefficient :=
    recursive_signed_code
      (recursive_signed_mult (recursive_signed_decode coefficient_code)
        factor_coefficient) in
  let next_exponent coordinate previous :=
    RecPlus previous
      (resolvent_homogeneous_factor_exponent_from descriptor_exponent
        factor digit coordinate) in
  recursive_inject9 (RecSucc factor) next_remaining next_coefficient
    (next_exponent 0 exponent0) (next_exponent 1 exponent1)
    (next_exponent 2 exponent2) (next_exponent 3 exponent3)
    (next_exponent 4 exponent4) (next_exponent 5 exponent5).

Definition resolvent_homogeneous_term_state_from {arity}
    (descriptor_terms partition_count : nat)
    (descriptor_coefficient : recursive_descriptor_coefficient_builder)
    (descriptor_exponent : recursive_descriptor_exponent_builder)
    (term_index x0 x1 denominator : recursive_expression arity)
    (numerator : recursive_signed_expression arity) :
    recursive_expression arity :=
  RecIter (RecConst partition_count)
    (recursive_inject9 (RecConst 0) term_index
      (recursive_signed_code recursive_signed_one)
      (RecConst 0) (RecConst 0) (RecConst 0)
      (RecConst 0) (RecConst 0) (RecConst 0))
    (resolvent_homogeneous_state_step_from descriptor_terms
      descriptor_coefficient descriptor_exponent (RecVar pos0)
      (recursive_weaken x0) (recursive_weaken x1)
      (recursive_weaken denominator) (recursive_signed_weaken numerator)).

Definition resolvent_homogeneous_term_count_from {arity}
    (descriptor_terms partition_count : nat) :
    recursive_expression arity :=
  RecIter (RecConst partition_count) (RecConst 1)
    (RecMult (RecVar pos0) (RecConst (S descriptor_terms))).

Definition resolvent_homogeneous_term_code_from {arity}
    (descriptor_terms partition_count : nat)
    (descriptor_coefficient : recursive_descriptor_coefficient_builder)
    (descriptor_exponent : recursive_descriptor_exponent_builder)
    (term_index x0 x1 denominator : recursive_expression arity)
    (numerator e1 e2 e3 e4 e5 e6 :
      recursive_signed_expression arity) : recursive_expression arity :=
  RecIter (RecConst 1)
    (resolvent_homogeneous_term_state_from descriptor_terms partition_count
      descriptor_coefficient descriptor_exponent
      term_index x0 x1 denominator numerator)
    (recursive_signed_code
      (recursive_signed_mult
        (recursive_signed_decode
          (recursive_project9 pos2 (RecVar pos0)))
        (recursive_newton_mobius_from
          (recursive_project9 pos3 (RecVar pos0))
          (recursive_project9 pos4 (RecVar pos0))
          (recursive_project9 pos5 (RecVar pos0))
          (recursive_project9 pos6 (RecVar pos0))
          (recursive_project9 pos7 (RecVar pos0))
          (recursive_project9 pos8 (RecVar pos0))
          (recursive_signed_weaken e1) (recursive_signed_weaken e2)
          (recursive_signed_weaken e3) (recursive_signed_weaken e4)
          (recursive_signed_weaken e5) (recursive_signed_weaken e6)))).

Definition resolvent_scaled_homogeneous_from {arity}
    (descriptor_terms partition_count : nat)
    (descriptor_coefficient : recursive_descriptor_coefficient_builder)
    (descriptor_exponent : recursive_descriptor_exponent_builder)
    (x0 x1 denominator : recursive_expression arity)
    (numerator e1 e2 e3 e4 e5 e6 :
      recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_bounded_sum
    (resolvent_homogeneous_term_count_from
      descriptor_terms partition_count)
    (recursive_signed_decode
      (resolvent_homogeneous_term_code_from
        descriptor_terms partition_count
        descriptor_coefficient descriptor_exponent
        (RecVar pos0) (recursive_weaken x0) (recursive_weaken x1)
        (recursive_weaken denominator) (recursive_signed_weaken numerator)
        (recursive_signed_weaken e1) (recursive_signed_weaken e2)
        (recursive_signed_weaken e3) (recursive_signed_weaken e4)
        (recursive_signed_weaken e5) (recursive_signed_weaken e6))).

Definition recursive_homogeneous_builder : Type :=
  forall arity : nat,
    recursive_expression arity -> recursive_expression arity ->
    recursive_expression arity -> recursive_signed_expression arity ->
    recursive_signed_expression arity -> recursive_signed_expression arity ->
    recursive_signed_expression arity -> recursive_signed_expression arity ->
    recursive_signed_expression arity -> recursive_signed_expression arity ->
    recursive_signed_expression arity.

(** Builder argument order is [x0], [x1], [denominator], [numerator],
    followed by the six elementary symmetric values. *)
Definition pair_scaled_homogeneous_from : recursive_homogeneous_builder :=
  fun arity x0 x1 denominator numerator e1 e2 e3 e4 e5 e6 =>
    resolvent_scaled_homogeneous_from 125 15
      (@pair_descriptor_coefficient_from)
      (@pair_descriptor_exponent_from)
      x0 x1 denominator numerator e1 e2 e3 e4 e5 e6.

Definition triple_scaled_homogeneous_from : recursive_homogeneous_builder :=
  fun arity x0 x1 denominator numerator e1 e2 e3 e4 e5 e6 =>
    resolvent_scaled_homogeneous_from 81 10
      (@triple_descriptor_coefficient_from)
      (@triple_descriptor_exponent_from)
      x0 x1 denominator numerator e1 e2 e3 e4 e5 e6.

(* --------------------------------------------------------------------- *)
(* Public direct homogeneous-value programs.                             *)

(** Inputs are zigzag codes [f0,...,f5], natural parameters [x0,x1],
    a zigzag numerator code [u], and a natural denominator [v]. *)
Definition pair_scaled_homogeneous_signed_expression :
    recursive_signed_expression 10 :=
  @pair_scaled_homogeneous_from 10
    (RecVar pos6) (RecVar pos7) (RecVar pos9)
    (recursive_signed_input pos8)
    (recursive_signed_negate (recursive_signed_input pos5))
    (recursive_signed_input pos4)
    (recursive_signed_negate (recursive_signed_input pos3))
    (recursive_signed_input pos2)
    (recursive_signed_negate (recursive_signed_input pos1))
    (recursive_signed_input pos0).

Definition triple_scaled_homogeneous_signed_expression :
    recursive_signed_expression 10 :=
  @triple_scaled_homogeneous_from 10
    (RecVar pos6) (RecVar pos7) (RecVar pos9)
    (recursive_signed_input pos8)
    (recursive_signed_negate (recursive_signed_input pos5))
    (recursive_signed_input pos4)
    (recursive_signed_negate (recursive_signed_input pos3))
    (recursive_signed_input pos2)
    (recursive_signed_negate (recursive_signed_input pos1))
    (recursive_signed_input pos0).

Definition pair_scaled_homogeneous_code_expression :
    recursive_expression 10 :=
  recursive_signed_code pair_scaled_homogeneous_signed_expression.

Definition triple_scaled_homogeneous_code_expression :
    recursive_expression 10 :=
  recursive_signed_code triple_scaled_homogeneous_signed_expression.

Definition encoded_pair_scaled_homogeneous_value
    (values : Vector.t nat 10) : nat :=
  eval_recursive_expression pair_scaled_homogeneous_code_expression values.

Definition encoded_triple_scaled_homogeneous_value
    (values : Vector.t nat 10) : nat :=
  eval_recursive_expression triple_scaled_homogeneous_code_expression values.

Definition ra_pair_scaled_homogeneous_value : recalg 10 :=
  compile_recursive_expression pair_scaled_homogeneous_code_expression.

Definition ra_triple_scaled_homogeneous_value : recalg 10 :=
  compile_recursive_expression triple_scaled_homogeneous_code_expression.

Theorem ra_pair_scaled_homogeneous_value_correct values :
  ⟦ra_pair_scaled_homogeneous_value⟧ values
    (encoded_pair_scaled_homogeneous_value values).
Proof. exact: compile_recursive_expression_correct. Qed.

Theorem ra_triple_scaled_homogeneous_value_correct values :
  ⟦ra_triple_scaled_homogeneous_value⟧ values
    (encoded_triple_scaled_homogeneous_value values).
Proof. exact: compile_recursive_expression_correct. Qed.

Theorem ra_pair_scaled_homogeneous_value_primitive_recursive :
  prim_rec ra_pair_scaled_homogeneous_value.
Proof. exact: compile_recursive_expression_primitive_recursive. Qed.

Theorem ra_triple_scaled_homogeneous_value_primitive_recursive :
  prim_rec ra_triple_scaled_homogeneous_value.
Proof. exact: compile_recursive_expression_primitive_recursive. Qed.

(* --------------------------------------------------------------------- *)
(* Bounded rational-root search without coefficient materialization.     *)

Definition recursive_signed_absolute_magnitude {arity}
    (expression : recursive_signed_expression arity) :
    recursive_expression arity :=
  RecPlus
    (RecMinus (recursive_positive expression)
      (recursive_negative expression))
    (RecMinus (recursive_negative expression)
      (recursive_positive expression)).

Definition recursive_weaken2 {arity}
    (expression : recursive_expression arity) :
    recursive_expression (S (S arity)) :=
  recursive_weaken (recursive_weaken expression).

Definition recursive_signed_weaken2 {arity}
    (expression : recursive_signed_expression arity) :
    recursive_signed_expression (S (S arity)) :=
  recursive_signed_weaken (recursive_signed_weaken expression).

Definition resolvent_root_test_expression_from {arity}
    (homogeneous : recursive_homogeneous_builder)
    (constant : recursive_signed_expression arity)
    (x0 x1 : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_expression arity :=
  let magnitude := recursive_signed_absolute_magnitude constant in
  let numerator : recursive_signed_expression (S (S arity)) :=
    {| recursive_positive := RecVar pos1;
       recursive_negative := recursive_weaken2 magnitude |} in
  let denominator : recursive_expression (S (S arity)) :=
    RecSucc (RecVar pos0) in
  let candidate := @homogeneous (S (S arity))
    (recursive_weaken2 x0) (recursive_weaken2 x1) denominator numerator
    (recursive_signed_weaken2 e1) (recursive_signed_weaken2 e2)
    (recursive_signed_weaken2 e3) (recursive_signed_weaken2 e4)
    (recursive_signed_weaken2 e5) (recursive_signed_weaken2 e6) in
  let denominator_hit : recursive_expression (S (S arity)) :=
    RecIfZero (recursive_signed_code candidate)
      (RecConst 1) (RecConst 0) in
  let numerator_hit : recursive_expression (S arity) :=
    RecIfZero (RecBoundedSum (RecConst 720) denominator_hit)
      (RecConst 0) (RecConst 1) in
  let numerator_count := RecSucc (RecMult (RecConst 2) magnitude) in
  let search := RecBoundedSum numerator_count numerator_hit in
  RecIfZero magnitude (RecConst 1)
    (RecIfZero search (RecConst 0) (RecConst 1)).

Definition pair_scaled_constant_signed_expression :
    recursive_signed_expression 8 :=
  @pair_scaled_homogeneous_from 8
    (RecVar pos6) (RecVar pos7) (RecConst 1) recursive_signed_zero
    (recursive_signed_negate (recursive_signed_input pos5))
    (recursive_signed_input pos4)
    (recursive_signed_negate (recursive_signed_input pos3))
    (recursive_signed_input pos2)
    (recursive_signed_negate (recursive_signed_input pos1))
    (recursive_signed_input pos0).

Definition triple_scaled_constant_signed_expression :
    recursive_signed_expression 8 :=
  @triple_scaled_homogeneous_from 8
    (RecVar pos6) (RecVar pos7) (RecConst 1) recursive_signed_zero
    (recursive_signed_negate (recursive_signed_input pos5))
    (recursive_signed_input pos4)
    (recursive_signed_negate (recursive_signed_input pos3))
    (recursive_signed_input pos2)
    (recursive_signed_negate (recursive_signed_input pos1))
    (recursive_signed_input pos0).

Definition pair_resolvent_root_test_expression : recursive_expression 8 :=
  resolvent_root_test_expression_from pair_scaled_homogeneous_from
    pair_scaled_constant_signed_expression
    (RecVar pos6) (RecVar pos7)
    (recursive_signed_negate (recursive_signed_input pos5))
    (recursive_signed_input pos4)
    (recursive_signed_negate (recursive_signed_input pos3))
    (recursive_signed_input pos2)
    (recursive_signed_negate (recursive_signed_input pos1))
    (recursive_signed_input pos0).

Definition triple_resolvent_root_test_expression : recursive_expression 8 :=
  resolvent_root_test_expression_from triple_scaled_homogeneous_from
    triple_scaled_constant_signed_expression
    (RecVar pos6) (RecVar pos7)
    (recursive_signed_negate (recursive_signed_input pos5))
    (recursive_signed_input pos4)
    (recursive_signed_negate (recursive_signed_input pos3))
    (recursive_signed_input pos2)
    (recursive_signed_negate (recursive_signed_input pos1))
    (recursive_signed_input pos0).

Definition encoded_pair_resolvent_root_indicator
    (values : Vector.t nat 8) : nat :=
  eval_recursive_expression pair_resolvent_root_test_expression values.

Definition encoded_triple_resolvent_root_indicator
    (values : Vector.t nat 8) : nat :=
  eval_recursive_expression triple_resolvent_root_test_expression values.

Definition encoded_pair_resolvent_rootb
    (values : Vector.t nat 8) : bool :=
  Nat.eqb (encoded_pair_resolvent_root_indicator values) 1.

Definition encoded_triple_resolvent_rootb
    (values : Vector.t nat 8) : bool :=
  Nat.eqb (encoded_triple_resolvent_root_indicator values) 1.

Lemma ite_nested_zero_or_one first second :
  ite_rel first 1 (ite_rel second 0 1) = 0 \/
  ite_rel first 1 (ite_rel second 0 1) = 1.
Proof.
  unfold ite_rel.
  destruct first; [right|]; destruct second; auto.
Qed.

Lemma encoded_pair_resolvent_root_zero_or_one values :
  encoded_pair_resolvent_root_indicator values = 0 \/
  encoded_pair_resolvent_root_indicator values = 1.
Proof.
  unfold encoded_pair_resolvent_root_indicator,
    pair_resolvent_root_test_expression,
    resolvent_root_test_expression_from.
  cbn [eval_recursive_expression].
  exact: ite_nested_zero_or_one.
Qed.

Lemma encoded_triple_resolvent_root_zero_or_one values :
  encoded_triple_resolvent_root_indicator values = 0 \/
  encoded_triple_resolvent_root_indicator values = 1.
Proof.
  unfold encoded_triple_resolvent_root_indicator,
    triple_resolvent_root_test_expression,
    resolvent_root_test_expression_from.
  cbn [eval_recursive_expression].
  exact: ite_nested_zero_or_one.
Qed.

Lemma encoded_pair_resolvent_root_indicator_bool values :
  encoded_pair_resolvent_root_indicator values =
  bool_to_nat (encoded_pair_resolvent_rootb values).
Proof.
  destruct (encoded_pair_resolvent_root_zero_or_one values) as [H|H];
    unfold encoded_pair_resolvent_rootb, bool_to_nat; rewrite H; reflexivity.
Qed.

Lemma encoded_triple_resolvent_root_indicator_bool values :
  encoded_triple_resolvent_root_indicator values =
  bool_to_nat (encoded_triple_resolvent_rootb values).
Proof.
  destruct (encoded_triple_resolvent_root_zero_or_one values) as [H|H];
    unfold encoded_triple_resolvent_rootb, bool_to_nat; rewrite H; reflexivity.
Qed.

Definition ra_pair_resolvent_root : recalg 8 :=
  compile_recursive_expression pair_resolvent_root_test_expression.

Definition ra_triple_resolvent_root : recalg 8 :=
  compile_recursive_expression triple_resolvent_root_test_expression.

Theorem ra_pair_resolvent_root_correct values :
  ⟦ra_pair_resolvent_root⟧ values
    (bool_to_nat (encoded_pair_resolvent_rootb values)).
Proof.
  unfold ra_pair_resolvent_root.
  rewrite <- encoded_pair_resolvent_root_indicator_bool.
  exact: compile_recursive_expression_correct.
Qed.

Theorem ra_triple_resolvent_root_correct values :
  ⟦ra_triple_resolvent_root⟧ values
    (bool_to_nat (encoded_triple_resolvent_rootb values)).
Proof.
  unfold ra_triple_resolvent_root.
  rewrite <- encoded_triple_resolvent_root_indicator_bool.
  exact: compile_recursive_expression_correct.
Qed.

Theorem ra_pair_resolvent_root_primitive_recursive :
  prim_rec ra_pair_resolvent_root.
Proof. exact: compile_recursive_expression_primitive_recursive. Qed.

Theorem ra_triple_resolvent_root_primitive_recursive :
  prim_rec ra_triple_resolvent_root.
Proof. exact: compile_recursive_expression_primitive_recursive. Qed.

Print Assumptions ra_pair_scaled_homogeneous_value_correct.
Print Assumptions ra_triple_scaled_homogeneous_value_correct.
Print Assumptions ra_pair_resolvent_root_correct.
Print Assumptions ra_triple_resolvent_root_correct.
Print Assumptions ra_pair_resolvent_root_primitive_recursive.
Print Assumptions ra_triple_resolvent_root_primitive_recursive.

End PolynomialFormulasSexticMuRecResolventRootEvaluator.
