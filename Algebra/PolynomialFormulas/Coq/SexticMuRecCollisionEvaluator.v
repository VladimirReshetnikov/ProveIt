(* ===================================================================== *)
(*  Compact collision/resolvent evaluation above the checked Newton DSL. *)
(* ===================================================================== *)

From Stdlib Require Import Arith Lia List Vector ZArith.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From mathcomp Require Import all_ssreflect all_algebra.

From PolynomialFormulas Require Import
  SexticMuRecComputability SexticMuRecSparseEvaluator
  SexticPowerSumSymmetric SexticSparseResolvents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Module PolynomialFormulasSexticMuRecCollisionEvaluator.

Import PolynomialFormulasSexticMuRecSparseEvaluator.

(* --------------------------------------------------------------------- *)
(* Compact table lookup and the 203-term Mobius evaluator.               *)

Definition lift_pos_renaming {source target}
    (rename : pos source -> pos target) :
    pos (S source) -> pos (S target) :=
  fun variable =>
    Fin.caseS' variable (fun _ => pos (S target)) pos0
      (fun tail => pos_nxt (rename tail)).

Fixpoint recursive_rename {source target}
    (rename : pos source -> pos target)
    (expression : recursive_expression source) :
    recursive_expression target :=
  match expression with
  | RecConst constant => RecConst constant
  | RecVar variable => RecVar (rename variable)
  | RecSucc inner => RecSucc (recursive_rename rename inner)
  | RecPlus lhs rhs =>
      RecPlus (recursive_rename rename lhs) (recursive_rename rename rhs)
  | RecMinus lhs rhs =>
      RecMinus (recursive_rename rename lhs) (recursive_rename rename rhs)
  | RecMult lhs rhs =>
      RecMult (recursive_rename rename lhs) (recursive_rename rename rhs)
  | RecDivSucc dividend divisor =>
      RecDivSucc (recursive_rename rename dividend) divisor
  | RecRemSucc dividend divisor =>
      RecRemSucc (recursive_rename rename dividend) divisor
  | RecIfZero test if_zero if_nonzero =>
      RecIfZero (recursive_rename rename test)
        (recursive_rename rename if_zero)
        (recursive_rename rename if_nonzero)
  | RecDecompL code => RecDecompL (recursive_rename rename code)
  | RecDecompR code => RecDecompR (recursive_rename rename code)
  | RecRecomp lhs rhs =>
      RecRecomp (recursive_rename rename lhs) (recursive_rename rename rhs)
  | RecBoundedSum upper body =>
      RecBoundedSum (recursive_rename rename upper)
        (recursive_rename (lift_pos_renaming rename) body)
  | RecIter count initial step =>
      RecIter (recursive_rename rename count)
        (recursive_rename rename initial)
        (recursive_rename (lift_pos_renaming rename) step)
  end.

Definition recursive_weaken {arity}
    (expression : recursive_expression arity) :
    recursive_expression (S arity) :=
  recursive_rename (@pos_nxt arity) expression.

Definition recursive_signed_rename {source target}
    (rename : pos source -> pos target)
    (expression : recursive_signed_expression source) :
    recursive_signed_expression target :=
  {| recursive_positive :=
       recursive_rename rename (recursive_positive expression);
     recursive_negative :=
       recursive_rename rename (recursive_negative expression) |}.

Definition recursive_signed_weaken {arity}
    (expression : recursive_signed_expression arity) :
    recursive_signed_expression (S arity) :=
  recursive_signed_rename (@pos_nxt arity) expression.

Definition newton_sparse_power_from {arity}
    (power : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_expression arity :=
  RecIfZero power
    (recursive_signed_code (recursive_signed_nat 6))
    (recursive_project6 pos0
      (RecIter (RecMinus power (RecConst 1))
        (newton_initial_state_from e1 e2 e3 e4 e5 e6)
        (newton_step_from (RecVar pos0)
          (recursive_signed_weaken e1) (recursive_signed_weaken e2)
          (recursive_signed_weaken e3) (recursive_signed_weaken e4)
          (recursive_signed_weaken e5) (recursive_signed_weaken e6)))).

Fixpoint recursive_lookup_list {arity}
    (table : list nat) (index : recursive_expression arity) :
    recursive_expression arity :=
  match table with
  | List.nil => RecConst 0
  | List.cons value tail =>
      RecIfZero index (RecConst value)
        (recursive_lookup_list tail (RecMinus index (RecConst 1)))
  end.

Definition recursive_signed_bounded_sum {arity}
    (upper : recursive_expression arity)
    (body : recursive_signed_expression (S arity)) :
    recursive_signed_expression arity :=
  {| recursive_positive :=
       RecBoundedSum upper (recursive_positive body);
     recursive_negative :=
       RecBoundedSum upper (recursive_negative body) |}.

Fixpoint partition_block_mask_from
    (bit : nat) (labels : list nat) (block : nat) : nat :=
  match labels with
  | List.nil => 0
  | List.cons label tail =>
      (if Nat.eqb label block then Nat.pow 2 bit else 0) +
      partition_block_mask_from (S bit) tail block
  end.

Definition partition_block_mask (labels : list nat) (block : nat) : nat :=
  partition_block_mask_from 0 labels block.

Definition partition_block_mask_table (block : nat) : list nat :=
  List.map (fun labels => partition_block_mask labels block)
    PolynomialFormulasSexticPowerSumSymmetric.partition_codes.

Definition partition_mobius_positive_table : list nat :=
  List.map
    PolynomialFormulasSexticPowerSumSymmetric.partition_mobius_positive
    PolynomialFormulasSexticPowerSumSymmetric.partition_codes.

Definition partition_mobius_negative_table : list nat :=
  List.map
    PolynomialFormulasSexticPowerSumSymmetric.partition_mobius_negative
    PolynomialFormulasSexticPowerSumSymmetric.partition_codes.

Definition recursive_partition_mask {arity} (block : nat)
    (partition : recursive_expression arity) :
    recursive_expression arity :=
  recursive_lookup_list (partition_block_mask_table block) partition.

Definition recursive_mask_bit {arity}
    (mask : recursive_expression arity) (bit : nat) :
    recursive_expression arity :=
  RecRemSucc
    (RecDivSucc mask (Nat.pred (Nat.pow 2 bit))) 1.

Definition recursive_block_exponent {arity}
    (mask : recursive_expression arity)
    (x0 x1 x2 x3 x4 x5 : recursive_expression arity) :
    recursive_expression arity :=
  RecPlus (RecMult (recursive_mask_bit mask 0) x0)
    (RecPlus (RecMult (recursive_mask_bit mask 1) x1)
      (RecPlus (RecMult (recursive_mask_bit mask 2) x2)
        (RecPlus (RecMult (recursive_mask_bit mask 3) x3)
          (RecPlus (RecMult (recursive_mask_bit mask 4) x4)
            (RecMult (recursive_mask_bit mask 5) x5))))).

Definition recursive_newton_block_factor_from {arity}
    (mask exponent : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_decode
    (RecIfZero mask
      (recursive_signed_code (recursive_signed_nat 1))
      (newton_sparse_power_from exponent e1 e2 e3 e4 e5 e6)).

Definition recursive_partition_factor_from {arity}
    (partition : recursive_expression arity) (block : nat)
    (x0 x1 x2 x3 x4 x5 : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  let mask := recursive_partition_mask block partition in
  recursive_newton_block_factor_from mask
    (recursive_block_exponent mask x0 x1 x2 x3 x4 x5)
    e1 e2 e3 e4 e5 e6.

Definition recursive_partition_weight {arity}
    (partition : recursive_expression arity) :
    recursive_signed_expression arity :=
  {| recursive_positive :=
       recursive_lookup_list partition_mobius_positive_table partition;
     recursive_negative :=
       recursive_lookup_list partition_mobius_negative_table partition |}.

Definition recursive_mobius_partition_from {arity}
    (partition : recursive_expression arity)
    (x0 x1 x2 x3 x4 x5 : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_mult (recursive_partition_weight partition)
    (recursive_signed_mult
      (recursive_partition_factor_from partition 0 x0 x1 x2 x3 x4 x5
        e1 e2 e3 e4 e5 e6)
      (recursive_signed_mult
        (recursive_partition_factor_from partition 1 x0 x1 x2 x3 x4 x5
          e1 e2 e3 e4 e5 e6)
        (recursive_signed_mult
          (recursive_partition_factor_from partition 2 x0 x1 x2 x3 x4 x5
            e1 e2 e3 e4 e5 e6)
          (recursive_signed_mult
            (recursive_partition_factor_from partition 3 x0 x1 x2 x3 x4 x5
              e1 e2 e3 e4 e5 e6)
            (recursive_signed_mult
              (recursive_partition_factor_from partition 4 x0 x1 x2 x3 x4 x5
                e1 e2 e3 e4 e5 e6)
              (recursive_partition_factor_from partition 5 x0 x1 x2 x3 x4 x5
                e1 e2 e3 e4 e5 e6)))))).

Definition recursive_newton_mobius_from {arity}
    (x0 x1 x2 x3 x4 x5 : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_bounded_sum (RecConst 203)
    (recursive_mobius_partition_from (RecVar pos0)
      (recursive_weaken x0) (recursive_weaken x1)
      (recursive_weaken x2) (recursive_weaken x3)
      (recursive_weaken x4) (recursive_weaken x5)
      (recursive_signed_weaken e1) (recursive_signed_weaken e2)
      (recursive_signed_weaken e3) (recursive_signed_weaken e4)
      (recursive_signed_weaken e5) (recursive_signed_weaken e6)).

Definition newton_sparse_term_signed_expression :
    recursive_signed_expression 13 :=
  recursive_signed_mult (recursive_signed_input pos0)
    (recursive_newton_mobius_from
      (RecVar pos1) (RecVar pos2) (RecVar pos3)
      (RecVar pos4) (RecVar pos5) (RecVar pos6)
      (recursive_signed_input pos7) (recursive_signed_input pos8)
      (recursive_signed_input pos9) (recursive_signed_input pos10)
      (recursive_signed_input pos11) (recursive_signed_input pos12)).

Definition newton_sparse_term_code_expression : recursive_expression 13 :=
  recursive_signed_code newton_sparse_term_signed_expression.

Definition encoded_newton_sparse_term (values : Vector.t nat 13) : nat :=
  eval_recursive_expression newton_sparse_term_code_expression values.

Definition ra_newton_sparse_term : recalg 13 :=
  compile_recursive_expression newton_sparse_term_code_expression.

Theorem ra_newton_sparse_term_correct values :
  ⟦ra_newton_sparse_term⟧ values (encoded_newton_sparse_term values).
Proof. exact: compile_recursive_expression_correct. Qed.

Theorem ra_newton_sparse_term_primitive_recursive :
  prim_rec ra_newton_sparse_term.
Proof. exact: compile_recursive_expression_primitive_recursive. Qed.

Definition newton_sparse_term_relation
    (values : Vector.t nat 13) (out : nat) : Prop :=
  out = encoded_newton_sparse_term values.

Theorem newton_sparse_term_relation_murec :
  MuRec_computable newton_sparse_term_relation.
Proof.
  unfold newton_sparse_term_relation.
  refine (@recalg_graph_murec 13 encoded_newton_sparse_term
    ra_newton_sparse_term _).
  exact ra_newton_sparse_term_correct.
Qed.

Theorem decode_encoded_newton_sparse_term values :
  zigzag_decode (encoded_newton_sparse_term values) =
  eval_recursive_signed_expression
    newton_sparse_term_signed_expression values.
Proof.
  unfold encoded_newton_sparse_term, newton_sparse_term_code_expression.
  exact: zigzag_decode_recursive_signed_code.
Qed.

(* --------------------------------------------------------------------- *)
(* Pair-descriptor terms and the compact ordered collision product.      *)

Definition recursive_signed_one {arity} :
    recursive_signed_expression arity := recursive_signed_nat 1.

Definition recursive_signed_if_zero {arity}
    (test : recursive_expression arity)
    (if_zero if_nonzero : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  {| recursive_positive :=
       RecIfZero test (recursive_positive if_zero)
         (recursive_positive if_nonzero);
     recursive_negative :=
       RecIfZero test (recursive_negative if_zero)
         (recursive_negative if_nonzero) |}.

Definition recursive_equal_distance {arity}
    (left right : recursive_expression arity) :
    recursive_expression arity :=
  RecPlus (RecMinus left right) (RecMinus right left).

Definition recursive_equal_indicator {arity}
    (left right : recursive_expression arity) :
    recursive_expression arity :=
  RecIfZero (recursive_equal_distance left right) (RecConst 1) (RecConst 0).

Definition recursive_inject9 {arity}
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : recursive_expression arity) :
    recursive_expression arity :=
  RecRecomp a0
    (RecRecomp a1
      (RecRecomp a2
        (RecRecomp a3
          (RecRecomp a4
            (RecRecomp a5
              (RecRecomp a6
                (RecRecomp a7 (RecRecomp a8 (RecConst 0))))))))).

Definition recursive_project9 {arity} (index : pos 9)
    (code : recursive_expression arity) : recursive_expression arity :=
  recursive_project index code.

Definition pair_member_table
    (block : 'I_3) (slot : 'I_2) : list nat :=
  List.map
    (fun partition =>
      val
        (PolynomialFormulasSexticSparseResolvents.pair_member
          partition block slot))
    (enum PolynomialFormulasSexticSparseResolvents.pair_partition).

Definition recursive_pair_member {arity}
    (partition : recursive_expression arity)
    (block : 'I_3) (slot : 'I_2) : recursive_expression arity :=
  recursive_lookup_list (pair_member_table block slot) partition.

Definition pair_outer_digit {arity}
    (term_index : recursive_expression arity) (block : nat) :
    recursive_expression arity :=
  RecRemSucc
    (RecDivSucc term_index (Nat.pred (Nat.pow 5 block))) 4.

Definition pair_inner_bit {arity}
    (outer_digit : recursive_expression arity) (slot : nat) :
    recursive_expression arity :=
  RecRemSucc
    (RecDivSucc (RecMinus outer_digit (RecConst 1))
      (Nat.pred (Nat.pow 2 slot))) 1.

Definition pair_block_coefficient_from {arity}
    (term_index x0 x1 : recursive_expression arity) (block : nat) :
    recursive_signed_expression arity :=
  let digit := pair_outer_digit term_index block in
  let bit0 := pair_inner_bit digit 0 in
  let bit1 := pair_inner_bit digit 1 in
  recursive_signed_if_zero digit (recursive_signed_of_nat x0)
    (recursive_signed_mult
      (recursive_signed_negate recursive_signed_one)
      (recursive_signed_mult
        (recursive_signed_if_zero bit0 (recursive_signed_of_nat x1)
          (recursive_signed_negate recursive_signed_one))
        (recursive_signed_if_zero bit1 (recursive_signed_of_nat x1)
          (recursive_signed_negate recursive_signed_one)))).

Definition pair_descriptor_coefficient_from {arity}
    (term_index x0 x1 : recursive_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_mult
    (pair_block_coefficient_from term_index x0 x1 0)
    (recursive_signed_mult
      (pair_block_coefficient_from term_index x0 x1 1)
      (pair_block_coefficient_from term_index x0 x1 2)).

Definition pair_selected_root_indicator_from {arity}
    (partition term_index : recursive_expression arity)
    (coordinate : nat) (block : 'I_3) (slot : 'I_2) :
    recursive_expression arity :=
  let digit := pair_outer_digit term_index (val block) in
  let bit := pair_inner_bit digit (val slot) in
  RecMult (RecIfZero digit (RecConst 0) (RecConst 1))
    (RecMult bit
      (recursive_equal_indicator
        (recursive_pair_member partition block slot)
        (RecConst coordinate))).

Definition pair_descriptor_exponent_from {arity}
    (partition term_index : recursive_expression arity)
    (coordinate : nat) : recursive_expression arity :=
  RecPlus
    (pair_selected_root_indicator_from partition term_index coordinate
      ord0 ord0)
    (RecPlus
      (pair_selected_root_indicator_from partition term_index coordinate
        ord0 ord_max)
      (RecPlus
        (pair_selected_root_indicator_from partition term_index coordinate
          (@Ordinal 3 1 isT) ord0)
        (RecPlus
          (pair_selected_root_indicator_from partition term_index coordinate
            (@Ordinal 3 1 isT) ord_max)
          (RecPlus
            (pair_selected_root_indicator_from partition term_index coordinate
              ord_max ord0)
            (pair_selected_root_indicator_from partition term_index coordinate
              ord_max ord_max))))).

Definition pair_collision_factor_coefficient_from {arity}
    (left_partition right_partition digit x0 x1 :
      recursive_expression arity) : recursive_signed_expression arity :=
  let right_branch :=
    recursive_signed_negate
      (pair_descriptor_coefficient_from
        (RecMinus digit (RecConst 125)) x0 x1) in
  let left_branch := pair_descriptor_coefficient_from digit x0 x1 in
  recursive_signed_if_zero (RecMinus (RecConst 125) digit)
    right_branch left_branch.

Definition pair_collision_factor_exponent_from {arity}
    (left_partition right_partition digit : recursive_expression arity)
    (coordinate : nat) : recursive_expression arity :=
  RecIfZero (RecMinus (RecConst 125) digit)
    (pair_descriptor_exponent_from right_partition
      (RecMinus digit (RecConst 125)) coordinate)
    (pair_descriptor_exponent_from left_partition digit coordinate).

Definition pair_collision_state_step_from {arity}
    (state x0 x1 : recursive_expression arity) :
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
  let left_partition := RecDivSucc factor 14 in
  let right_partition := RecRemSucc factor 14 in
  let digit := RecRemSucc remaining 249 in
  let next_remaining := RecDivSucc remaining 249 in
  let factor_coefficient :=
    pair_collision_factor_coefficient_from left_partition right_partition
      digit x0 x1 in
  let next_coefficient :=
    recursive_signed_code
      (recursive_signed_mult (recursive_signed_decode coefficient_code)
        factor_coefficient) in
  let next_exponent coordinate previous :=
    RecPlus previous
      (pair_collision_factor_exponent_from left_partition right_partition
        digit coordinate) in
  let diagonal_state :=
    recursive_inject9 (RecSucc factor) remaining coefficient_code
      exponent0 exponent1 exponent2 exponent3 exponent4 exponent5 in
  let off_diagonal_state :=
    recursive_inject9 (RecSucc factor) next_remaining next_coefficient
      (next_exponent 0 exponent0) (next_exponent 1 exponent1)
      (next_exponent 2 exponent2) (next_exponent 3 exponent3)
      (next_exponent 4 exponent4) (next_exponent 5 exponent5) in
  RecIfZero (recursive_equal_distance left_partition right_partition)
    diagonal_state off_diagonal_state.

Definition pair_collision_term_state_from {arity}
    (term_index x0 x1 : recursive_expression arity) :
    recursive_expression arity :=
  RecIter (RecConst 225)
    (recursive_inject9 (RecConst 0) term_index
      (recursive_signed_code recursive_signed_one)
      (RecConst 0) (RecConst 0) (RecConst 0)
      (RecConst 0) (RecConst 0) (RecConst 0))
    (pair_collision_state_step_from (RecVar pos0)
      (recursive_weaken x0) (recursive_weaken x1)).

Definition pair_collision_term_count_from {arity} :
    recursive_expression arity :=
  RecIter (RecConst 210) (RecConst 1)
    (RecMult (RecVar pos0) (RecConst 250)).

Definition pair_collision_term_code_from {arity}
    (term_index x0 x1 : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_expression arity :=
  RecIter (RecConst 1)
    (pair_collision_term_state_from term_index x0 x1)
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

(** Inputs are zigzag codes [f0,...,f5] followed by the two natural
    descriptor parameters [x0,x1]. *)
Definition pair_scaled_collision_signed_expression :
    recursive_signed_expression 8 :=
  recursive_signed_bounded_sum pair_collision_term_count_from
    (recursive_signed_decode
      (pair_collision_term_code_from (RecVar pos0)
        (RecVar pos7) (RecVar pos8)
        (recursive_signed_negate (recursive_signed_input pos6))
        (recursive_signed_input pos5)
        (recursive_signed_negate (recursive_signed_input pos4))
        (recursive_signed_input pos3)
        (recursive_signed_negate (recursive_signed_input pos2))
        (recursive_signed_input pos1))).

Definition pair_scaled_collision_code_expression :
    recursive_expression 8 :=
  recursive_signed_code pair_scaled_collision_signed_expression.

Definition encoded_pair_scaled_collision_value
    (values : Vector.t nat 8) : nat :=
  eval_recursive_expression pair_scaled_collision_code_expression values.

Definition ra_pair_scaled_collision_value : recalg 8 :=
  compile_recursive_expression pair_scaled_collision_code_expression.

Theorem ra_pair_scaled_collision_value_correct values :
  ⟦ra_pair_scaled_collision_value⟧ values
    (encoded_pair_scaled_collision_value values).
Proof. exact: compile_recursive_expression_correct. Qed.

Theorem ra_pair_scaled_collision_value_primitive_recursive :
  prim_rec ra_pair_scaled_collision_value.
Proof. exact: compile_recursive_expression_primitive_recursive. Qed.

Definition encoded_pair_collision_test (values : Vector.t nat 8) : nat :=
  ite_rel (encoded_pair_scaled_collision_value values) 0 1.

Definition pair_collision_test_expression : recursive_expression 8 :=
  RecIfZero pair_scaled_collision_code_expression
    (RecConst 0) (RecConst 1).

Definition ra_pair_collision_test : recalg 8 :=
  ra_comp ra_ite
    (ra_pair_scaled_collision_value ##
     ra_cst_n 8 0 ## ra_cst_n 8 1 ## vec_nil).

Theorem ra_pair_collision_test_correct values :
  ⟦ra_pair_collision_test⟧ values (encoded_pair_collision_test values).
Proof.
  unfold ra_pair_collision_test, encoded_pair_collision_test.
  eapply ra_comp3_val.
  - exact: ra_pair_scaled_collision_value_correct.
  - exact: ra_cst_n_val.
  - exact: ra_cst_n_val.
  - exact: ra_ite_val.
Qed.

Theorem ra_pair_collision_test_primitive_recursive :
  prim_rec ra_pair_collision_test.
Proof.
  unfold ra_pair_collision_test.
  change
    (prim_rec ra_ite /\
      forall variable,
        prim_rec
          (vec_pos
            (ra_pair_scaled_collision_value ##
             ra_cst_n 8 0 ## ra_cst_n 8 1 ## vec_nil)
            variable)).
  split; [exact ra_ite_prim_rec|].
  intro variable; analyse pos variable; cbn [vec_pos pos_S_inv].
  - exact ra_pair_scaled_collision_value_primitive_recursive.
  - exact (ra_cst_n_prim 8 0).
  - exact (ra_cst_n_prim 8 1).
Qed.

(* The separating-search seam consumes [index ## f0 ## ... ## f5].      *)

Definition pair_projected_collision_arguments
    (index : nat) (values : Vector.t nat 6) : Vector.t nat 8 :=
  vec_pos values pos0 ## vec_pos values pos1 ## vec_pos values pos2 ##
  vec_pos values pos3 ## vec_pos values pos4 ## vec_pos values pos5 ##
  vec_pos (project 2 index) pos0 ##
  vec_pos (project 2 index) pos1 ## vec_nil.

Definition ra_pair_projected_x0 : recalg 7 :=
  ra_comp (@ra_project 2 pos0) (ra_proj pos0 ## vec_nil).

Definition ra_pair_projected_x1 : recalg 7 :=
  ra_comp (@ra_project 2 pos1) (ra_proj pos0 ## vec_nil).

Lemma ra_pair_projected_x0_correct index values :
  ⟦ra_pair_projected_x0⟧ (index ## values)
    (vec_pos (project 2 index) pos0).
Proof.
  unfold ra_pair_projected_x0.
  eapply ra_comp1_val; [exact: ra_proj_val|exact: ra_project_val].
Qed.

Lemma ra_pair_projected_x1_correct index values :
  ⟦ra_pair_projected_x1⟧ (index ## values)
    (vec_pos (project 2 index) pos1).
Proof.
  unfold ra_pair_projected_x1.
  eapply ra_comp1_val; [exact: ra_proj_val|exact: ra_project_val].
Qed.

Definition ra_pair_projected_collision_arguments :
    Vector.t (recalg 7) 8 :=
  ra_proj pos1 ## ra_proj pos2 ## ra_proj pos3 ##
  ra_proj pos4 ## ra_proj pos5 ## ra_proj pos6 ##
  ra_pair_projected_x0 ## ra_pair_projected_x1 ## vec_nil.

Definition ra_pair_projected_collision_test : recalg 7 :=
  ra_comp ra_pair_collision_test ra_pair_projected_collision_arguments.

Theorem ra_pair_projected_collision_test_correct index values :
  ⟦ra_pair_projected_collision_test⟧ (index ## values)
    (encoded_pair_collision_test
      (pair_projected_collision_arguments index values)).
Proof.
  unfold ra_pair_projected_collision_test.
  exists (pair_projected_collision_arguments index values); split.
  - exact: ra_pair_collision_test_correct.
  - intro variable; analyse pos variable;
      cbn [ra_pair_projected_collision_arguments
        pair_projected_collision_arguments vec_pos pos_S_inv].
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_pair_projected_x0_correct.
    + exact: ra_pair_projected_x1_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* Triple-descriptor terms and the compact ordered collision product.    *)

Definition triple_member_table
    (block : 'I_2) (slot : 'I_3) : list nat :=
  List.map
    (fun partition =>
      val
        (PolynomialFormulasSexticSparseResolvents.triple_member
          partition block slot))
    (enum PolynomialFormulasSexticSparseResolvents.triple_partition).

Definition recursive_triple_member {arity}
    (partition : recursive_expression arity)
    (block : 'I_2) (slot : 'I_3) : recursive_expression arity :=
  recursive_lookup_list (triple_member_table block slot) partition.

Definition triple_outer_digit {arity}
    (term_index : recursive_expression arity) (block : nat) :
    recursive_expression arity :=
  RecRemSucc
    (RecDivSucc term_index (Nat.pred (Nat.pow 9 block))) 8.

Definition triple_inner_bit {arity}
    (outer_digit : recursive_expression arity) (slot : nat) :
    recursive_expression arity :=
  RecRemSucc
    (RecDivSucc (RecMinus outer_digit (RecConst 1))
      (Nat.pred (Nat.pow 2 slot))) 1.

Definition triple_block_coefficient_from {arity}
    (term_index x0 x1 : recursive_expression arity) (block : nat) :
    recursive_signed_expression arity :=
  let digit := triple_outer_digit term_index block in
  let bit0 := triple_inner_bit digit 0 in
  let bit1 := triple_inner_bit digit 1 in
  let bit2 := triple_inner_bit digit 2 in
  recursive_signed_if_zero digit (recursive_signed_of_nat x0)
    (recursive_signed_mult
      (recursive_signed_negate recursive_signed_one)
      (recursive_signed_mult
        (recursive_signed_if_zero bit0 (recursive_signed_of_nat x1)
          (recursive_signed_negate recursive_signed_one))
        (recursive_signed_mult
          (recursive_signed_if_zero bit1 (recursive_signed_of_nat x1)
            (recursive_signed_negate recursive_signed_one))
          (recursive_signed_if_zero bit2 (recursive_signed_of_nat x1)
            (recursive_signed_negate recursive_signed_one))))).

Definition triple_descriptor_coefficient_from {arity}
    (term_index x0 x1 : recursive_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_mult
    (triple_block_coefficient_from term_index x0 x1 0)
    (triple_block_coefficient_from term_index x0 x1 1).

Definition triple_selected_root_indicator_from {arity}
    (partition term_index : recursive_expression arity)
    (coordinate : nat) (block : 'I_2) (slot : 'I_3) :
    recursive_expression arity :=
  let digit := triple_outer_digit term_index (val block) in
  let bit := triple_inner_bit digit (val slot) in
  RecMult (RecIfZero digit (RecConst 0) (RecConst 1))
    (RecMult bit
      (recursive_equal_indicator
        (recursive_triple_member partition block slot)
        (RecConst coordinate))).

Definition triple_descriptor_exponent_from {arity}
    (partition term_index : recursive_expression arity)
    (coordinate : nat) : recursive_expression arity :=
  RecPlus
    (triple_selected_root_indicator_from partition term_index coordinate
      ord0 ord0)
    (RecPlus
      (triple_selected_root_indicator_from partition term_index coordinate
        ord0 (@Ordinal 3 1 isT))
      (RecPlus
        (triple_selected_root_indicator_from partition term_index coordinate
          ord0 ord_max)
        (RecPlus
          (triple_selected_root_indicator_from partition term_index coordinate
            ord_max ord0)
          (RecPlus
            (triple_selected_root_indicator_from partition term_index coordinate
              ord_max (@Ordinal 3 1 isT))
            (triple_selected_root_indicator_from partition term_index coordinate
              ord_max ord_max))))).

Definition triple_collision_factor_coefficient_from {arity}
    (left_partition right_partition digit x0 x1 :
      recursive_expression arity) : recursive_signed_expression arity :=
  let right_branch :=
    recursive_signed_negate
      (triple_descriptor_coefficient_from
        (RecMinus digit (RecConst 81)) x0 x1) in
  let left_branch := triple_descriptor_coefficient_from digit x0 x1 in
  recursive_signed_if_zero (RecMinus (RecConst 81) digit)
    right_branch left_branch.

Definition triple_collision_factor_exponent_from {arity}
    (left_partition right_partition digit : recursive_expression arity)
    (coordinate : nat) : recursive_expression arity :=
  RecIfZero (RecMinus (RecConst 81) digit)
    (triple_descriptor_exponent_from right_partition
      (RecMinus digit (RecConst 81)) coordinate)
    (triple_descriptor_exponent_from left_partition digit coordinate).

Definition triple_collision_state_step_from {arity}
    (state x0 x1 : recursive_expression arity) :
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
  let left_partition := RecDivSucc factor 9 in
  let right_partition := RecRemSucc factor 9 in
  let digit := RecRemSucc remaining 161 in
  let next_remaining := RecDivSucc remaining 161 in
  let factor_coefficient :=
    triple_collision_factor_coefficient_from left_partition right_partition
      digit x0 x1 in
  let next_coefficient :=
    recursive_signed_code
      (recursive_signed_mult (recursive_signed_decode coefficient_code)
        factor_coefficient) in
  let next_exponent coordinate previous :=
    RecPlus previous
      (triple_collision_factor_exponent_from left_partition right_partition
        digit coordinate) in
  let diagonal_state :=
    recursive_inject9 (RecSucc factor) remaining coefficient_code
      exponent0 exponent1 exponent2 exponent3 exponent4 exponent5 in
  let off_diagonal_state :=
    recursive_inject9 (RecSucc factor) next_remaining next_coefficient
      (next_exponent 0 exponent0) (next_exponent 1 exponent1)
      (next_exponent 2 exponent2) (next_exponent 3 exponent3)
      (next_exponent 4 exponent4) (next_exponent 5 exponent5) in
  RecIfZero (recursive_equal_distance left_partition right_partition)
    diagonal_state off_diagonal_state.

Definition triple_collision_term_state_from {arity}
    (term_index x0 x1 : recursive_expression arity) :
    recursive_expression arity :=
  RecIter (RecConst 100)
    (recursive_inject9 (RecConst 0) term_index
      (recursive_signed_code recursive_signed_one)
      (RecConst 0) (RecConst 0) (RecConst 0)
      (RecConst 0) (RecConst 0) (RecConst 0))
    (triple_collision_state_step_from (RecVar pos0)
      (recursive_weaken x0) (recursive_weaken x1)).

Definition triple_collision_term_count_from {arity} :
    recursive_expression arity :=
  RecIter (RecConst 90) (RecConst 1)
    (RecMult (RecVar pos0) (RecConst 162)).

Definition triple_collision_term_code_from {arity}
    (term_index x0 x1 : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_expression arity :=
  RecIter (RecConst 1)
    (triple_collision_term_state_from term_index x0 x1)
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

(** Inputs are zigzag codes [f0,...,f5] followed by the two natural
    descriptor parameters [x0,x1]. *)
Definition triple_scaled_collision_signed_expression :
    recursive_signed_expression 8 :=
  recursive_signed_bounded_sum triple_collision_term_count_from
    (recursive_signed_decode
      (triple_collision_term_code_from (RecVar pos0)
        (RecVar pos7) (RecVar pos8)
        (recursive_signed_negate (recursive_signed_input pos6))
        (recursive_signed_input pos5)
        (recursive_signed_negate (recursive_signed_input pos4))
        (recursive_signed_input pos3)
        (recursive_signed_negate (recursive_signed_input pos2))
        (recursive_signed_input pos1))).

Definition triple_scaled_collision_code_expression :
    recursive_expression 8 :=
  recursive_signed_code triple_scaled_collision_signed_expression.

Definition encoded_triple_scaled_collision_value
    (values : Vector.t nat 8) : nat :=
  eval_recursive_expression triple_scaled_collision_code_expression values.

Definition ra_triple_scaled_collision_value : recalg 8 :=
  compile_recursive_expression triple_scaled_collision_code_expression.

Theorem ra_triple_scaled_collision_value_correct values :
  ⟦ra_triple_scaled_collision_value⟧ values
    (encoded_triple_scaled_collision_value values).
Proof. exact: compile_recursive_expression_correct. Qed.

Theorem ra_triple_scaled_collision_value_primitive_recursive :
  prim_rec ra_triple_scaled_collision_value.
Proof. exact: compile_recursive_expression_primitive_recursive. Qed.

Definition encoded_triple_collision_test (values : Vector.t nat 8) : nat :=
  ite_rel (encoded_triple_scaled_collision_value values) 0 1.

Definition triple_collision_test_expression : recursive_expression 8 :=
  RecIfZero triple_scaled_collision_code_expression
    (RecConst 0) (RecConst 1).

Definition ra_triple_collision_test : recalg 8 :=
  ra_comp ra_ite
    (ra_triple_scaled_collision_value ##
     ra_cst_n 8 0 ## ra_cst_n 8 1 ## vec_nil).

Theorem ra_triple_collision_test_correct values :
  ⟦ra_triple_collision_test⟧ values (encoded_triple_collision_test values).
Proof.
  unfold ra_triple_collision_test, encoded_triple_collision_test.
  eapply ra_comp3_val.
  - exact: ra_triple_scaled_collision_value_correct.
  - exact: ra_cst_n_val.
  - exact: ra_cst_n_val.
  - exact: ra_ite_val.
Qed.

Theorem ra_triple_collision_test_primitive_recursive :
  prim_rec ra_triple_collision_test.
Proof.
  unfold ra_triple_collision_test.
  change
    (prim_rec ra_ite /\
      forall variable,
        prim_rec
          (vec_pos
            (ra_triple_scaled_collision_value ##
             ra_cst_n 8 0 ## ra_cst_n 8 1 ## vec_nil)
            variable)).
  split; [exact ra_ite_prim_rec|].
  intro variable; analyse pos variable; cbn [vec_pos pos_S_inv].
  - exact ra_triple_scaled_collision_value_primitive_recursive.
  - exact (ra_cst_n_prim 8 0).
  - exact (ra_cst_n_prim 8 1).
Qed.

Definition triple_projected_collision_arguments :=
  pair_projected_collision_arguments.

Definition ra_triple_projected_collision_test : recalg 7 :=
  ra_comp ra_triple_collision_test ra_pair_projected_collision_arguments.

Theorem ra_triple_projected_collision_test_correct index values :
  ⟦ra_triple_projected_collision_test⟧ (index ## values)
    (encoded_triple_collision_test
      (triple_projected_collision_arguments index values)).
Proof.
  unfold ra_triple_projected_collision_test,
    triple_projected_collision_arguments.
  exists (pair_projected_collision_arguments index values); split.
  - exact: ra_triple_collision_test_correct.
  - intro variable; analyse pos variable;
      cbn [ra_pair_projected_collision_arguments
        pair_projected_collision_arguments vec_pos pos_S_inv].
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_proj_val.
    + exact: ra_pair_projected_x0_correct.
    + exact: ra_pair_projected_x1_correct.
Qed.

Print Assumptions ra_newton_sparse_term_correct.
Print Assumptions newton_sparse_term_relation_murec.
Print Assumptions decode_encoded_newton_sparse_term.
Print Assumptions ra_pair_scaled_collision_value_correct.
Print Assumptions ra_pair_collision_test_correct.
Print Assumptions ra_pair_projected_collision_test_correct.
Print Assumptions ra_triple_scaled_collision_value_correct.
Print Assumptions ra_triple_collision_test_correct.
Print Assumptions ra_triple_projected_collision_test_correct.

End PolynomialFormulasSexticMuRecCollisionEvaluator.
