(* ===================================================================== *)
(*  Compact Mu-recursive evaluation of the sparse Newton constructions.  *)
(*                                                                       *)
(*  The computed resolvents are intentionally represented by compact     *)
(*  sparse syntax.  Expanding a collision product before compiling it     *)
(*  would make the certificate enormous.  This file therefore starts     *)
(*  with a small certified expression language containing bounded sums,   *)
(*  primitive iteration, and the concrete pairing operations used for     *)
(*  encoded finite state.                                                  *)
(* ===================================================================== *)

From Stdlib Require Import Arith Lia List Vector ZArith.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.

From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From mathcomp Require Import all_ssreflect all_algebra.
From Abel Require Import abel.

From PolynomialFormulas Require Import SexticMuRecComputability
  SexticRecursiveCore SexticSparsePolynomials SexticSparseResolvents
  SexticPowerSumSymmetric SexticNewtonPowerSums SexticComputedResolvents
  SexticSeparatingSearch QuinticRecursiveFactor
  QuinticPaddedSymmetrization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Module PolynomialFormulasSexticMuRecSparseEvaluator.

(* --------------------------------------------------------------------- *)
(* A compact expression language with genuine primitive iteration.       *)

Inductive recursive_expression (arity : nat) : Type :=
  | RecConst : nat -> recursive_expression arity
  | RecVar : pos arity -> recursive_expression arity
  | RecSucc : recursive_expression arity -> recursive_expression arity
  | RecPlus : recursive_expression arity -> recursive_expression arity ->
      recursive_expression arity
  | RecMinus : recursive_expression arity -> recursive_expression arity ->
      recursive_expression arity
  | RecMult : recursive_expression arity -> recursive_expression arity ->
      recursive_expression arity
  | RecDivSucc : recursive_expression arity -> nat ->
      recursive_expression arity
  | RecRemSucc : recursive_expression arity -> nat ->
      recursive_expression arity
  | RecIfZero : recursive_expression arity -> recursive_expression arity ->
      recursive_expression arity -> recursive_expression arity
  | RecDecompL : recursive_expression arity -> recursive_expression arity
  | RecDecompR : recursive_expression arity -> recursive_expression arity
  | RecRecomp : recursive_expression arity -> recursive_expression arity ->
      recursive_expression arity
  | RecBoundedSum : recursive_expression arity ->
      recursive_expression (S arity) -> recursive_expression arity
  | RecIter : recursive_expression arity -> recursive_expression arity ->
      recursive_expression (S arity) -> recursive_expression arity.

Arguments RecConst {arity} _.
Arguments RecVar {arity} _.
Arguments RecSucc {arity} _.
Arguments RecPlus {arity} _ _.
Arguments RecMinus {arity} _ _.
Arguments RecMult {arity} _ _.
Arguments RecDivSucc {arity} _ _.
Arguments RecRemSucc {arity} _ _.
Arguments RecIfZero {arity} _ _ _.
Arguments RecDecompL {arity} _.
Arguments RecDecompR {arity} _.
Arguments RecRecomp {arity} _ _.
Arguments RecBoundedSum {arity} _ _.
Arguments RecIter {arity} _ _ _.

Fixpoint eval_recursive_expression {arity}
    (expression : recursive_expression arity)
    (values : Vector.t nat arity) : nat :=
  match expression with
  | RecConst constant => constant
  | RecVar variable => vec_pos values variable
  | RecSucc inner => S (eval_recursive_expression inner values)
  | RecPlus lhs rhs =>
      eval_recursive_expression lhs values +
      eval_recursive_expression rhs values
  | RecMinus lhs rhs =>
      eval_recursive_expression lhs values -
      eval_recursive_expression rhs values
  | RecMult lhs rhs =>
      eval_recursive_expression lhs values *
      eval_recursive_expression rhs values
  | RecDivSucc dividend divisor =>
      gcd.div (eval_recursive_expression dividend values) (S divisor)
  | RecRemSucc dividend divisor =>
      gcd.rem (eval_recursive_expression dividend values) (S divisor)
  | RecIfZero test if_zero if_nonzero =>
      ite_rel (eval_recursive_expression test values)
        (eval_recursive_expression if_zero values)
        (eval_recursive_expression if_nonzero values)
  | RecDecompL code =>
      decomp_l (eval_recursive_expression code values)
  | RecDecompR code =>
      decomp_r (eval_recursive_expression code values)
  | RecRecomp lhs rhs =>
      recomp (eval_recursive_expression lhs values)
        (eval_recursive_expression rhs values)
  | RecBoundedSum upper body =>
      lsum
        (List.map
          (fun index => eval_recursive_expression body (index ## values))
          (list_an 0 (eval_recursive_expression upper values)))
  | RecIter count initial step =>
      prim_min.iter
        (fun state => eval_recursive_expression step (state ## values))
        (eval_recursive_expression count values)
        (eval_recursive_expression initial values)
  end.

Definition recursive_identity_arguments arity :
    Vector.t (recalg arity) arity :=
  vec_set_pos (fun variable => ra_proj variable).

Fixpoint compile_recursive_expression {arity}
    (expression : recursive_expression arity) : recalg arity :=
  match expression with
  | RecConst constant => ra_cst_n arity constant
  | RecVar variable => ra_proj variable
  | RecSucc inner =>
      ra_comp ra_succ (compile_recursive_expression inner ## vec_nil)
  | RecPlus lhs rhs =>
      ra_comp ra_plus
        (compile_recursive_expression lhs ##
         compile_recursive_expression rhs ## vec_nil)
  | RecMinus lhs rhs =>
      ra_comp ra_minus
        (compile_recursive_expression lhs ##
         compile_recursive_expression rhs ## vec_nil)
  | RecMult lhs rhs =>
      ra_comp ra_mult
        (compile_recursive_expression lhs ##
         compile_recursive_expression rhs ## vec_nil)
  | RecDivSucc dividend divisor =>
      ra_comp ra_div
        (compile_recursive_expression dividend ##
         ra_cst_n arity (S divisor) ## vec_nil)
  | RecRemSucc dividend divisor =>
      ra_comp ra_rem
        (compile_recursive_expression dividend ##
         ra_cst_n arity (S divisor) ## vec_nil)
  | RecIfZero test if_zero if_nonzero =>
      ra_comp ra_ite
        (compile_recursive_expression test ##
         compile_recursive_expression if_zero ##
         compile_recursive_expression if_nonzero ## vec_nil)
  | RecDecompL code =>
      ra_comp ra_decomp_l
        (compile_recursive_expression code ## vec_nil)
  | RecDecompR code =>
      ra_comp ra_decomp_r
        (compile_recursive_expression code ## vec_nil)
  | RecRecomp lhs rhs =>
      ra_comp ra_recomp
        (compile_recursive_expression lhs ##
         compile_recursive_expression rhs ## vec_nil)
  | RecBoundedSum upper body =>
      ra_comp (ra_lsum (compile_recursive_expression body))
        (compile_recursive_expression upper ##
         recursive_identity_arguments arity)
  | RecIter count initial step =>
      ra_comp
        (ra_iter_n (compile_recursive_expression initial)
          (compile_recursive_expression step))
        (compile_recursive_expression count ##
         recursive_identity_arguments arity)
  end.

Theorem compile_recursive_expression_correct {arity}
    (expression : recursive_expression arity) values :
  ⟦compile_recursive_expression expression⟧ values
    (eval_recursive_expression expression values).
Proof.
  induction expression; cbn [compile_recursive_expression
    eval_recursive_expression].
  - apply ra_cst_n_val.
  - apply ra_proj_val.
  - eapply ra_comp1_val; [apply IHexpression|reflexivity].
  - eapply ra_comp2_val; [apply IHexpression1|apply IHexpression2|].
    apply ra_plus_val.
  - eapply ra_comp2_val; [apply IHexpression1|apply IHexpression2|].
    apply ra_minus_val.
  - eapply ra_comp2_val; [apply IHexpression1|apply IHexpression2|].
    apply ra_mult_val.
  - eapply ra_comp2_val.
    + apply IHexpression.
    + apply ra_cst_n_val.
    + apply ra_div_val. lia.
  - eapply ra_comp2_val.
    + apply IHexpression.
    + apply ra_cst_n_val.
    + apply ra_rem_val. lia.
  - eapply ra_comp3_val.
    + apply IHexpression1.
    + apply IHexpression2.
    + apply IHexpression3.
    + apply ra_ite_val.
  - eapply ra_comp1_val; [apply IHexpression|apply ra_decomp_l_val].
  - eapply ra_comp1_val; [apply IHexpression|apply ra_decomp_r_val].
  - eapply ra_comp2_val; [apply IHexpression1|apply IHexpression2|].
    apply ra_recomp_val.
  - exists (eval_recursive_expression expression1 values ## values).
    split.
    + apply ra_lsum_spec.
      induction (list_an 0 (eval_recursive_expression expression1 values))
        as [|index indices IHindices]; cbn.
      * constructor.
      * constructor; [apply IHexpression2|exact IHindices].
    + intro variable; analyse pos variable; cbn.
      * apply IHexpression1.
      * unfold recursive_identity_arguments.
        repeat rewrite vec_pos_set.
        apply ra_proj_val.
  - exists (eval_recursive_expression expression1 values ## values).
    split.
    + exact
        (@ra_iter_n_val arity
          (fun tail_values =>
            eval_recursive_expression expression2 tail_values)
          (compile_recursive_expression expression2)
          IHexpression2
          (fun tail_values state =>
            eval_recursive_expression expression3
              (state ## tail_values))
          (compile_recursive_expression expression3)
          (fun state tail_values =>
            IHexpression3 (state ## tail_values))
          (eval_recursive_expression expression1 values) values).
    + intro variable; analyse pos variable; cbn.
      * apply IHexpression1.
      * unfold recursive_identity_arguments.
        repeat rewrite vec_pos_set.
        apply ra_proj_val.
Qed.

Theorem compile_recursive_expression_primitive_recursive {arity}
    (expression : recursive_expression arity) :
  prim_rec (compile_recursive_expression expression).
Proof.
  induction expression; cbn [compile_recursive_expression]; ra prim rec.
  - unfold recursive_identity_arguments.
    rewrite vec_pos_set. exact I.
  - unfold recursive_identity_arguments.
    rewrite vec_pos_set. exact I.
Qed.

(* --------------------------------------------------------------------- *)
(* Canonical zigzag normalization and six-component encoded state.       *)

Record recursive_signed_expression (arity : nat) : Type := {
  recursive_positive : recursive_expression arity;
  recursive_negative : recursive_expression arity
}.

Arguments recursive_positive {arity} _.
Arguments recursive_negative {arity} _.

Definition eval_recursive_signed_expression {arity}
    (expression : recursive_signed_expression arity) values : Z :=
  Z.sub
    (Z.of_nat
      (eval_recursive_expression (recursive_positive expression) values))
    (Z.of_nat
      (eval_recursive_expression (recursive_negative expression) values)).

Definition recursive_signed_zero {arity} :
    recursive_signed_expression arity :=
  {| recursive_positive := RecConst 0;
     recursive_negative := RecConst 0 |}.

Definition recursive_signed_of_nat {arity}
    (expression : recursive_expression arity) :
    recursive_signed_expression arity :=
  {| recursive_positive := expression;
     recursive_negative := RecConst 0 |}.

Definition recursive_signed_decode {arity}
    (code : recursive_expression arity) :
    recursive_signed_expression arity :=
  {| recursive_positive :=
       RecIfZero (RecRemSucc code 1)
         (RecDivSucc code 1) (RecConst 0);
     recursive_negative :=
       RecIfZero (RecRemSucc code 1)
         (RecConst 0) (RecSucc (RecDivSucc code 1)) |}.

Definition recursive_signed_input {arity} (variable : pos arity) :
    recursive_signed_expression arity :=
  recursive_signed_decode (RecVar variable).

Definition recursive_signed_plus {arity}
    (left right : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  {| recursive_positive :=
       RecPlus (recursive_positive left) (recursive_positive right);
     recursive_negative :=
       RecPlus (recursive_negative left) (recursive_negative right) |}.

Definition recursive_signed_negate {arity}
    (expression : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  {| recursive_positive := recursive_negative expression;
     recursive_negative := recursive_positive expression |}.

Definition recursive_signed_minus {arity}
    (left right : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_plus left (recursive_signed_negate right).

Definition recursive_signed_mult {arity}
    (left right : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  {| recursive_positive :=
       RecPlus
         (RecMult (recursive_positive left) (recursive_positive right))
         (RecMult (recursive_negative left) (recursive_negative right));
     recursive_negative :=
       RecPlus
         (RecMult (recursive_positive left) (recursive_negative right))
         (RecMult (recursive_negative left) (recursive_positive right)) |}.

Definition recursive_signed_code {arity}
    (expression : recursive_signed_expression arity) :
    recursive_expression arity :=
  let positive := recursive_positive expression in
  let negative := recursive_negative expression in
  let positive_difference := RecMinus positive negative in
  let negative_difference := RecMinus negative positive in
  RecIfZero negative_difference
    (RecMult (RecConst 2) positive_difference)
    (RecSucc
      (RecMult (RecConst 2) (RecMinus negative_difference (RecConst 1)))).

Definition signed_normalize (positive negative : nat) : nat :=
  ite_rel (Nat.sub negative positive)
    (Nat.mul 2 (Nat.sub positive negative))
    (S (Nat.mul 2 (Nat.sub (Nat.sub negative positive) 1))).

Lemma eval_recursive_signed_decode {arity}
    (code : recursive_expression arity) values :
  eval_recursive_signed_expression (recursive_signed_decode code) values =
  zigzag_decode (eval_recursive_expression code values).
Proof. reflexivity. Qed.

Lemma eval_recursive_signed_input {arity} (variable : pos arity) values :
  eval_recursive_signed_expression (recursive_signed_input variable) values =
  zigzag_decode (vec_pos values variable).
Proof. reflexivity. Qed.

Lemma eval_recursive_signed_plus {arity}
    (left right : recursive_signed_expression arity) values :
  eval_recursive_signed_expression (recursive_signed_plus left right) values =
  Z.add (eval_recursive_signed_expression left values)
    (eval_recursive_signed_expression right values).
Proof.
  unfold eval_recursive_signed_expression, recursive_signed_plus; cbn.
  repeat rewrite Nat2Z.inj_add. lia.
Qed.

Lemma eval_recursive_signed_negate {arity}
    (expression : recursive_signed_expression arity) values :
  eval_recursive_signed_expression (recursive_signed_negate expression)
      values =
  Z.opp (eval_recursive_signed_expression expression values).
Proof.
  unfold eval_recursive_signed_expression, recursive_signed_negate; cbn.
  lia.
Qed.

Lemma eval_recursive_signed_minus {arity}
    (left right : recursive_signed_expression arity) values :
  eval_recursive_signed_expression (recursive_signed_minus left right) values =
  Z.sub (eval_recursive_signed_expression left values)
    (eval_recursive_signed_expression right values).
Proof.
  unfold recursive_signed_minus.
  rewrite eval_recursive_signed_plus eval_recursive_signed_negate.
  lia.
Qed.

Lemma eval_recursive_signed_mult {arity}
    (left right : recursive_signed_expression arity) values :
  eval_recursive_signed_expression (recursive_signed_mult left right) values =
  Z.mul (eval_recursive_signed_expression left values)
    (eval_recursive_signed_expression right values).
Proof.
  unfold eval_recursive_signed_expression, recursive_signed_mult; cbn.
  repeat rewrite Nat2Z.inj_add.
  repeat rewrite Nat2Z.inj_mul.
  ring.
Qed.

Lemma eval_recursive_signed_code {arity}
    (expression : recursive_signed_expression arity) values :
  eval_recursive_expression (recursive_signed_code expression) values =
  signed_normalize
    (eval_recursive_expression (recursive_positive expression) values)
    (eval_recursive_expression (recursive_negative expression) values).
Proof. reflexivity. Qed.

Lemma zigzag_decode_signed_normalize positive negative :
  zigzag_decode (signed_normalize positive negative) =
  Z.sub (Z.of_nat positive) (Z.of_nat negative).
Proof.
  unfold signed_normalize, zigzag_decode, ite_rel.
  destruct (Nat.sub negative positive) as [|difference] eqn:Hdifference.
  - assert (Hle : Nat.le negative positive) by lia.
    rewrite zigzag_positive_even zigzag_negative_even.
    rewrite Nat2Z.inj_sub; last exact Hle.
    lia.
  - replace (Nat.sub (S difference) 1) with difference by lia.
    replace (S (Nat.mul 2 difference))
      with (Nat.add (Nat.mul 2 difference) 1) by lia.
    rewrite zigzag_positive_odd zigzag_negative_odd.
    assert (Hlt : Nat.lt positive negative) by lia.
    pose proof
      (Nat2Z.inj_sub negative positive
        (Nat.lt_le_incl positive negative Hlt)) as Hcast.
    rewrite Hdifference in Hcast.
    lia.
Qed.

Corollary zigzag_decode_recursive_signed_code {arity}
    (expression : recursive_signed_expression arity) values :
  zigzag_decode
      (eval_recursive_expression (recursive_signed_code expression) values) =
  eval_recursive_signed_expression expression values.
Proof.
  rewrite eval_recursive_signed_code zigzag_decode_signed_normalize.
  reflexivity.
Qed.

Definition recursive_inject6 {arity}
    (a0 a1 a2 a3 a4 a5 : recursive_expression arity) :
    recursive_expression arity :=
  RecRecomp a0
    (RecRecomp a1
      (RecRecomp a2
        (RecRecomp a3 (RecRecomp a4 (RecRecomp a5 (RecConst 0)))))).

Fixpoint recursive_project {count arity} (index : pos count)
    (code : recursive_expression arity) : recursive_expression arity :=
  match index with
  | @Fin.F1 _ => RecDecompL code
  | @Fin.FS _ tail => recursive_project tail (RecDecompR code)
  end.

Definition recursive_project6 {arity} (index : pos 6)
    (code : recursive_expression arity) : recursive_expression arity :=
  recursive_project index code.

Lemma eval_recursive_project {count arity} (index : pos count)
    (code : recursive_expression arity) values :
  eval_recursive_expression (recursive_project index code) values =
  vec_pos
    (project count (eval_recursive_expression code values)) index.
Proof.
  revert code.
  induction index; intro code; cbn [recursive_project
    eval_recursive_expression project vec_pos].
  - reflexivity.
  - apply IHindex.
Qed.

Definition encoded_six_state (values : Vector.t nat 6) : nat :=
  inject values.

Lemma eval_recursive_inject6 {arity}
    (a0 a1 a2 a3 a4 a5 : recursive_expression arity) values :
  eval_recursive_expression (recursive_inject6 a0 a1 a2 a3 a4 a5) values =
  inject
    (eval_recursive_expression a0 values ##
     eval_recursive_expression a1 values ##
     eval_recursive_expression a2 values ##
     eval_recursive_expression a3 values ##
     eval_recursive_expression a4 values ##
     eval_recursive_expression a5 values ## vec_nil).
Proof. reflexivity. Qed.

Definition ra_recursive_inject6 {arity}
    (a0 a1 a2 a3 a4 a5 : recursive_expression arity) : recalg arity :=
  compile_recursive_expression (recursive_inject6 a0 a1 a2 a3 a4 a5).

Theorem ra_recursive_inject6_correct {arity}
    (a0 a1 a2 a3 a4 a5 : recursive_expression arity) values :
  ⟦ra_recursive_inject6 a0 a1 a2 a3 a4 a5⟧ values
    (inject
      (eval_recursive_expression a0 values ##
       eval_recursive_expression a1 values ##
       eval_recursive_expression a2 values ##
       eval_recursive_expression a3 values ##
       eval_recursive_expression a4 values ##
       eval_recursive_expression a5 values ## vec_nil)).
Proof.
  unfold ra_recursive_inject6.
  rewrite <- eval_recursive_inject6.
  apply compile_recursive_expression_correct.
Qed.

Theorem ra_recursive_inject6_primitive_recursive {arity}
    (a0 a1 a2 a3 a4 a5 : recursive_expression arity) :
  prim_rec (ra_recursive_inject6 a0 a1 a2 a3 a4 a5).
Proof. apply compile_recursive_expression_primitive_recursive. Qed.

(* A first dynamic Newton milestone: shift a six-value state and append the
   alternating recurrence value
     e1*s6 - e2*s5 + e3*s4 - e4*s3 + e5*s2 - e6*s1.
   [pos0] is the encoded state and [pos1..pos6] are zigzag-coded e1..e6. *)

Definition newton_state_code_from {arity}
    (state : recursive_expression arity) (index : pos 6) :
    recursive_expression arity :=
  recursive_project6 index state.

Definition newton_state_signed_from {arity}
    (state : recursive_expression arity) (index : pos 6) :
    recursive_signed_expression arity :=
  recursive_signed_decode (newton_state_code_from state index).

Definition newton_recurrence_from {arity}
    (state : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_signed_expression arity :=
  recursive_signed_minus
    (recursive_signed_plus
      (recursive_signed_minus
        (recursive_signed_plus
          (recursive_signed_minus
            (recursive_signed_mult e1
              (newton_state_signed_from state pos5))
            (recursive_signed_mult e2
              (newton_state_signed_from state pos4)))
          (recursive_signed_mult e3
            (newton_state_signed_from state pos3)))
        (recursive_signed_mult e4
          (newton_state_signed_from state pos2)))
      (recursive_signed_mult e5
        (newton_state_signed_from state pos1)))
    (recursive_signed_mult e6
      (newton_state_signed_from state pos0)).

Definition newton_step_from {arity}
    (state : recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_expression arity :=
  recursive_inject6
    (newton_state_code_from state pos1)
    (newton_state_code_from state pos2)
    (newton_state_code_from state pos3)
    (newton_state_code_from state pos4)
    (newton_state_code_from state pos5)
    (recursive_signed_code
      (newton_recurrence_from state e1 e2 e3 e4 e5 e6)).

Definition newton_state_code (index : pos 6) : recursive_expression 7 :=
  newton_state_code_from (RecVar pos0) index.

Definition newton_state_signed (index : pos 6) :
    recursive_signed_expression 7 :=
  newton_state_signed_from (RecVar pos0) index.

Definition newton_recurrence_signed : recursive_signed_expression 7 :=
  newton_recurrence_from (RecVar pos0)
    (recursive_signed_input pos1) (recursive_signed_input pos2)
    (recursive_signed_input pos3) (recursive_signed_input pos4)
    (recursive_signed_input pos5) (recursive_signed_input pos6).

Definition encoded_newton_recurrence (values : Vector.t nat 7) : Z :=
  let state := project 6 (vec_pos values pos0) in
  Z.sub
    (Z.add
      (Z.sub
        (Z.add
          (Z.sub
            (Z.mul (zigzag_decode (vec_pos values pos1))
              (zigzag_decode (vec_pos state pos5)))
            (Z.mul (zigzag_decode (vec_pos values pos2))
              (zigzag_decode (vec_pos state pos4))))
          (Z.mul (zigzag_decode (vec_pos values pos3))
            (zigzag_decode (vec_pos state pos3))))
        (Z.mul (zigzag_decode (vec_pos values pos4))
          (zigzag_decode (vec_pos state pos2))))
      (Z.mul (zigzag_decode (vec_pos values pos5))
        (zigzag_decode (vec_pos state pos1))))
    (Z.mul (zigzag_decode (vec_pos values pos6))
      (zigzag_decode (vec_pos state pos0))).

Theorem eval_newton_recurrence_signed values :
  eval_recursive_signed_expression newton_recurrence_signed values =
  encoded_newton_recurrence values.
Proof.
  unfold newton_recurrence_signed, encoded_newton_recurrence,
    newton_recurrence_from, newton_state_signed_from,
    newton_state_code_from, newton_state_signed, newton_state_code.
  repeat first
    [ rewrite eval_recursive_signed_minus
    | rewrite eval_recursive_signed_plus
    | rewrite eval_recursive_signed_mult
    | rewrite eval_recursive_signed_input
    | rewrite eval_recursive_signed_decode
    | rewrite eval_recursive_project ].
  reflexivity.
Qed.

Definition newton_step_expression : recursive_expression 7 :=
  newton_step_from (RecVar pos0)
    (recursive_signed_input pos1) (recursive_signed_input pos2)
    (recursive_signed_input pos3) (recursive_signed_input pos4)
    (recursive_signed_input pos5) (recursive_signed_input pos6).

Definition encoded_newton_step (values : Vector.t nat 7) : nat :=
  let state := project 6 (vec_pos values pos0) in
  inject
    (vec_pos state pos1 ##
     vec_pos state pos2 ##
     vec_pos state pos3 ##
     vec_pos state pos4 ##
     vec_pos state pos5 ##
     signed_normalize
       (eval_recursive_expression
         (recursive_positive newton_recurrence_signed) values)
       (eval_recursive_expression
         (recursive_negative newton_recurrence_signed) values) ## vec_nil).

Lemma eval_newton_step_expression values :
  eval_recursive_expression newton_step_expression values =
  encoded_newton_step values.
Proof.
  unfold newton_step_expression, encoded_newton_step,
    newton_step_from, newton_recurrence_signed,
    newton_recurrence_from, newton_state_code_from, newton_state_code.
  rewrite eval_recursive_inject6 eval_recursive_signed_code.
  repeat rewrite eval_recursive_project.
  reflexivity.
Qed.

Lemma encoded_newton_step_project values :
  project 6 (encoded_newton_step values) =
    let state := project 6 (vec_pos values pos0) in
    vec_pos state pos1 ##
    vec_pos state pos2 ##
    vec_pos state pos3 ##
    vec_pos state pos4 ##
    vec_pos state pos5 ##
    signed_normalize
      (eval_recursive_expression
        (recursive_positive newton_recurrence_signed) values)
      (eval_recursive_expression
        (recursive_negative newton_recurrence_signed) values) ## vec_nil.
Proof. unfold encoded_newton_step; apply project_inject. Qed.

Theorem encoded_newton_step_last_decode values :
  zigzag_decode
      (vec_pos (project 6 (encoded_newton_step values)) pos5) =
  encoded_newton_recurrence values.
Proof.
  rewrite encoded_newton_step_project; cbn [vec_pos].
  rewrite zigzag_decode_signed_normalize.
  exact: eval_newton_recurrence_signed.
Qed.

Definition ra_newton_step : recalg 7 :=
  compile_recursive_expression newton_step_expression.

Theorem ra_newton_step_correct values :
  ⟦ra_newton_step⟧ values (encoded_newton_step values).
Proof.
  unfold ra_newton_step.
  rewrite <- eval_newton_step_expression.
  apply compile_recursive_expression_correct.
Qed.

Theorem ra_newton_step_primitive_recursive : prim_rec ra_newton_step.
Proof. apply compile_recursive_expression_primitive_recursive. Qed.

Theorem encoded_newton_step_murec :
  MuRec_computable
    (fun values out => out = encoded_newton_step values).
Proof.
  refine (@recalg_graph_murec 7 encoded_newton_step ra_newton_step _).
  exact ra_newton_step_correct.
Qed.

(* --------------------------------------------------------------------- *)
(* Six initial Newton powers and the dynamic scalar power program.        *)

Definition recursive_signed_nat {arity} (constant : nat) :
    recursive_signed_expression arity :=
  recursive_signed_of_nat (RecConst constant).

Definition newton_p1_from {arity}
    (e1 : recursive_signed_expression arity) := e1.

Definition newton_p2_from {arity}
    (e1 e2 : recursive_signed_expression arity) :=
  recursive_signed_minus
    (recursive_signed_mult e1 (newton_p1_from e1))
    (recursive_signed_mult (recursive_signed_nat 2) e2).

Definition newton_p3_from {arity}
    (e1 e2 e3 : recursive_signed_expression arity) :=
  recursive_signed_plus
    (recursive_signed_minus
      (recursive_signed_mult e1 (newton_p2_from e1 e2))
      (recursive_signed_mult e2 (newton_p1_from e1)))
    (recursive_signed_mult (recursive_signed_nat 3) e3).

Definition newton_p4_from {arity}
    (e1 e2 e3 e4 : recursive_signed_expression arity) :=
  recursive_signed_minus
    (recursive_signed_plus
      (recursive_signed_minus
        (recursive_signed_mult e1 (newton_p3_from e1 e2 e3))
        (recursive_signed_mult e2 (newton_p2_from e1 e2)))
      (recursive_signed_mult e3 (newton_p1_from e1)))
    (recursive_signed_mult (recursive_signed_nat 4) e4).

Definition newton_p5_from {arity}
    (e1 e2 e3 e4 e5 : recursive_signed_expression arity) :=
  recursive_signed_plus
    (recursive_signed_minus
      (recursive_signed_plus
        (recursive_signed_minus
          (recursive_signed_mult e1 (newton_p4_from e1 e2 e3 e4))
          (recursive_signed_mult e2 (newton_p3_from e1 e2 e3)))
        (recursive_signed_mult e3 (newton_p2_from e1 e2)))
      (recursive_signed_mult e4 (newton_p1_from e1)))
    (recursive_signed_mult (recursive_signed_nat 5) e5).

Definition newton_p6_from {arity}
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :=
  recursive_signed_minus
    (recursive_signed_plus
      (recursive_signed_minus
        (recursive_signed_plus
          (recursive_signed_minus
            (recursive_signed_mult e1
              (newton_p5_from e1 e2 e3 e4 e5))
            (recursive_signed_mult e2
              (newton_p4_from e1 e2 e3 e4)))
          (recursive_signed_mult e3 (newton_p3_from e1 e2 e3)))
        (recursive_signed_mult e4 (newton_p2_from e1 e2)))
      (recursive_signed_mult e5 (newton_p1_from e1)))
    (recursive_signed_mult (recursive_signed_nat 6) e6).

Definition newton_initial_state_from {arity}
    (e1 e2 e3 e4 e5 e6 : recursive_signed_expression arity) :
    recursive_expression arity :=
  recursive_inject6
    (recursive_signed_code (newton_p1_from e1))
    (recursive_signed_code (newton_p2_from e1 e2))
    (recursive_signed_code (newton_p3_from e1 e2 e3))
    (recursive_signed_code (newton_p4_from e1 e2 e3 e4))
    (recursive_signed_code (newton_p5_from e1 e2 e3 e4 e5))
    (recursive_signed_code (newton_p6_from e1 e2 e3 e4 e5 e6)).

Definition newton_initial_state_expression : recursive_expression 6 :=
  newton_initial_state_from
    (recursive_signed_input pos0) (recursive_signed_input pos1)
    (recursive_signed_input pos2) (recursive_signed_input pos3)
    (recursive_signed_input pos4) (recursive_signed_input pos5).

Definition newton_iteration_step_expression : recursive_expression 8 :=
  newton_step_from (RecVar pos0)
    (recursive_signed_input pos2) (recursive_signed_input pos3)
    (recursive_signed_input pos4) (recursive_signed_input pos5)
    (recursive_signed_input pos6) (recursive_signed_input pos7).

Definition newton_iterated_state_expression : recursive_expression 7 :=
  RecIter (RecMinus (RecVar pos0) (RecConst 1))
    (newton_initial_state_from
      (recursive_signed_input pos1) (recursive_signed_input pos2)
      (recursive_signed_input pos3) (recursive_signed_input pos4)
      (recursive_signed_input pos5) (recursive_signed_input pos6))
    newton_iteration_step_expression.

Definition newton_sparse_power_code_expression : recursive_expression 7 :=
  RecIfZero (RecVar pos0)
    (recursive_signed_code (recursive_signed_nat 6))
    (recursive_project6 pos0 newton_iterated_state_expression).

Definition encoded_newton_initial_state
    (elementary : Vector.t nat 6) : nat :=
  eval_recursive_expression newton_initial_state_expression elementary.

Definition encoded_newton_state_step
    (elementary : Vector.t nat 6) (state : nat) : nat :=
  encoded_newton_step (state ## elementary).

Definition encoded_newton_state_iter
    (power : nat) (elementary : Vector.t nat 6) : nat :=
  prim_min.iter (encoded_newton_state_step elementary) power
    (encoded_newton_initial_state elementary).

Definition encoded_newton_sparse_power_code
    (power : nat) (elementary : Vector.t nat 6) : nat :=
  match power with
  | 0 => signed_normalize 6 0
  | S previous =>
      vec_pos
        (project 6 (encoded_newton_state_iter previous elementary)) pos0
  end.

Lemma eval_newton_initial_state_shift power elementary :
  eval_recursive_expression
      (newton_initial_state_from
        (recursive_signed_input pos1) (recursive_signed_input pos2)
        (recursive_signed_input pos3) (recursive_signed_input pos4)
        (recursive_signed_input pos5) (recursive_signed_input pos6))
      (power ## elementary) =
  encoded_newton_initial_state elementary.
Proof. reflexivity. Qed.

Lemma eval_newton_iteration_step state power elementary :
  eval_recursive_expression newton_iteration_step_expression
      (state ## power ## elementary) =
  encoded_newton_state_step elementary state.
Proof. reflexivity. Qed.

Lemma eval_newton_iterated_state_expression power elementary :
  eval_recursive_expression newton_iterated_state_expression
      (power ## elementary) =
  encoded_newton_state_iter (power - 1) elementary.
Proof.
  unfold newton_iterated_state_expression, encoded_newton_state_iter.
  cbn [eval_recursive_expression].
  rewrite eval_newton_initial_state_shift.
  assert (Hiterate : forall iterations state,
      prim_min.iter
        (fun current =>
          eval_recursive_expression newton_iteration_step_expression
            (current ## power ## elementary)) iterations state =
      prim_min.iter (encoded_newton_state_step elementary)
        iterations state).
  { induction iterations as [|iterations IH]; intro state.
    - reflexivity.
    - rewrite !prim_min.iter_S.
      rewrite eval_newton_iteration_step.
      apply IH. }
  apply Hiterate.
Qed.

Theorem eval_newton_sparse_power_code_expression power elementary :
  eval_recursive_expression newton_sparse_power_code_expression
      (power ## elementary) =
  encoded_newton_sparse_power_code power elementary.
Proof.
  case: power=> [|previous].
  - reflexivity.
  - unfold newton_sparse_power_code_expression,
      encoded_newton_sparse_power_code.
    cbn [eval_recursive_expression ite_rel].
    rewrite eval_recursive_project eval_newton_iterated_state_expression.
    replace (S previous - 1)%N with previous by
      (rewrite subn1; reflexivity).
    reflexivity.
Qed.

Definition ra_newton_sparse_power : recalg 7 :=
  compile_recursive_expression newton_sparse_power_code_expression.

Theorem ra_newton_sparse_power_correct power elementary :
  ⟦ra_newton_sparse_power⟧ (power ## elementary)
    (encoded_newton_sparse_power_code power elementary).
Proof.
  unfold ra_newton_sparse_power.
  rewrite <- eval_newton_sparse_power_code_expression.
  apply compile_recursive_expression_correct.
Qed.

Theorem ra_newton_sparse_power_primitive_recursive :
  prim_rec ra_newton_sparse_power.
Proof. apply compile_recursive_expression_primitive_recursive. Qed.

Theorem encoded_newton_sparse_power_murec :
  MuRec_computable
    (fun values out =>
      out = encoded_newton_sparse_power_code
        (vec_pos values pos0) (vec_tail values)).
Proof.
  refine (@recalg_graph_murec 7
    (fun values => encoded_newton_sparse_power_code
      (vec_pos values pos0) (vec_tail values))
    ra_newton_sparse_power _).
  intro values; vec split values with power.
  exact: ra_newton_sparse_power_correct.
Qed.

(* A transparent Stdlib-Z model of exactly the same Newton recurrence. *)

Definition decode_six_vector (codes : Vector.t nat 6) : Vector.t Z 6 :=
  vec_map zigzag_decode codes.

Definition z_newton_p1 (elementary : Vector.t Z 6) : Z :=
  vec_pos elementary pos0.

Definition z_newton_p2 (elementary : Vector.t Z 6) : Z :=
  Z.sub (Z.mul (vec_pos elementary pos0) (z_newton_p1 elementary))
    (Z.mul 2 (vec_pos elementary pos1)).

Definition z_newton_p3 (elementary : Vector.t Z 6) : Z :=
  Z.add
    (Z.sub (Z.mul (vec_pos elementary pos0) (z_newton_p2 elementary))
      (Z.mul (vec_pos elementary pos1) (z_newton_p1 elementary)))
    (Z.mul 3 (vec_pos elementary pos2)).

Definition z_newton_p4 (elementary : Vector.t Z 6) : Z :=
  Z.sub
    (Z.add
      (Z.sub (Z.mul (vec_pos elementary pos0) (z_newton_p3 elementary))
        (Z.mul (vec_pos elementary pos1) (z_newton_p2 elementary)))
      (Z.mul (vec_pos elementary pos2) (z_newton_p1 elementary)))
    (Z.mul 4 (vec_pos elementary pos3)).

Definition z_newton_p5 (elementary : Vector.t Z 6) : Z :=
  Z.add
    (Z.sub
      (Z.add
        (Z.sub (Z.mul (vec_pos elementary pos0) (z_newton_p4 elementary))
          (Z.mul (vec_pos elementary pos1) (z_newton_p3 elementary)))
        (Z.mul (vec_pos elementary pos2) (z_newton_p2 elementary)))
      (Z.mul (vec_pos elementary pos3) (z_newton_p1 elementary)))
    (Z.mul 5 (vec_pos elementary pos4)).

Definition z_newton_p6 (elementary : Vector.t Z 6) : Z :=
  Z.sub
    (Z.add
      (Z.sub
        (Z.add
          (Z.sub (Z.mul (vec_pos elementary pos0) (z_newton_p5 elementary))
            (Z.mul (vec_pos elementary pos1) (z_newton_p4 elementary)))
          (Z.mul (vec_pos elementary pos2) (z_newton_p3 elementary)))
        (Z.mul (vec_pos elementary pos3) (z_newton_p2 elementary)))
      (Z.mul (vec_pos elementary pos4) (z_newton_p1 elementary)))
    (Z.mul 6 (vec_pos elementary pos5)).

Definition z_newton_initial_state (elementary : Vector.t Z 6) :
    Vector.t Z 6 :=
  z_newton_p1 elementary ## z_newton_p2 elementary ##
  z_newton_p3 elementary ## z_newton_p4 elementary ##
  z_newton_p5 elementary ## z_newton_p6 elementary ## vec_nil.

Definition z_newton_next (elementary state : Vector.t Z 6) : Z :=
  Z.sub
    (Z.add
      (Z.sub
        (Z.add
          (Z.sub
            (Z.mul (vec_pos elementary pos0) (vec_pos state pos5))
            (Z.mul (vec_pos elementary pos1) (vec_pos state pos4)))
          (Z.mul (vec_pos elementary pos2) (vec_pos state pos3)))
        (Z.mul (vec_pos elementary pos3) (vec_pos state pos2)))
      (Z.mul (vec_pos elementary pos4) (vec_pos state pos1)))
    (Z.mul (vec_pos elementary pos5) (vec_pos state pos0)).

Definition z_newton_step (elementary state : Vector.t Z 6) :
    Vector.t Z 6 :=
  vec_pos state pos1 ## vec_pos state pos2 ## vec_pos state pos3 ##
  vec_pos state pos4 ## vec_pos state pos5 ##
  z_newton_next elementary state ## vec_nil.

Definition z_newton_sparse_power
    (elementary : Vector.t Z 6) (power : nat) : Z :=
  match power with
  | 0 => Z.of_nat 6
  | S previous =>
      vec_pos
        (prim_min.iter (z_newton_step elementary) previous
          (z_newton_initial_state elementary)) pos0
  end.

Lemma eval_recursive_signed_of_nat {arity}
    (expression : recursive_expression arity) values :
  eval_recursive_signed_expression (recursive_signed_of_nat expression)
      values =
  Z.of_nat (eval_recursive_expression expression values).
Proof.
  unfold recursive_signed_of_nat, eval_recursive_signed_expression; cbn.
  lia.
Qed.

Lemma decode_encoded_newton_initial_state elementary :
  decode_six_vector (project 6 (encoded_newton_initial_state elementary)) =
  z_newton_initial_state (decode_six_vector elementary).
Proof.
  unfold encoded_newton_initial_state, newton_initial_state_expression,
    newton_initial_state_from, decode_six_vector, z_newton_initial_state.
  rewrite eval_recursive_inject6 project_inject.
  cbn [vec_map].
  repeat f_equal.
  all: rewrite zigzag_decode_recursive_signed_code.
  all: unfold newton_p6_from, newton_p5_from, newton_p4_from,
    newton_p3_from, newton_p2_from, newton_p1_from,
    recursive_signed_nat.
  all: repeat first
    [ rewrite eval_recursive_signed_minus
    | rewrite eval_recursive_signed_plus
    | rewrite eval_recursive_signed_mult
    | rewrite eval_recursive_signed_input
    | rewrite eval_recursive_signed_of_nat ].
  all: unfold z_newton_p6, z_newton_p5, z_newton_p4,
    z_newton_p3, z_newton_p2, z_newton_p1.
  all: repeat rewrite vec_pos_map.
  all: cbn [eval_recursive_expression].
  all: reflexivity.
Qed.

Lemma encoded_newton_recurrence_z state elementary :
  encoded_newton_recurrence (state ## elementary) =
  z_newton_next (decode_six_vector elementary)
    (decode_six_vector (project 6 state)).
Proof.
  unfold encoded_newton_recurrence, z_newton_next, decode_six_vector.
  repeat rewrite vec_pos_map.
  reflexivity.
Qed.

Lemma decode_encoded_newton_step state elementary :
  decode_six_vector
      (project 6 (encoded_newton_state_step elementary state)) =
  z_newton_step (decode_six_vector elementary)
    (decode_six_vector (project 6 state)).
Proof.
  unfold encoded_newton_state_step, z_newton_step, decode_six_vector.
  rewrite encoded_newton_step_project.
  cbn [vec_map].
  do 6 f_equal.
  rewrite zigzag_decode_signed_normalize.
  change
    (eval_recursive_signed_expression newton_recurrence_signed
      (state ## elementary) =
    z_newton_next (vec_map zigzag_decode elementary)
      (vec_map zigzag_decode (project 6 state))).
  rewrite eval_newton_recurrence_signed.
  exact: encoded_newton_recurrence_z.
Qed.

Lemma decode_encoded_newton_state_iter_from iterations elementary state :
  decode_six_vector
    (project 6
      (prim_min.iter (encoded_newton_state_step elementary) iterations
        state)) =
  prim_min.iter (z_newton_step (decode_six_vector elementary)) iterations
    (decode_six_vector (project 6 state)).
Proof.
  revert state.
  induction iterations as [|iterations IH]; intro state.
  - reflexivity.
  - rewrite !prim_min.iter_S.
    rewrite IH decode_encoded_newton_step.
    reflexivity.
Qed.

Theorem decode_encoded_newton_sparse_power power elementary :
  zigzag_decode (encoded_newton_sparse_power_code power elementary) =
  z_newton_sparse_power (decode_six_vector elementary) power.
Proof.
  case: power=> [|previous].
  - cbn [encoded_newton_sparse_power_code z_newton_sparse_power].
    rewrite zigzag_decode_signed_normalize. reflexivity.
  - unfold encoded_newton_sparse_power_code, z_newton_sparse_power,
      encoded_newton_state_iter.
    have Hstates := decode_encoded_newton_state_iter_from previous elementary
      (encoded_newton_initial_state elementary).
    rewrite decode_encoded_newton_initial_state in Hstates.
    have Hcomponent := congr1 (fun state => vec_pos state pos0) Hstates.
    rewrite /decode_six_vector vec_pos_map in Hcomponent.
    exact Hcomponent.
Qed.

Corollary ra_newton_sparse_power_decodes power elementary :
  ⟦ra_newton_sparse_power⟧ (power ## elementary)
    (encoded_newton_sparse_power_code power elementary) /\
  zigzag_decode (encoded_newton_sparse_power_code power elementary) =
    z_newton_sparse_power (decode_six_vector elementary) power.
Proof. split; [apply ra_newton_sparse_power_correct|apply decode_encoded_newton_sparse_power]. Qed.

(* --------------------------------------------------------------------- *)
(* Compact table lookup and the 203-term Mobius evaluator.               *)

Definition lift_pos_renaming {source target}
    (rename : pos source -> pos target) :
    pos (S source) -> pos (S target) :=
  fun variable =>
    match variable with
    | @Fin.F1 _ => pos0
    | @Fin.FS _ tail => pos_nxt (rename tail)
    end.

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
  | nil => RecConst 0
  | value :: tail =>
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
  | nil => 0
  | label :: tail =>
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

Print Assumptions compile_recursive_expression_correct.
Print Assumptions compile_recursive_expression_primitive_recursive.
Print Assumptions ra_recursive_inject6_correct.
Print Assumptions encoded_newton_step_last_decode.
Print Assumptions ra_newton_step_correct.
Print Assumptions encoded_newton_step_murec.
Print Assumptions ra_newton_sparse_power_correct.
Print Assumptions decode_encoded_newton_sparse_power.
Print Assumptions ra_newton_sparse_power_decodes.
Print Assumptions ra_newton_sparse_term_correct.
Print Assumptions newton_sparse_term_relation_murec.
Print Assumptions decode_encoded_newton_sparse_term.

End PolynomialFormulasSexticMuRecSparseEvaluator.
