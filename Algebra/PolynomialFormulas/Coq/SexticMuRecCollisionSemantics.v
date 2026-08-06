From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra.
From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util Require Import recomp.
From PolynomialFormulas Require Import
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecSparseEvaluator SexticMuRecCollisionEvaluator
  SexticRecursiveCore SexticSparsePolynomials SexticSparseResolvents
  SexticPowerSumSymmetric SexticNewtonPowerSums SexticComputedResolvents
  SexticSeparatingSearch SexticMuRecSeparatingInstance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Exact semantic connection between the compact recursive collision
    evaluator and the executable MathComp separating search.  The generic
    interpreter lemmas in the first part are deliberately independent of the
    pair tables, so the triple evaluator can reuse them unchanged. *)
Module PolynomialFormulasSexticMuRecCollisionSemantics.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SP := PolynomialFormulasSexticSparsePolynomials.
Module SR := PolynomialFormulasSexticSparseResolvents.
Module PS := PolynomialFormulasSexticPowerSumSymmetric.
Module NPS := PolynomialFormulasSexticNewtonPowerSums.
Module CR := PolynomialFormulasSexticComputedResolvents.
Module SS := PolynomialFormulasSexticSeparatingSearch.
Module SSI := PolynomialFormulasSexticMuRecSeparatingInstance.
Module SMFD := PolynomialFormulasSexticMuRecFactorDecision.
Module SE := PolynomialFormulasSexticMuRecSparseEvaluator.
Module CE := PolynomialFormulasSexticMuRecCollisionEvaluator.

(* --------------------------------------------------------------------- *)
(* A MathComp-integer semantics for the recursive signed interpreter.     *)

Definition eval_mathcomp_recursive_signed_expression {arity}
    (expression : SE.recursive_signed_expression arity)
    (values : Vector.t nat arity) : int :=
  (SE.eval_recursive_expression (SE.recursive_positive expression)
      values)%:Z -
  (SE.eval_recursive_expression (SE.recursive_negative expression)
      values)%:Z.

(** The recursive interpreter's normalization is exactly the canonical
    MathComp zigzag encoding, not merely another code with the same sign. *)
Lemma eval_recursive_signed_code_mathcomp {arity}
    (expression : SE.recursive_signed_expression arity) values :
  SE.eval_recursive_expression (SE.recursive_signed_code expression) values =
  mathcomp_zigzag_encode
    (eval_mathcomp_recursive_signed_expression expression values).
Proof.
unfold SE.recursive_signed_code,
  eval_mathcomp_recursive_signed_expression.
cbn [SE.eval_recursive_expression].
remember
  (SE.eval_recursive_expression (SE.recursive_positive expression) values)
  as positive eqn:hpositive.
remember
  (SE.eval_recursive_expression (SE.recursive_negative expression) values)
  as negative eqn:hnegative.
case: (leqP negative positive)=> hle.
- have hzero : (negative - positive)%N = 0%N.
    apply/eqP.
    by rewrite subn_eq0.
  rewrite hzero.
  have hdecomp :
      positive = ((positive - negative) + negative)%N.
    by rewrite subnK.
  have hint : (positive%:Z - negative%:Z : int) =
      Posz (positive - negative).
    have hcast := congr1 (fun value : nat => (value%:Z : int)) hdecomp.
    rewrite PoszD in hcast.
    by rewrite hcast addrK.
  rewrite hint /mathcomp_zigzag_encode.
  reflexivity.
- have hposle : (positive <= negative)%N := ltnW hle.
  have hzero : (positive - negative)%N = 0%N.
    apply/eqP.
    by rewrite subn_eq0.
  rewrite hzero.
  pose magnitude := (negative - positive).-1.
  have hdiffpos : (0 < negative - positive)%N.
    by rewrite subn_gt0.
  have hdiff : (negative - positive)%N = magnitude.+1.
    by rewrite /magnitude prednK.
  rewrite hdiff /=.
  have hint : (positive%:Z - negative%:Z : int) = Negz magnitude.
    have hdecomp : negative = (positive + magnitude.+1)%N.
      rewrite addnC -hdiff.
      by rewrite subnK.
    rewrite hdecomp PoszD NegzE opprD addrA subrr add0r.
    reflexivity.
  rewrite hint /mathcomp_zigzag_encode.
  change
    (S (Nat.mul 2 (Nat.sub (S magnitude) 1)) =
      Nat.add (Nat.mul 2 magnitude) 1).
  rewrite Nat.sub_1_r Nat.pred_succ Nat.add_1_r.
  reflexivity.
Qed.

Lemma eval_mathcomp_recursive_signed_input {arity}
    (variable : pos arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.recursive_signed_input variable) values =
  mathcomp_zigzag_decode (vec_pos values variable).
Proof. reflexivity. Qed.

Lemma eval_mathcomp_recursive_signed_decode {arity}
    (code : SE.recursive_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.recursive_signed_decode code) values =
  mathcomp_zigzag_decode
    (SE.eval_recursive_expression code values).
Proof. reflexivity. Qed.

Lemma eval_mathcomp_recursive_signed_of_nat {arity}
    (expression : SE.recursive_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.recursive_signed_of_nat expression) values =
  (SE.eval_recursive_expression expression values)%:Z.
Proof.
by rewrite /eval_mathcomp_recursive_signed_expression
  /SE.recursive_signed_of_nat /= subr0.
Qed.

Lemma eval_mathcomp_recursive_signed_plus {arity}
    (left right : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.recursive_signed_plus left right) values =
  eval_mathcomp_recursive_signed_expression left values +
  eval_mathcomp_recursive_signed_expression right values.
Proof.
rewrite /eval_mathcomp_recursive_signed_expression
  /SE.recursive_signed_plus /= !PoszD.
finish_mathcomp_int_ring.
Qed.

Lemma eval_mathcomp_recursive_signed_negate {arity}
    (expression : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.recursive_signed_negate expression) values =
  - eval_mathcomp_recursive_signed_expression expression values.
Proof.
rewrite /eval_mathcomp_recursive_signed_expression
  /SE.recursive_signed_negate /=.
finish_mathcomp_int_ring.
Qed.

Lemma eval_mathcomp_recursive_signed_mult {arity}
    (left right : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.recursive_signed_mult left right) values =
  eval_mathcomp_recursive_signed_expression left values *
  eval_mathcomp_recursive_signed_expression right values.
Proof.
rewrite /eval_mathcomp_recursive_signed_expression
  /SE.recursive_signed_mult /= !PoszD !PoszM.
finish_mathcomp_int_ring.
Qed.

Lemma eval_mathcomp_recursive_signed_if_zero {arity}
    (test : SE.recursive_expression arity)
    (if_zero if_nonzero : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (CE.recursive_signed_if_zero test if_zero if_nonzero) values =
  if SE.eval_recursive_expression test values is 0%nat
  then eval_mathcomp_recursive_signed_expression if_zero values
  else eval_mathcomp_recursive_signed_expression if_nonzero values.
Proof.
rewrite /eval_mathcomp_recursive_signed_expression
  /CE.recursive_signed_if_zero /=.
by case: (SE.eval_recursive_expression test values).
Qed.

Lemma Posz_lsum_map_sub (indices : list nat)
    (positive negative : nat -> nat) :
  (lsum (List.map positive indices))%:Z -
      (lsum (List.map negative indices))%:Z =
    \sum_(index <- indices)
      ((positive index)%:Z - (negative index)%:Z : int).
Proof.
elim: indices=> [|index indices ih].
- change ((0%nat)%:Z - (0%nat)%:Z = \sum_(index <- [::])
    ((positive index)%:Z - (negative index)%:Z : int)).
  rewrite big_nil subrr.
  reflexivity.
- change
    ((positive index + lsum (List.map positive indices))%:Z -
       (negative index + lsum (List.map negative indices))%:Z =
     \sum_(entry <- index :: indices)
       ((positive entry)%:Z - (negative entry)%:Z : int)).
  rewrite !PoszD big_cons -ih.
  finish_mathcomp_int_ring.
Qed.

(** [RecBoundedSum] is an honest finite sum over the half-open interval
    [0, upper).  This list form matches the recursive interpreter exactly
    and is convenient for both the pair and triple mixed-radix proofs. *)
Lemma eval_mathcomp_recursive_signed_bounded_sum {arity}
    (upper : SE.recursive_expression arity)
    (body : SE.recursive_signed_expression (S arity)) values :
  eval_mathcomp_recursive_signed_expression
      (CE.recursive_signed_bounded_sum upper body) values =
    \sum_(index <-
        list_an 0 (SE.eval_recursive_expression upper values))
      eval_mathcomp_recursive_signed_expression body (index ## values).
Proof.
rewrite /eval_mathcomp_recursive_signed_expression
  /CE.recursive_signed_bounded_sum /=.
exact: Posz_lsum_map_sub.
Qed.

(* --------------------------------------------------------------------- *)
(* Renaming and weakening commute with the recursive interpreter.         *)

Definition recursive_renamed_values {source target}
    (rename : pos source -> pos target)
    (values : Vector.t nat target) : Vector.t nat source :=
  vec_set_pos (fun variable => vec_pos values (rename variable)).

Lemma iter_pointwise (X : Type) (left right : X -> X) iterations initial :
  (forall state, left state = right state) ->
  prim_min.iter left iterations initial =
  prim_min.iter right iterations initial.
Proof.
move=> hstep.
elim: iterations=> [|iterations ih] //=.
by rewrite ih hstep.
Qed.

Lemma recursive_renamed_values_lift {source target}
    (rename : pos source -> pos target) index values :
  recursive_renamed_values (CE.lift_pos_renaming rename)
      (index ## values) =
  index ## recursive_renamed_values rename values.
Proof.
apply vec_pos_ext=> variable.
analyse pos variable; cbn [recursive_renamed_values
  CE.lift_pos_renaming].
- by rewrite vec_pos_set.
- by rewrite !vec_pos_set.
Qed.

Lemma eval_recursive_rename {source}
    (expression : SE.recursive_expression source) :
  forall target (rename : pos source -> pos target) values,
  SE.eval_recursive_expression (CE.recursive_rename rename expression) values =
  SE.eval_recursive_expression expression
    (recursive_renamed_values rename values).
Proof.
induction expression; intros target rename values;
  cbn [CE.recursive_rename SE.eval_recursive_expression].
- reflexivity.
- by rewrite /recursive_renamed_values vec_pos_set.
- by rewrite IHexpression.
- by rewrite IHexpression1 IHexpression2.
- by rewrite IHexpression1 IHexpression2.
- by rewrite IHexpression1 IHexpression2.
- by rewrite IHexpression.
- by rewrite IHexpression.
- by rewrite IHexpression1 IHexpression2 IHexpression3.
- by rewrite IHexpression.
- by rewrite IHexpression.
- by rewrite IHexpression1 IHexpression2.
- rewrite IHexpression1.
  apply f_equal.
  apply List.map_ext=> index.
  rewrite IHexpression2 recursive_renamed_values_lift.
  reflexivity.
- rewrite IHexpression1 IHexpression2.
  apply: iter_pointwise=> state.
  rewrite IHexpression3 recursive_renamed_values_lift.
  reflexivity.
Qed.

Lemma eval_recursive_signed_rename {source}
    (expression : SE.recursive_signed_expression source)
    target (rename : pos source -> pos target) values :
  eval_mathcomp_recursive_signed_expression
      (CE.recursive_signed_rename rename expression) values =
  eval_mathcomp_recursive_signed_expression expression
    (recursive_renamed_values rename values).
Proof.
rewrite /eval_mathcomp_recursive_signed_expression
  /CE.recursive_signed_rename /= !eval_recursive_rename.
reflexivity.
Qed.

Lemma recursive_renamed_values_weaken {arity} head
    (values : Vector.t nat arity) :
  recursive_renamed_values (@pos_nxt arity) (head ## values) = values.
Proof.
apply vec_pos_ext=> variable.
by rewrite /recursive_renamed_values vec_pos_set.
Qed.

Lemma eval_recursive_weaken {arity}
    (expression : SE.recursive_expression arity) head values :
  SE.eval_recursive_expression (CE.recursive_weaken expression)
      (head ## values) =
  SE.eval_recursive_expression expression values.
Proof.
rewrite /CE.recursive_weaken eval_recursive_rename
  recursive_renamed_values_weaken.
reflexivity.
Qed.

Lemma eval_recursive_signed_weaken {arity}
    (expression : SE.recursive_signed_expression arity) head values :
  eval_mathcomp_recursive_signed_expression
      (CE.recursive_signed_weaken expression) (head ## values) =
  eval_mathcomp_recursive_signed_expression expression values.
Proof.
rewrite /CE.recursive_signed_weaken eval_recursive_signed_rename
  recursive_renamed_values_weaken.
reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Transparent lookup and state-code lemmas shared by pair and triple.    *)

Lemma eval_recursive_lookup_list {arity} (table : list nat)
    (index : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (CE.recursive_lookup_list table index) values =
  nth 0 table (SE.eval_recursive_expression index values).
Proof.
revert index.
induction table as [|entry table ih]; intro index.
- cbn [CE.recursive_lookup_list SE.eval_recursive_expression].
  by rewrite nth_nil.
- cbn [CE.recursive_lookup_list SE.eval_recursive_expression].
  remember (SE.eval_recursive_expression index values) as position.
  destruct position as [|position].
  + reflexivity.
  + rewrite ih.
    cbn [SE.eval_recursive_expression].
    rewrite -Heqposition subn1.
    reflexivity.
Qed.

Lemma eval_recursive_inject9 {arity}
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : SE.recursive_expression arity)
    values :
  SE.eval_recursive_expression
      (CE.recursive_inject9 a0 a1 a2 a3 a4 a5 a6 a7 a8) values =
  inject
    (SE.eval_recursive_expression a0 values ##
     SE.eval_recursive_expression a1 values ##
     SE.eval_recursive_expression a2 values ##
     SE.eval_recursive_expression a3 values ##
     SE.eval_recursive_expression a4 values ##
     SE.eval_recursive_expression a5 values ##
     SE.eval_recursive_expression a6 values ##
     SE.eval_recursive_expression a7 values ##
     SE.eval_recursive_expression a8 values ## vec_nil).
Proof. reflexivity. Qed.

Lemma eval_recursive_project9 {arity} (index : pos 9)
    (code : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (CE.recursive_project9 index code) values =
  vec_pos
    (project 9 (SE.eval_recursive_expression code values)) index.
Proof. exact: SE.eval_recursive_project. Qed.

Print Assumptions eval_recursive_signed_code_mathcomp.
Print Assumptions eval_mathcomp_recursive_signed_bounded_sum.
Print Assumptions eval_recursive_rename.
Print Assumptions eval_recursive_lookup_list.

End PolynomialFormulasSexticMuRecCollisionSemantics.
