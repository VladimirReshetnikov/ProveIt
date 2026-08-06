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

Lemma eval_recursive_if_zero {arity}
    (test if_zero if_nonzero : SE.recursive_expression arity) values :
  SE.eval_recursive_expression
      (SE.RecIfZero test if_zero if_nonzero) values =
    match SE.eval_recursive_expression test values with
    | 0%nat => SE.eval_recursive_expression if_zero values
    | S _ => SE.eval_recursive_expression if_nonzero values
    end.
Proof. reflexivity. Qed.

Lemma eval_recursive_minus {arity}
    (left right : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (SE.RecMinus left right) values =
    (SE.eval_recursive_expression left values -
      SE.eval_recursive_expression right values)%nat.
Proof. reflexivity. Qed.

Lemma eval_recursive_const {arity} constant values :
  SE.eval_recursive_expression (@SE.RecConst arity constant) values =
    constant.
Proof. reflexivity. Qed.

Lemma eval_recursive_iter {arity}
    (count initial : SE.recursive_expression arity)
    (step : SE.recursive_expression (S arity)) values :
  SE.eval_recursive_expression (SE.RecIter count initial step) values =
    prim_min.iter
      (fun state => SE.eval_recursive_expression step (state ## values))
      (SE.eval_recursive_expression count values)
      (SE.eval_recursive_expression initial values).
Proof. reflexivity. Qed.

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

(* --------------------------------------------------------------------- *)
(* The recursive Newton engine denotes the sparse Newton construction.    *)

Lemma eval_mathcomp_recursive_signed_minus {arity}
    (left right : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.recursive_signed_minus left right) values =
    eval_mathcomp_recursive_signed_expression left values -
    eval_mathcomp_recursive_signed_expression right values.
Proof.
rewrite /SE.recursive_signed_minus
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_negate.
reflexivity.
Qed.

Lemma eval_mathcomp_recursive_signed_nat {arity} constant values :
  eval_mathcomp_recursive_signed_expression
      (@SE.recursive_signed_nat arity constant) values = constant%:Z.
Proof.
by rewrite /SE.recursive_signed_nat
  eval_mathcomp_recursive_signed_of_nat.
Qed.

Lemma decode_eval_recursive_signed_code_mathcomp {arity}
    (expression : SE.recursive_signed_expression arity) values :
  mathcomp_zigzag_decode
      (SE.eval_recursive_expression
        (SE.recursive_signed_code expression) values) =
    eval_mathcomp_recursive_signed_expression expression values.
Proof.
by rewrite eval_recursive_signed_code_mathcomp
  mathcomp_zigzag_decode_encode.
Qed.

Definition recursive_elementary_values {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity)
    (values : Vector.t nat arity) : 6.-tuple int :=
  [tuple
    eval_mathcomp_recursive_signed_expression e1 values;
    eval_mathcomp_recursive_signed_expression e2 values;
    eval_mathcomp_recursive_signed_expression e3 values;
    eval_mathcomp_recursive_signed_expression e4 values;
    eval_mathcomp_recursive_signed_expression e5 values;
    eval_mathcomp_recursive_signed_expression e6 values].

Definition recursive_sparse_exponent {arity}
    (x0 x1 x2 x3 x4 x5 : SE.recursive_expression arity)
    (values : Vector.t nat arity) : SP.sparse_exponent :=
  [tuple
    SE.eval_recursive_expression x0 values;
    SE.eval_recursive_expression x1 values;
    SE.eval_recursive_expression x2 values;
    SE.eval_recursive_expression x3 values;
    SE.eval_recursive_expression x4 values;
    SE.eval_recursive_expression x5 values].

Lemma sparse_eval_ring_recursive_newton_e1 {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_e1 =
    eval_mathcomp_recursive_signed_expression e1 values.
Proof. by rewrite /NPS.newton_e1 NPS.sparse_eval_ring_var. Qed.

Lemma sparse_eval_ring_recursive_newton_e2 {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_e2 =
    eval_mathcomp_recursive_signed_expression e2 values.
Proof.
by rewrite /NPS.newton_e2 NPS.sparse_eval_ring_var
  (tnth_nth 0) inordK.
Qed.

Lemma sparse_eval_ring_recursive_newton_e3 {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_e3 =
    eval_mathcomp_recursive_signed_expression e3 values.
Proof.
by rewrite /NPS.newton_e3 NPS.sparse_eval_ring_var
  (tnth_nth 0) inordK.
Qed.

Lemma sparse_eval_ring_recursive_newton_e4 {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_e4 =
    eval_mathcomp_recursive_signed_expression e4 values.
Proof.
by rewrite /NPS.newton_e4 NPS.sparse_eval_ring_var
  (tnth_nth 0) inordK.
Qed.

Lemma sparse_eval_ring_recursive_newton_e5 {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_e5 =
    eval_mathcomp_recursive_signed_expression e5 values.
Proof.
by rewrite /NPS.newton_e5 NPS.sparse_eval_ring_var
  (tnth_nth 0) inordK.
Qed.

Lemma sparse_eval_ring_recursive_newton_e6 {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_e6 =
    eval_mathcomp_recursive_signed_expression e6 values.
Proof.
by rewrite /NPS.newton_e6 NPS.sparse_eval_ring_var
  (tnth_nth 0) inordK.
Qed.

Lemma eval_recursive_newton_p1_from {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.newton_p1_from e1) values =
    NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_p1.
Proof.
by rewrite /SE.newton_p1_from /NPS.newton_p1
  sparse_eval_ring_recursive_newton_e1.
Qed.

Lemma eval_recursive_newton_p2_from {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.newton_p2_from e1 e2) values =
    NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_p2.
Proof.
rewrite /SE.newton_p2_from /NPS.newton_p2
  eval_mathcomp_recursive_signed_minus
  !eval_mathcomp_recursive_signed_mult
  eval_mathcomp_recursive_signed_nat
  NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_mul
  NPS.sparse_eval_ring_nsmul
  sparse_eval_ring_recursive_newton_e1
  sparse_eval_ring_recursive_newton_e2
  (@eval_recursive_newton_p1_from arity
    e1 e2 e3 e4 e5 e6 values).
reflexivity.
Qed.

Lemma eval_recursive_newton_p3_from {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.newton_p3_from e1 e2 e3) values =
    NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_p3.
Proof.
rewrite /SE.newton_p3_from /NPS.newton_p3
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  !eval_mathcomp_recursive_signed_mult
  eval_mathcomp_recursive_signed_nat
  NPS.sparse_eval_ring_add NPS.sparse_eval_ring_sub
  !NPS.sparse_eval_ring_mul NPS.sparse_eval_ring_nsmul
  sparse_eval_ring_recursive_newton_e1
  sparse_eval_ring_recursive_newton_e2
  sparse_eval_ring_recursive_newton_e3
  (@eval_recursive_newton_p1_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p2_from arity
    e1 e2 e3 e4 e5 e6 values).
reflexivity.
Qed.

Lemma eval_recursive_newton_p4_from {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.newton_p4_from e1 e2 e3 e4) values =
    NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_p4.
Proof.
rewrite /SE.newton_p4_from /NPS.newton_p4.
rewrite eval_mathcomp_recursive_signed_minus
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  !eval_mathcomp_recursive_signed_mult
  eval_mathcomp_recursive_signed_nat.
rewrite NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_add
  NPS.sparse_eval_ring_sub !NPS.sparse_eval_ring_mul
  NPS.sparse_eval_ring_nsmul.
rewrite (@eval_recursive_newton_p3_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p2_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p1_from arity
    e1 e2 e3 e4 e5 e6 values)
  sparse_eval_ring_recursive_newton_e1
  sparse_eval_ring_recursive_newton_e2
  sparse_eval_ring_recursive_newton_e3
  sparse_eval_ring_recursive_newton_e4.
reflexivity.
Qed.

Lemma eval_recursive_newton_p5_from {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.newton_p5_from e1 e2 e3 e4 e5) values =
    NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_p5.
Proof.
rewrite /SE.newton_p5_from /NPS.newton_p5.
rewrite eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  !eval_mathcomp_recursive_signed_mult
  eval_mathcomp_recursive_signed_nat.
rewrite NPS.sparse_eval_ring_add NPS.sparse_eval_ring_sub
  NPS.sparse_eval_ring_add NPS.sparse_eval_ring_sub
  !NPS.sparse_eval_ring_mul NPS.sparse_eval_ring_nsmul.
rewrite (@eval_recursive_newton_p4_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p3_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p2_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p1_from arity
    e1 e2 e3 e4 e5 e6 values)
  sparse_eval_ring_recursive_newton_e1
  sparse_eval_ring_recursive_newton_e2
  sparse_eval_ring_recursive_newton_e3
  sparse_eval_ring_recursive_newton_e4
  sparse_eval_ring_recursive_newton_e5.
reflexivity.
Qed.

Lemma eval_recursive_newton_p6_from {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (SE.newton_p6_from e1 e2 e3 e4 e5 e6) values =
    NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      NPS.newton_p6.
Proof.
rewrite /SE.newton_p6_from /NPS.newton_p6.
rewrite eval_mathcomp_recursive_signed_minus
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  !eval_mathcomp_recursive_signed_mult
  eval_mathcomp_recursive_signed_nat.
rewrite NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_add
  NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_add
  NPS.sparse_eval_ring_sub !NPS.sparse_eval_ring_mul
  NPS.sparse_eval_ring_nsmul.
rewrite (@eval_recursive_newton_p5_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p4_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p3_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p2_from arity
    e1 e2 e3 e4 e5 e6 values)
  (@eval_recursive_newton_p1_from arity
    e1 e2 e3 e4 e5 e6 values)
  sparse_eval_ring_recursive_newton_e1
  sparse_eval_ring_recursive_newton_e2
  sparse_eval_ring_recursive_newton_e3
  sparse_eval_ring_recursive_newton_e4
  sparse_eval_ring_recursive_newton_e5
  sparse_eval_ring_recursive_newton_e6.
reflexivity.
Qed.

Definition decode_recursive_newton_state_component
    (state : nat) (index : pos 6) : int :=
  mathcomp_zigzag_decode (vec_pos (project 6 state) index).

Definition recursive_newton_state_semantics
    (state : nat) (elementary : 6.-tuple int)
    (sparse_state : NPS.newton_state) : Prop :=
  decode_recursive_newton_state_component state pos0 =
      NPS.sparse_eval_ring elementary (NPS.newton_s1 sparse_state) /\
  decode_recursive_newton_state_component state pos1 =
      NPS.sparse_eval_ring elementary (NPS.newton_s2 sparse_state) /\
  decode_recursive_newton_state_component state pos2 =
      NPS.sparse_eval_ring elementary (NPS.newton_s3 sparse_state) /\
  decode_recursive_newton_state_component state pos3 =
      NPS.sparse_eval_ring elementary (NPS.newton_s4 sparse_state) /\
  decode_recursive_newton_state_component state pos4 =
      NPS.sparse_eval_ring elementary (NPS.newton_s5 sparse_state) /\
  decode_recursive_newton_state_component state pos5 =
      NPS.sparse_eval_ring elementary (NPS.newton_s6 sparse_state).

Lemma eval_recursive_newton_initial_state_from {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  recursive_newton_state_semantics
    (SE.eval_recursive_expression
      (SE.newton_initial_state_from e1 e2 e3 e4 e5 e6) values)
    (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
    NPS.newton_initial_state.
Proof.
rewrite /recursive_newton_state_semantics
  /decode_recursive_newton_state_component
  /NPS.newton_initial_state.
rewrite !SE.eval_recursive_inject6 !project_inject.
cbn [vec_pos NPS.newton_s1 NPS.newton_s2 NPS.newton_s3
  NPS.newton_s4 NPS.newton_s5 NPS.newton_s6].
repeat split.
- rewrite decode_eval_recursive_signed_code_mathcomp.
  exact: eval_recursive_newton_p1_from.
- rewrite decode_eval_recursive_signed_code_mathcomp.
  exact: eval_recursive_newton_p2_from.
- rewrite decode_eval_recursive_signed_code_mathcomp.
  exact: eval_recursive_newton_p3_from.
- rewrite decode_eval_recursive_signed_code_mathcomp.
  exact: eval_recursive_newton_p4_from.
- rewrite decode_eval_recursive_signed_code_mathcomp.
  exact: eval_recursive_newton_p5_from.
- rewrite decode_eval_recursive_signed_code_mathcomp.
  exact: eval_recursive_newton_p6_from.
Qed.

Lemma eval_recursive_newton_state_signed_from {arity}
    (state : SE.recursive_expression arity) (index : pos 6) values :
  eval_mathcomp_recursive_signed_expression
      (SE.newton_state_signed_from state index) values =
    decode_recursive_newton_state_component
      (SE.eval_recursive_expression state values) index.
Proof.
rewrite /SE.newton_state_signed_from /SE.newton_state_code_from
  eval_mathcomp_recursive_signed_decode SE.eval_recursive_project
  /decode_recursive_newton_state_component.
reflexivity.
Qed.

Lemma eval_recursive_newton_recurrence_from {arity}
    (state : SE.recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity)
    values sparse_state :
  recursive_newton_state_semantics
      (SE.eval_recursive_expression state values)
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      sparse_state ->
  eval_mathcomp_recursive_signed_expression
      (SE.newton_recurrence_from state e1 e2 e3 e4 e5 e6) values =
    NPS.sparse_eval_ring
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      (NPS.newton_next sparse_state).
Proof.
move=> [h0 [h1 [h2 [h3 [h4 h5]]]]].
rewrite /SE.newton_recurrence_from /NPS.newton_next.
rewrite eval_mathcomp_recursive_signed_minus
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  eval_mathcomp_recursive_signed_plus
  eval_mathcomp_recursive_signed_minus
  !eval_mathcomp_recursive_signed_mult.
rewrite NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_add
  NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_add
  NPS.sparse_eval_ring_sub !NPS.sparse_eval_ring_mul.
rewrite !eval_recursive_newton_state_signed_from
  h0 h1 h2 h3 h4 h5
  sparse_eval_ring_recursive_newton_e1
  sparse_eval_ring_recursive_newton_e2
  sparse_eval_ring_recursive_newton_e3
  sparse_eval_ring_recursive_newton_e4
  sparse_eval_ring_recursive_newton_e5
  sparse_eval_ring_recursive_newton_e6.
reflexivity.
Qed.

Lemma eval_recursive_newton_step_from {arity}
    (state : SE.recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity)
    values sparse_state :
  recursive_newton_state_semantics
      (SE.eval_recursive_expression state values)
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      sparse_state ->
  recursive_newton_state_semantics
    (SE.eval_recursive_expression
      (SE.newton_step_from state e1 e2 e3 e4 e5 e6) values)
    (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
    (NPS.newton_step sparse_state).
Proof.
move=> hstate.
have hnext := eval_recursive_newton_recurrence_from hstate.
move: hstate=> [h0 [h1 [h2 [h3 [h4 h5]]]]].
rewrite /recursive_newton_state_semantics
  /decode_recursive_newton_state_component
  /SE.newton_step_from /NPS.newton_step.
rewrite !SE.eval_recursive_inject6 !project_inject.
cbn [vec_pos NPS.newton_s1 NPS.newton_s2 NPS.newton_s3
  NPS.newton_s4 NPS.newton_s5 NPS.newton_s6].
repeat split.
- rewrite /SE.newton_state_code_from SE.eval_recursive_project.
  exact h1.
- rewrite /SE.newton_state_code_from SE.eval_recursive_project.
  exact h2.
- rewrite /SE.newton_state_code_from SE.eval_recursive_project.
  exact h3.
- rewrite /SE.newton_state_code_from SE.eval_recursive_project.
  exact h4.
- rewrite /SE.newton_state_code_from SE.eval_recursive_project.
  exact h5.
- rewrite decode_eval_recursive_signed_code_mathcomp.
  exact hnext.
Qed.

Lemma recursive_elementary_values_weakened {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity)
    state values :
  recursive_elementary_values
      (CE.recursive_signed_weaken e1)
      (CE.recursive_signed_weaken e2)
      (CE.recursive_signed_weaken e3)
      (CE.recursive_signed_weaken e4)
      (CE.recursive_signed_weaken e5)
      (CE.recursive_signed_weaken e6)
      (state ## values) =
    recursive_elementary_values e1 e2 e3 e4 e5 e6 values.
Proof.
rewrite /recursive_elementary_values
  !eval_recursive_signed_weaken.
reflexivity.
Qed.

Definition recursive_newton_state_step_value {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity)
    (values : Vector.t nat arity) (state : nat) : nat :=
  SE.eval_recursive_expression
    (SE.newton_step_from (SE.RecVar pos0)
      (CE.recursive_signed_weaken e1)
      (CE.recursive_signed_weaken e2)
      (CE.recursive_signed_weaken e3)
      (CE.recursive_signed_weaken e4)
      (CE.recursive_signed_weaken e5)
      (CE.recursive_signed_weaken e6))
    (state ## values).

Lemma recursive_newton_state_step_value_semantics {arity}
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity)
    values state sparse_state :
  recursive_newton_state_semantics state
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      sparse_state ->
  recursive_newton_state_semantics
      (recursive_newton_state_step_value
        e1 e2 e3 e4 e5 e6 values state)
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      (NPS.newton_step sparse_state).
Proof.
move=> hstate.
have hstep := @eval_recursive_newton_step_from (S arity)
  (SE.RecVar pos0)
  (CE.recursive_signed_weaken e1)
  (CE.recursive_signed_weaken e2)
  (CE.recursive_signed_weaken e3)
  (CE.recursive_signed_weaken e4)
  (CE.recursive_signed_weaken e5)
  (CE.recursive_signed_weaken e6)
  (state ## values) sparse_state.
cbn [SE.eval_recursive_expression] in hstep.
rewrite !recursive_elementary_values_weakened in hstep.
exact: hstep hstate.
Qed.

Lemma recursive_newton_state_iter_semantics {arity} iterations
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity)
    values state sparse_state :
  recursive_newton_state_semantics state
      (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      sparse_state ->
  recursive_newton_state_semantics
    (prim_min.iter
      (recursive_newton_state_step_value e1 e2 e3 e4 e5 e6 values)
      iterations state)
    (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
    (NPS.newton_iterate iterations sparse_state).
Proof.
revert state sparse_state.
induction iterations as [|iterations ih]; intros state sparse_state hstate.
- exact hstate.
- rewrite prim_min.iter_S /=.
  apply ih.
  exact: recursive_newton_state_step_value_semantics hstate.
Qed.

(** The dynamic recursive Newton program computes exactly the sparse
    polynomial [newton_sparse_power], for arbitrary recursively supplied
    elementary coordinates. *)
Lemma eval_recursive_newton_sparse_power_from {arity}
    (power : SE.recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  mathcomp_zigzag_decode
    (SE.eval_recursive_expression
      (CE.newton_sparse_power_from power e1 e2 e3 e4 e5 e6) values) =
  NPS.sparse_eval_ring
    (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
    (NPS.newton_sparse_power
      (SE.eval_recursive_expression power values)).
Proof.
remember (SE.eval_recursive_expression power values) as power_value
  eqn:hpower.
case: power_value hpower=> [|previous] hpower.
- rewrite /CE.newton_sparse_power_from
    eval_recursive_if_zero -hpower.
  rewrite decode_eval_recursive_signed_code_mathcomp
    eval_mathcomp_recursive_signed_nat
    /NPS.newton_sparse_power NPS.sparse_eval_ring_nsmul
    NPS.sparse_eval_ring_const rmorph1 mulr1.
  reflexivity.
- have hinitial := eval_recursive_newton_initial_state_from
      e1 e2 e3 e4 e5 e6 values.
  have hiter := recursive_newton_state_iter_semantics previous hinitial.
  move: hiter=> [hfirst _].
  rewrite /CE.newton_sparse_power_from
    eval_recursive_if_zero -hpower
    SE.eval_recursive_project eval_recursive_iter
    eval_recursive_minus eval_recursive_const -hpower subn1
    /NPS.newton_sparse_power /=.
  change
    (decode_recursive_newton_state_component
      (prim_min.iter
        (recursive_newton_state_step_value
          e1 e2 e3 e4 e5 e6 values)
        previous
        (SE.eval_recursive_expression
          (SE.newton_initial_state_from e1 e2 e3 e4 e5 e6) values))
      pos0 =
     NPS.sparse_eval_ring
       (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
       (NPS.newton_s1
         (NPS.newton_iterate previous NPS.newton_initial_state))).
  exact hfirst.
Qed.

(* --------------------------------------------------------------------- *)
(* The table-driven Möbius evaluator denotes the sparse orbit polynomial. *)

(** Looking up a block mask in the recursive table is the same operation as
    first looking up the corresponding canonical partition code. *)
Lemma eval_recursive_partition_mask {arity} block
    (partition : SE.recursive_expression arity) values :
  (SE.eval_recursive_expression partition values < 203)%N ->
  SE.eval_recursive_expression
      (CE.recursive_partition_mask block partition) values =
    CE.partition_block_mask
      (nth [::] PS.partition_codes
        (SE.eval_recursive_expression partition values)) block.
Proof.
move=> hpartition.
have hsize :
    (SE.eval_recursive_expression partition values <
      size PS.partition_codes)%N.
  by rewrite -/PS.partition_count PS.partition_count_is_203.
rewrite /CE.recursive_partition_mask eval_recursive_lookup_list
  /CE.partition_block_mask_table.
change
  (nth 0%N
      (map (fun labels => CE.partition_block_mask labels block)
        PS.partition_codes)
      (SE.eval_recursive_expression partition values) =
   CE.partition_block_mask
      (nth [::] PS.partition_codes
        (SE.eval_recursive_expression partition values)) block).
by rewrite (nth_map [::] 0%N
  (fun labels => CE.partition_block_mask labels block) hsize).
Qed.

(** The two natural-valued lookup tables are exactly the positive and
    negative parts of the MathComp integer Möbius weight. *)
Lemma eval_recursive_partition_weight {arity}
    (partition : SE.recursive_expression arity) values :
  (SE.eval_recursive_expression partition values < 203)%N ->
  eval_mathcomp_recursive_signed_expression
      (CE.recursive_partition_weight partition) values =
    (PS.partition_mobius_positive
      (nth [::] PS.partition_codes
        (SE.eval_recursive_expression partition values)))%:Z -
    (PS.partition_mobius_negative
      (nth [::] PS.partition_codes
        (SE.eval_recursive_expression partition values)))%:Z.
Proof.
move=> hpartition.
have hsize :
    (SE.eval_recursive_expression partition values <
      size PS.partition_codes)%N.
  by rewrite -/PS.partition_count PS.partition_count_is_203.
rewrite /eval_mathcomp_recursive_signed_expression
  /CE.recursive_partition_weight
  !eval_recursive_lookup_list
  /CE.partition_mobius_positive_table
  /CE.partition_mobius_negative_table.
change
  ((nth 0%N (map PS.partition_mobius_positive PS.partition_codes)
      (SE.eval_recursive_expression partition values))%:Z -
   (nth 0%N (map PS.partition_mobius_negative PS.partition_codes)
      (SE.eval_recursive_expression partition values))%:Z =
   (PS.partition_mobius_positive
      (nth [::] PS.partition_codes
        (SE.eval_recursive_expression partition values)))%:Z -
   (PS.partition_mobius_negative
      (nth [::] PS.partition_codes
        (SE.eval_recursive_expression partition values)))%:Z).
rewrite (nth_map [::] 0%N PS.partition_mobius_positive hsize).
by rewrite (nth_map [::] 0%N PS.partition_mobius_negative hsize).
Qed.

(** A block factor is one for an inactive block and the already-verified
    Newton sparse power for an active one. *)
Lemma eval_recursive_newton_block_factor_from {arity}
    (mask exponent : SE.recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  eval_mathcomp_recursive_signed_expression
      (CE.recursive_newton_block_factor_from mask exponent
        e1 e2 e3 e4 e5 e6) values =
    match SE.eval_recursive_expression mask values with
    | 0%nat => 1
    | S _ =>
        NPS.sparse_eval_ring
          (recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
          (NPS.newton_sparse_power
            (SE.eval_recursive_expression exponent values))
    end.
Proof.
rewrite /CE.recursive_newton_block_factor_from
  eval_mathcomp_recursive_signed_decode eval_recursive_if_zero.
case hmask: (SE.eval_recursive_expression mask values)=> [|mask_value].
- rewrite decode_eval_recursive_signed_code_mathcomp
    eval_mathcomp_recursive_signed_nat.
  reflexivity.
- exact: eval_recursive_newton_sparse_power_from.
Qed.

Print Assumptions eval_recursive_signed_code_mathcomp.
Print Assumptions eval_mathcomp_recursive_signed_bounded_sum.
Print Assumptions eval_recursive_rename.
Print Assumptions eval_recursive_lookup_list.

End PolynomialFormulasSexticMuRecCollisionSemantics.
