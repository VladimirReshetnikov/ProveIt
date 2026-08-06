(* ===================================================================== *)
(*  Mu-recursive minimization for sextic separating-parameter searches.  *)
(*                                                                       *)
(*  The expensive collision-coefficient compiler is deliberately an      *)
(*  explicit input to the last section.  Everything else in the search   *)
(*  -- Boolean totalization, unbounded minimization, vector coding, and   *)
(*  proof-independent agreement with [first_true_index] -- is compiled    *)
(*  here from concrete [recalg] constructors.                             *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia Vector.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat pos vec.

From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From PolynomialFormulas Require Import
  SexticMuRecComputability SexticSeparatingSelector.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Module PolynomialFormulasSexticMuRecSeparatingSearch.

Module ExistingSelector := PolynomialFormulasSexticSeparatingSelector.

(* --------------------------------------------------------------------- *)
(* A Boolean test compiler with a fixed output convention.               *)

Definition recalg_boolean_spec {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (program : recalg (S arity)) : Prop :=
  forall index values,
    ⟦program⟧ (index ## values) (bool_to_nat (test index values)).

(* [ra_min] searches for an output equal to zero.  A compiled Boolean uses
   zero for false and one for true, so one final [ra_not] gives exactly the
   zero-at-success convention needed by minimization. *)
Definition ra_true_zero {arity : nat} (test_program : recalg (S arity)) :
    recalg (S arity) :=
  ra_comp ra_not (test_program ## vec_nil).

Lemma ra_true_zero_correct {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (test_program : recalg (S arity))
    (Htest : recalg_boolean_spec test test_program)
    index values :
  ⟦ra_true_zero test_program⟧ (index ## values)
    (1 - bool_to_nat (test index values)).
Proof.
  unfold ra_true_zero.
  eapply ra_comp1_val.
  - apply Htest.
  - apply ra_not_val.
Qed.

Lemma bool_to_nat_true b : bool_to_nat b = 1 -> b = true.
Proof. destruct b; cbn; congruence. Qed.

Lemma bool_to_nat_false b : bool_to_nat b = 0 -> b = false.
Proof. destruct b; cbn; congruence. Qed.

Lemma bool_to_nat_eq_one b : bool_to_nat b = 1 <-> b = true.
Proof. destruct b; cbn; intuition congruence. Qed.

Lemma bool_to_nat_eq_zero b : bool_to_nat b = 0 <-> b = false.
Proof. destruct b; cbn; intuition congruence. Qed.

(* --------------------------------------------------------------------- *)
(* Honest unbounded minimization.                                        *)

Definition ra_first_true {arity : nat} (test_program : recalg (S arity)) :
    recalg arity :=
  ra_min (ra_true_zero test_program).

Definition certified_first_true {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (eventually : forall values, exists index, test index values = true)
    (values : Vector.t nat arity) : nat :=
  @ExistingSelector.first_true_index (fun index => test index values)
    (eventually values).

Arguments certified_first_true
  {arity} test eventually values.

Lemma certified_first_trueP {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (eventually : forall values, exists index, test index values = true)
    (values : Vector.t nat arity) :
  test (certified_first_true test eventually values) values = true.
Proof.
  exact (@ExistingSelector.first_true_indexP
    (fun index => test index values) (eventually values)).
Qed.

Lemma certified_first_true_minimal {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (eventually : forall values, exists index, test index values = true)
    (values : Vector.t nat arity) index :
  test index values = true ->
  Nat.le (certified_first_true test eventually values) index.
Proof.
  exact (@ExistingSelector.first_true_index_minimal
    (fun candidate => test candidate values)
    (eventually values) index).
Qed.

Lemma certified_first_true_proof_irrelevant {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (eventually1 eventually2 :
      forall values : Vector.t nat arity,
        exists index, test index values = true)
    values :
  certified_first_true test eventually1 values =
  certified_first_true test eventually2 values.
Proof.
  unfold certified_first_true.
  apply ExistingSelector.first_true_index_proof_irrelevant.
Qed.

Lemma certified_first_true_extensional {arity : nat}
    (left right : nat -> Vector.t nat arity -> bool)
    (left_eventually : forall values, exists index, left index values = true)
    (right_eventually : forall values, exists index, right index values = true)
    (Hext : forall index values, left index values = right index values)
    values :
  certified_first_true left left_eventually values =
  certified_first_true right right_eventually values.
Proof.
  apply Nat.le_antisymm.
  - apply (certified_first_true_minimal left left_eventually values
      (certified_first_true right right_eventually values)).
    rewrite (Hext
      (certified_first_true right right_eventually values) values).
    apply certified_first_trueP.
  - apply (certified_first_true_minimal right right_eventually values
      (certified_first_true left left_eventually values)).
    rewrite <- (Hext
      (certified_first_true left left_eventually values) values).
    apply certified_first_trueP.
Qed.

Theorem ra_first_true_correct {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (test_program : recalg (S arity))
    (Htest : recalg_boolean_spec test test_program)
    (eventually : forall values, exists index, test index values = true)
    values :
  ⟦ra_first_true test_program⟧ values
    (certified_first_true test eventually values).
Proof.
  unfold ra_first_true.
  rewrite ra_rel_fix_min.
  unfold s_min, μ_min.
  split.
  - replace 0 with
      (1 - bool_to_nat
        (test (certified_first_true test eventually values) values)).
    + apply ra_true_zero_correct. exact Htest.
    + rewrite certified_first_trueP. reflexivity.
  - intros index Hindex.
    exists 0.
    replace 1 with
      (1 - bool_to_nat (test index values)).
    + apply ra_true_zero_correct. exact Htest.
    + destruct (test index values) eqn:Hvalue; cbn.
      * exfalso.
        pose proof
          (certified_first_true_minimal test eventually values index Hvalue)
          as Hminimal.
        lia.
      * reflexivity.
Qed.

Definition first_true_vector_relation {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (eventually : forall values, exists index, test index values = true)
    (values : Vector.t nat arity) (out : nat) : Prop :=
  out = certified_first_true test eventually values.

Arguments first_true_vector_relation
  {arity} test eventually values out.

Theorem first_true_vector_relation_murec {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (test_program : recalg (S arity))
    (Htest : recalg_boolean_spec test test_program)
    (eventually : forall values, exists index, test index values = true) :
  MuRec_computable (first_true_vector_relation test eventually).
Proof.
  unfold first_true_vector_relation.
  refine (@recalg_graph_murec arity
    (certified_first_true test eventually)
    (ra_first_true test_program) _).
  apply ra_first_true_correct. exact Htest.
Qed.

(* --------------------------------------------------------------------- *)
(* The same search behind the repository's one-natural vector coding.    *)

Definition ra_first_true_code {arity : nat}
    (test_program : recalg (S arity)) : recalg 1 :=
  ra_comp (ra_first_true test_program) (ra_vec_project arity).

Lemma ra_first_true_code_correct {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (test_program : recalg (S arity))
    (Htest : recalg_boolean_spec test test_program)
    (eventually : forall values, exists index, test index values = true)
    code :
  ⟦ra_first_true_code test_program⟧ (code ## vec_nil)
    (certified_first_true test eventually (project arity code)).
Proof.
  unfold ra_first_true_code.
  exists (project arity code); split.
  - apply ra_first_true_correct. exact Htest.
  - intro variable. rewrite vec_pos_set.
    apply ra_vec_project_val_at.
Qed.

Definition first_true_code_relation {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (eventually : forall values, exists index, test index values = true)
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = certified_first_true test eventually
    (project arity (vec_head code)).

Arguments first_true_code_relation
  {arity} test eventually code out.

Theorem first_true_code_relation_murec {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (test_program : recalg (S arity))
    (Htest : recalg_boolean_spec test test_program)
    (eventually : forall values, exists index, test index values = true) :
  MuRec_computable (first_true_code_relation test eventually).
Proof.
  unfold first_true_code_relation.
  refine (@recalg_graph_murec 1
    (fun code => certified_first_true test eventually
      (project arity (vec_head code)))
    (ra_first_true_code test_program) _).
  intro values. vec split values with code. vec nil values.
  apply ra_first_true_code_correct. exact Htest.
Qed.

Lemma first_true_code_roundtrip {arity : nat}
    (test : nat -> Vector.t nat arity -> bool)
    (eventually : forall values, exists index, test index values = true)
    values out :
  first_true_code_relation test eventually (inject values ## vec_nil) out
  <-> first_true_vector_relation test eventually values out.
Proof.
  unfold first_true_code_relation, first_true_vector_relation.
  cbn [vec_head]. rewrite project_inject. reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Totalization seam for a compiled collision checker.                   *)

Definition ra_drop_index {arity : nat} (program : recalg arity) :
    recalg (S arity) :=
  ra_comp program
    (vec_set_pos (fun variable => ra_proj (pos_nxt variable))).

Lemma ra_drop_index_correct {arity : nat} (program : recalg arity)
    (function : Vector.t nat arity -> nat)
    (Hprogram : forall values, ⟦program⟧ values (function values))
    index values :
  ⟦ra_drop_index program⟧ (index ## values) (function values).
Proof.
  unfold ra_drop_index.
  exists values; split.
  - apply Hprogram.
  - intro variable. rewrite !vec_pos_set.
    change
      (⟦ra_proj (pos_nxt variable)⟧ (index ## values)
        (vec_pos (index ## values) (pos_nxt variable))).
    apply ra_proj_val.
Qed.

Definition ra_guarded_boolean {arity : nat}
    (guard_program : recalg arity)
    (collision_program : recalg (S arity)) : recalg (S arity) :=
  ra_comp ra_ite
    (ra_drop_index guard_program ##
     collision_program ##
     ra_cst_n (S arity) 1 ## vec_nil).

Lemma bool_to_nat_orb left right :
  bool_to_nat (orb left right) =
  ite_rel (bool_to_nat left) (bool_to_nat right) 1.
Proof. destruct left, right; reflexivity. Qed.

Theorem ra_guarded_boolean_correct {arity : nat}
    (guard : Vector.t nat arity -> bool)
    (collision : nat -> Vector.t nat arity -> bool)
    (guard_program : recalg arity)
    (collision_program : recalg (S arity))
    (Hguard : forall values,
      ⟦guard_program⟧ values (bool_to_nat (guard values)))
    (Hcollision : recalg_boolean_spec collision collision_program) :
  recalg_boolean_spec
    (fun index values => orb (guard values) (collision index values))
    (ra_guarded_boolean guard_program collision_program).
Proof.
  intros index values.
  unfold ra_guarded_boolean.
  rewrite bool_to_nat_orb.
  eapply ra_comp3_val.
  - apply ra_drop_index_correct. exact Hguard.
  - apply Hcollision.
  - apply ra_cst_n_val.
  - apply ra_ite_val.
Qed.

Definition guarded_first_true {arity : nat}
    (guard : Vector.t nat arity -> bool)
    (collision : nat -> Vector.t nat arity -> bool)
    (eventually : forall values, exists index,
      orb (guard values) (collision index values) = true) :=
  certified_first_true
    (fun index values => orb (guard values) (collision index values))
    eventually.

Arguments guarded_first_true
  {arity} guard collision eventually values.

Theorem guarded_first_true_vector_relation_murec {arity : nat}
    (guard : Vector.t nat arity -> bool)
    (collision : nat -> Vector.t nat arity -> bool)
    (guard_program : recalg arity)
    (collision_program : recalg (S arity))
    (Hguard : forall values,
      ⟦guard_program⟧ values (bool_to_nat (guard values)))
    (Hcollision : recalg_boolean_spec collision collision_program)
    (eventually : forall values, exists index,
      orb (guard values) (collision index values) = true) :
  MuRec_computable
    (first_true_vector_relation
      (fun index values => orb (guard values) (collision index values))
      eventually).
Proof.
  apply first_true_vector_relation_murec with
    (test_program := ra_guarded_boolean guard_program collision_program).
  apply ra_guarded_boolean_correct; assumption.
Qed.

Theorem guarded_first_true_code_relation_murec {arity : nat}
    (guard : Vector.t nat arity -> bool)
    (collision : nat -> Vector.t nat arity -> bool)
    (guard_program : recalg arity)
    (collision_program : recalg (S arity))
    (Hguard : forall values,
      ⟦guard_program⟧ values (bool_to_nat (guard values)))
    (Hcollision : recalg_boolean_spec collision collision_program)
    (eventually : forall values, exists index,
      orb (guard values) (collision index values) = true) :
  MuRec_computable
    (first_true_code_relation
      (fun index values => orb (guard values) (collision index values))
      eventually).
Proof.
  apply first_true_code_relation_murec with
    (test_program := ra_guarded_boolean guard_program collision_program).
  apply ra_guarded_boolean_correct; assumption.
Qed.

End PolynomialFormulasSexticMuRecSeparatingSearch.
