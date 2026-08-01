(** Generic axiom schemes underlying arithmetic induction theories. *)

From Stdlib Require Import Arith.PeanoNat Logic.Classical_Prop
  Logic.FunctionalExtensionality.
From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Eq Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics RewriteClosure OperatorSemantics ModelTheory Elementary.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Model Hierarchy.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic Theory
  Functions Definability.
From Foundation.FirstOrder.Arithmetic.TA Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition arithmetic_predicate_instance {X n}
    (phi : semiformula oring_language X 1)
    (t : semiterm oring_language X n) :
    semiformula oring_language X n :=
  semiformula_substitute (fun _ : Fin.t 1 => t) phi.

Definition arithmetic_successor_induction {X}
    (phi : semiformula oring_language X 1) :
    formula oring_language X :=
  semiformula_imp
    (arithmetic_predicate_instance phi arithmetic_zero_term)
    (semiformula_imp
      (Semiformula_all
        (semiformula_imp phi
          (arithmetic_predicate_instance phi
            (arithmetic_add_one_term (Semiterm_bvar Fin.F1)))))
      (Semiformula_all phi)).

Definition arithmetic_order_induction {X}
    (phi : semiformula oring_language X 1) :
    formula oring_language X :=
  semiformula_imp
    (Semiformula_all
      (semiformula_imp
        (arithmetic_bounded_all (Semiterm_bvar (Fin.FS Fin.F1))
          (arithmetic_predicate_instance phi (Semiterm_bvar Fin.F1)))
        phi))
    (Semiformula_all phi).

Definition arithmetic_least_number {X}
    (phi : semiformula oring_language X 1) :
    formula oring_language X :=
  semiformula_imp
    (Semiformula_exists phi)
    (Semiformula_exists
      (Semiformula_and phi
        (arithmetic_bounded_all (Semiterm_bvar (Fin.FS Fin.F1))
          (semiformula_neg
            (arithmetic_predicate_instance phi
              (Semiterm_bvar Fin.F1)))))).

Definition arithmetic_predicate_holds {M X}
    (Str : first_order_structure oring_language M)
    (f : X -> M) (phi : semiformula oring_language X 1)
    (x : M) : Prop :=
  semiformula_eval Str (fun _ : Fin.t 1 => x) f phi.

Definition arithmetic_predecessor_formula
    (phi : arithmetic_semiproposition 1) :
    arithmetic_semiproposition 1 :=
  arithmetic_bounded_all (Semiterm_bvar (Fin.FS Fin.F1))
    (arithmetic_predicate_instance phi (Semiterm_bvar Fin.F1)).

Theorem arithmetic_predecessor_formula_hierarchy : forall pol rank phi,
  arithmetic_hierarchy nat pol rank 1 phi ->
  arithmetic_hierarchy nat pol rank 1
    (arithmetic_predecessor_formula phi).
Proof.
  intros pol rank phi Hphi.
  unfold arithmetic_predecessor_formula.
  assert (Hpositive : semiterm_positive
      (@Semiterm_bvar oring_language nat 2 (Fin.FS Fin.F1))).
  { apply (proj2 (semiterm_positive_bvar oring_language nat
      (Fin.FS Fin.F1))). simpl. constructor. }
  apply (proj2 (@arithmetic_hierarchy_bounded_all_iff nat pol rank 1
    (Semiterm_bvar (Fin.FS Fin.F1))
    (arithmetic_predicate_instance phi (Semiterm_bvar Fin.F1)) Hpositive)).
  unfold arithmetic_predicate_instance, semiformula_substitute.
  now apply arithmetic_hierarchy_rewrite.
Qed.

Lemma arithmetic_predicate_instance_eval : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M)
    (phi : semiformula oring_language X 1)
    (t : semiterm oring_language X n),
  semiformula_eval Str b f (arithmetic_predicate_instance phi t) <->
  arithmetic_predicate_holds Str f phi (semiterm_val Str b f t).
Proof.
  intros. unfold arithmetic_predicate_instance, arithmetic_predicate_holds,
    semiformula_substitute.
  rewrite semiformula_eval_substitute. reflexivity.
Qed.

Lemma fin_env_cons_empty_eq_constant : forall M (x : M)
    (b : Fin.t 0 -> M),
  fin_env_cons x b = (fun _ : Fin.t 1 => x).
Proof.
  intros M x b. apply functional_extensionality. intro i.
  refine (@Fin.caseS' 0 i (fun j => fin_env_cons x b j = x)
    eq_refl _).
  intros j. inversion j.
Qed.

Lemma arithmetic_all_predicate_eval : forall M X
    (Str : first_order_structure oring_language M)
    (b : Fin.t 0 -> M) (f : X -> M)
    (phi : semiformula oring_language X 1),
  semiformula_eval Str b f (Semiformula_all phi) <->
  forall x, arithmetic_predicate_holds Str f phi x.
Proof.
  intros. simpl. split; intros H x.
  - unfold arithmetic_predicate_holds.
    rewrite <- (fin_env_cons_empty_eq_constant x b). apply H.
  - rewrite (fin_env_cons_empty_eq_constant x b). apply H.
Qed.

Lemma arithmetic_successor_step_eval : forall M X
    (Str : first_order_structure oring_language M)
    (b : Fin.t 0 -> M) (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1),
  structure_interprets_oring Str oring_language_structure O ->
  semiformula_eval Str b f
    (Semiformula_all
      (semiformula_imp phi
        (arithmetic_predicate_instance phi
          (arithmetic_add_one_term (Semiterm_bvar Fin.F1))))) <->
  forall x, arithmetic_predicate_holds Str f phi x ->
    arithmetic_predicate_holds Str f phi
      (oring_add O x (oring_one O)).
Proof.
  intros M X Str b f O phi Horing. split.
  - intros H x Hx. specialize (H x).
    rewrite semiformula_eval_imp in H.
    rewrite (fin_env_cons_empty_eq_constant x b) in H.
    pose proof (@arithmetic_add_one_term_val M X 1 Str
      (fun _ : Fin.t 1 => x) f O (Semiterm_bvar Fin.F1) Horing) as Hval.
    change (semiterm_val Str (fun _ : Fin.t 1 => x) f
      (arithmetic_add_one_term (Semiterm_bvar Fin.F1)) =
      oring_add O x (oring_one O)) in Hval.
    rewrite <- Hval.
    apply (proj1 (arithmetic_predicate_instance_eval
      Str (fun _ : Fin.t 1 => x) f phi
      (arithmetic_add_one_term (Semiterm_bvar Fin.F1)))).
    apply H. exact Hx.
  - intros H x. rewrite semiformula_eval_imp.
    rewrite (fin_env_cons_empty_eq_constant x b).
    intro Hphi.
    apply (proj2 (arithmetic_predicate_instance_eval
      Str (fun _ : Fin.t 1 => x) f phi
      (arithmetic_add_one_term (Semiterm_bvar Fin.F1)))).
    pose proof (@arithmetic_add_one_term_val M X 1 Str
      (fun _ : Fin.t 1 => x) f O (Semiterm_bvar Fin.F1) Horing) as Hval.
    change (semiterm_val Str (fun _ : Fin.t 1 => x) f
      (arithmetic_add_one_term (Semiterm_bvar Fin.F1)) =
      oring_add O x (oring_one O)) in Hval.
    rewrite Hval.
    apply H. exact Hphi.
Qed.

Theorem arithmetic_successor_induction_eval : forall M X
    (Str : first_order_structure oring_language M)
    (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1),
  structure_interprets_oring Str oring_language_structure O ->
  formula_eval Str f (arithmetic_successor_induction phi) <->
  (arithmetic_predicate_holds Str f phi (oring_zero O) ->
   (forall x, arithmetic_predicate_holds Str f phi x ->
      arithmetic_predicate_holds Str f phi
        (oring_add O x (oring_one O))) ->
   forall x, arithmetic_predicate_holds Str f phi x).
Proof.
  intros M X Str f O phi Horing.
  unfold formula_eval, arithmetic_successor_induction.
  rewrite !semiformula_eval_imp.
  setoid_rewrite arithmetic_predicate_instance_eval.
  rewrite (@arithmetic_zero_term_val M X 0 Str _ f O Horing).
  rewrite (@arithmetic_successor_step_eval M X Str _ f O phi Horing).
  rewrite arithmetic_all_predicate_eval. tauto.
Qed.

Lemma arithmetic_bounded_all_eval : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M)
    (t : semiterm oring_language X (S n))
    (p : semiformula oring_language X (S n)),
  structure_interprets_oring Str oring_language_structure O ->
  semiformula_eval Str b f (arithmetic_bounded_all t p) <->
  forall x,
    oring_lt O x (semiterm_val Str (fin_env_cons x b) f t) ->
    semiformula_eval Str (fin_env_cons x b) f p.
Proof.
  intros M X n Str b f O t p Horing.
  unfold arithmetic_bounded_all, arithmetic_lt_guard.
  rewrite semiformula_eval_bounded_all.
  setoid_rewrite semiformula_eval_operator_apply.
  setoid_rewrite semiterm_val_fin_two.
  setoid_rewrite (structure_relation_operator (structure_oring_lt Horing)).
  reflexivity.
Qed.

Lemma arithmetic_predecessors_eval : forall M X
    (Str : first_order_structure oring_language M)
    (b : Fin.t 0 -> M) (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1) x,
  structure_interprets_oring Str oring_language_structure O ->
  semiformula_eval Str (fin_env_cons x b) f
    (arithmetic_bounded_all (Semiterm_bvar (Fin.FS Fin.F1))
      (arithmetic_predicate_instance phi (Semiterm_bvar Fin.F1))) <->
  forall y, oring_lt O y x -> arithmetic_predicate_holds Str f phi y.
Proof.
  intros M X Str b f O phi x Horing.
  rewrite (@arithmetic_bounded_all_eval M X 1 Str
    (fin_env_cons x b) f O _ _ Horing).
  split; intros H y Hy.
  - specialize (H y). simpl in H.
    apply (proj1 (arithmetic_predicate_instance_eval Str
      (fin_env_cons y (fin_env_cons x b)) f phi (Semiterm_bvar Fin.F1))).
    simpl. apply H. exact Hy.
  - apply (proj2 (arithmetic_predicate_instance_eval Str
      (fin_env_cons y (fin_env_cons x b)) f phi (Semiterm_bvar Fin.F1))).
    simpl. apply H. exact Hy.
Qed.

Theorem arithmetic_predecessor_formula_eval : forall M
    (Str : first_order_structure oring_language M)
    (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  forall (phi : arithmetic_semiproposition 1) (f : nat -> M) x,
  arithmetic_predicate_holds Str f
    (arithmetic_predecessor_formula phi) x <->
  forall y, oring_lt O y x -> arithmetic_predicate_holds Str f phi y.
Proof.
  intros M Str O Horing phi f x.
  unfold arithmetic_predecessor_formula, arithmetic_predicate_holds.
  pose (b := fun i : Fin.t 0 => match i with end : M).
  rewrite <- (fin_env_cons_empty_eq_constant x b).
  apply (@arithmetic_predecessors_eval M nat Str b f O phi x Horing).
Qed.

Lemma arithmetic_order_step_eval : forall M X
    (Str : first_order_structure oring_language M)
    (b : Fin.t 0 -> M) (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1),
  structure_interprets_oring Str oring_language_structure O ->
  semiformula_eval Str b f
    (Semiformula_all
      (semiformula_imp
        (arithmetic_bounded_all (Semiterm_bvar (Fin.FS Fin.F1))
          (arithmetic_predicate_instance phi (Semiterm_bvar Fin.F1)))
        phi)) <->
  forall x,
    (forall y, oring_lt O y x ->
      arithmetic_predicate_holds Str f phi y) ->
    arithmetic_predicate_holds Str f phi x.
Proof.
  intros M X Str b f O phi Horing. split.
  - intros H x Hpred. specialize (H x).
    rewrite semiformula_eval_imp in H.
    unfold arithmetic_predicate_holds.
    rewrite <- (fin_env_cons_empty_eq_constant x b).
    apply H.
    apply (proj2 (@arithmetic_predecessors_eval
      M X Str b f O phi x Horing)). exact Hpred.
  - intros H x. rewrite semiformula_eval_imp. intro Hpred.
    specialize (H x) as Hx. unfold arithmetic_predicate_holds in Hx.
    rewrite (fin_env_cons_empty_eq_constant x b).
    apply Hx. apply (proj1 (@arithmetic_predecessors_eval
      M X Str b f O phi x Horing)). exact Hpred.
Qed.

Theorem arithmetic_order_induction_eval : forall M X
    (Str : first_order_structure oring_language M)
    (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1),
  structure_interprets_oring Str oring_language_structure O ->
  formula_eval Str f (arithmetic_order_induction phi) <->
  ((forall x,
      (forall y, oring_lt O y x ->
        arithmetic_predicate_holds Str f phi y) ->
      arithmetic_predicate_holds Str f phi x) ->
    forall x, arithmetic_predicate_holds Str f phi x).
Proof.
  intros M X Str f O phi Horing.
  unfold formula_eval, arithmetic_order_induction.
  rewrite semiformula_eval_imp.
  rewrite (@arithmetic_order_step_eval M X Str _ f O phi Horing).
  rewrite arithmetic_all_predicate_eval. tauto.
Qed.

Lemma arithmetic_exists_predicate_eval : forall M X
    (Str : first_order_structure oring_language M)
    (b : Fin.t 0 -> M) (f : X -> M)
    (phi : semiformula oring_language X 1),
  semiformula_eval Str b f (Semiformula_exists phi) <->
  exists x, arithmetic_predicate_holds Str f phi x.
Proof.
  intros. simpl. split; intros [x Hx]; exists x.
  - unfold arithmetic_predicate_holds.
    rewrite <- (fin_env_cons_empty_eq_constant x b). exact Hx.
  - rewrite (fin_env_cons_empty_eq_constant x b). exact Hx.
Qed.

Lemma arithmetic_no_predecessors_eval : forall M X
    (Str : first_order_structure oring_language M)
    (b : Fin.t 0 -> M) (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1) x,
  structure_interprets_oring Str oring_language_structure O ->
  semiformula_eval Str (fin_env_cons x b) f
    (arithmetic_bounded_all (Semiterm_bvar (Fin.FS Fin.F1))
      (semiformula_neg
        (arithmetic_predicate_instance phi (Semiterm_bvar Fin.F1)))) <->
  forall y, oring_lt O y x ->
    ~ arithmetic_predicate_holds Str f phi y.
Proof.
  intros M X Str b f O phi x Horing.
  rewrite (@arithmetic_bounded_all_eval M X 1 Str
    (fin_env_cons x b) f O _ _ Horing).
  split.
  - intros H y Hy. specialize (H y). simpl in H.
    specialize (H Hy). rewrite semiformula_eval_neg in H.
    intro Hphi. apply H.
    apply (proj2 (arithmetic_predicate_instance_eval Str
      (fin_env_cons y (fin_env_cons x b)) f phi (Semiterm_bvar Fin.F1))).
    simpl. exact Hphi.
  - intros H y Hy. simpl.
    rewrite semiformula_eval_neg. intro Hphi.
    apply (H y Hy).
    apply (proj1 (arithmetic_predicate_instance_eval Str
      (fin_env_cons y (fin_env_cons x b)) f phi (Semiterm_bvar Fin.F1))).
    simpl. exact Hphi.
Qed.

Lemma arithmetic_least_witness_eval : forall M X
    (Str : first_order_structure oring_language M)
    (b : Fin.t 0 -> M) (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1),
  structure_interprets_oring Str oring_language_structure O ->
  semiformula_eval Str b f
    (Semiformula_exists
      (Semiformula_and phi
        (arithmetic_bounded_all (Semiterm_bvar (Fin.FS Fin.F1))
          (semiformula_neg
            (arithmetic_predicate_instance phi
              (Semiterm_bvar Fin.F1)))))) <->
  exists x, arithmetic_predicate_holds Str f phi x /\
    forall y, oring_lt O y x ->
      ~ arithmetic_predicate_holds Str f phi y.
Proof.
  intros M X Str b f O phi Horing. simpl. split.
  - intros [x [Hx Hmin]]. exists x. split.
    + unfold arithmetic_predicate_holds.
      rewrite <- (fin_env_cons_empty_eq_constant x b). exact Hx.
    + apply (proj1 (@arithmetic_no_predecessors_eval
        M X Str b f O phi x Horing)). exact Hmin.
  - intros [x [Hx Hmin]]. exists x. split.
    + rewrite (fin_env_cons_empty_eq_constant x b). exact Hx.
    + apply (proj2 (@arithmetic_no_predecessors_eval
        M X Str b f O phi x Horing)). exact Hmin.
Qed.

Theorem arithmetic_least_number_eval : forall M X
    (Str : first_order_structure oring_language M)
    (f : X -> M) (O : oring_carrier M)
    (phi : semiformula oring_language X 1),
  structure_interprets_oring Str oring_language_structure O ->
  formula_eval Str f (arithmetic_least_number phi) <->
  ((exists x, arithmetic_predicate_holds Str f phi x) ->
   exists x, arithmetic_predicate_holds Str f phi x /\
     forall y, oring_lt O y x ->
       ~ arithmetic_predicate_holds Str f phi y).
Proof.
  intros M X Str f O phi Horing.
  unfold formula_eval, arithmetic_least_number.
  rewrite semiformula_eval_imp, arithmetic_exists_predicate_eval.
  rewrite (@arithmetic_least_witness_eval M X Str _ f O phi Horing).
  tauto.
Qed.

Definition first_order_axiom_scheme {L : language} {I : Type}
    (C : I -> Prop) (axiom : I -> sentence L) : theory L :=
  fun sigma => exists i, C i /\ sigma = axiom i.

Definition first_order_theory_union {L : language}
    (T U : theory L) : theory L :=
  fun sigma => T sigma \/ U sigma.

Lemma first_order_theory_union_subset_left : forall L
    (T U : theory L) sigma,
  T sigma -> first_order_theory_union T U sigma.
Proof. intros L T U sigma HT. now left. Qed.

Lemma first_order_theory_union_subset_right : forall L
    (T U : theory L) sigma,
  U sigma -> first_order_theory_union T U sigma.
Proof. intros L T U sigma HU. now right. Qed.

Theorem first_order_theory_weaker_than_union_left : forall L
    (T U : theory L),
  generic_weaker_than
    (first_order_theory_entailment L) (first_order_theory_entailment L)
    T (first_order_theory_union T U).
Proof.
  intros L T U. apply first_order_theory_weaker_of_subset.
  intros sigma HT. now left.
Qed.

Theorem first_order_theory_weaker_than_union_right : forall L
    (T U : theory L),
  generic_weaker_than
    (first_order_theory_entailment L) (first_order_theory_entailment L)
    U (first_order_theory_union T U).
Proof.
  intros L T U. apply first_order_theory_weaker_of_subset.
  intros sigma HU. now right.
Qed.

Lemma first_order_axiom_scheme_intro : forall L I
    (C : I -> Prop) (axiom : I -> sentence L) i,
  C i -> first_order_axiom_scheme C axiom (axiom i).
Proof.
  intros L I C axiom i Hi. exists i. now split.
Qed.

Lemma first_order_axiom_scheme_subset : forall L I
    (C D : I -> Prop) (axiom : I -> sentence L),
  (forall i, C i -> D i) ->
  forall sigma, first_order_axiom_scheme C axiom sigma ->
    first_order_axiom_scheme D axiom sigma.
Proof.
  intros L I C D axiom HCD sigma [i [Hi ->]].
  exists i. split; [now apply HCD | reflexivity].
Qed.

Lemma first_order_theory_union_mono_right : forall L
    (T U V : theory L),
  (forall sigma, U sigma -> V sigma) ->
  forall sigma, first_order_theory_union T U sigma ->
    first_order_theory_union T V sigma.
Proof.
  intros L T U V HUV sigma [HT | HU].
  - now left.
  - right. now apply HUV.
Qed.

Lemma first_order_scheme_union_subset : forall L I
    (T : theory L) (C D : I -> Prop) (axiom : I -> sentence L),
  (forall i, C i -> D i) ->
  forall sigma,
    first_order_theory_union T (first_order_axiom_scheme C axiom) sigma ->
    first_order_theory_union T (first_order_axiom_scheme D axiom) sigma.
Proof.
  intros L I T C D axiom HCD.
  apply first_order_theory_union_mono_right.
  now apply first_order_axiom_scheme_subset.
Qed.

Theorem first_order_scheme_union_weaker : forall L I
    (T : theory L) (C D : I -> Prop) (axiom : I -> sentence L),
  (forall i, C i -> D i) ->
  generic_weaker_than
    (first_order_theory_entailment L) (first_order_theory_entailment L)
    (first_order_theory_union T (first_order_axiom_scheme C axiom))
    (first_order_theory_union T (first_order_axiom_scheme D axiom)).
Proof.
  intros L I T C D axiom HCD.
  apply first_order_theory_weaker_of_subset.
  now apply first_order_scheme_union_subset.
Qed.

Definition arithmetic_induction_scheme
    (C : semiproposition oring_language 1 -> Prop)
    (induction_axiom : semiproposition oring_language 1 ->
      sentence oring_language) : theory oring_language :=
  first_order_axiom_scheme C induction_axiom.

Lemma arithmetic_induction_scheme_intro : forall C induction_axiom phi,
  C phi -> arithmetic_induction_scheme C induction_axiom
    (induction_axiom phi).
Proof.
  intros C induction_axiom phi Hphi.
  exists phi. split; [exact Hphi | reflexivity].
Qed.

Lemma arithmetic_induction_scheme_subset : forall C D induction_axiom,
  (forall phi, C phi -> D phi) ->
  forall sigma,
    arithmetic_induction_scheme C induction_axiom sigma ->
    arithmetic_induction_scheme D induction_axiom sigma.
Proof.
  intros. eapply first_order_axiom_scheme_subset; eauto.
Qed.

Definition arithmetic_successor_induction_scheme
    (C : arithmetic_semiproposition 1 -> Prop) : theory oring_language :=
  first_order_axiom_scheme C
    (fun phi => semiformula_universal_closure
      (arithmetic_successor_induction phi)).

Definition arithmetic_induction_theory (T : theory oring_language)
    (C : arithmetic_semiproposition 1 -> Prop) : theory oring_language :=
  first_order_theory_union T (arithmetic_successor_induction_scheme C).

Definition arithmetic_open_induction_theory (T : theory oring_language) :
    theory oring_language :=
  arithmetic_induction_theory T (@semiformula_open oring_language nat 1).

Definition arithmetic_hierarchy_induction_theory
    (T : theory oring_language) (pol : bool) (k : nat) :
    theory oring_language :=
  arithmetic_induction_theory T
    (fun phi => arithmetic_hierarchy nat pol k 1 phi).

Definition arithmetic_sigma_induction_theory
    (T : theory oring_language) (k : nat) : theory oring_language :=
  arithmetic_hierarchy_induction_theory T arithmetic_sigma k.

Definition arithmetic_peano_theory (T : theory oring_language) :
    theory oring_language :=
  arithmetic_induction_theory T (fun _ => True).

(** The source fixes PA-minus as the base of every named induction theory.
    Keeping the generic constructors above exposes the stronger reusable API;
    these aliases are its exact concrete specializations. *)
Definition arithmetic_iopen : theory oring_language :=
  arithmetic_open_induction_theory peano_minus_axiom.

Definition arithmetic_induction_on_hierarchy (pol : bool) (k : nat) :
    theory oring_language :=
  arithmetic_hierarchy_induction_theory peano_minus_axiom pol k.

Definition arithmetic_isigma (k : nat) : theory oring_language :=
  arithmetic_induction_on_hierarchy arithmetic_sigma k.

Definition arithmetic_ipi (k : nat) : theory oring_language :=
  arithmetic_induction_on_hierarchy arithmetic_pi k.

Definition first_order_peano_arithmetic : theory oring_language :=
  arithmetic_peano_theory peano_minus_axiom.

Lemma arithmetic_successor_induction_scheme_intro : forall C phi,
  C phi -> arithmetic_successor_induction_scheme C
    (semiformula_universal_closure
      (arithmetic_successor_induction phi)).
Proof.
  intros C phi Hphi. exists phi. split; [exact Hphi | reflexivity].
Qed.

Lemma arithmetic_successor_induction_scheme_subset : forall C D,
  (forall phi, C phi -> D phi) ->
  forall sigma, arithmetic_successor_induction_scheme C sigma ->
    arithmetic_successor_induction_scheme D sigma.
Proof.
  intros. eapply first_order_axiom_scheme_subset; eauto.
Qed.

Lemma arithmetic_induction_theory_subset : forall T C D,
  (forall phi, C phi -> D phi) ->
  forall sigma, arithmetic_induction_theory T C sigma ->
    arithmetic_induction_theory T D sigma.
Proof.
  intros T C D HCD.
  apply first_order_theory_union_mono_right.
  now apply arithmetic_successor_induction_scheme_subset.
Qed.

Theorem arithmetic_induction_theory_weaker : forall T C D,
  (forall phi, C phi -> D phi) ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_induction_theory T C)
    (arithmetic_induction_theory T D).
Proof.
  intros. apply first_order_theory_weaker_of_subset.
  now apply arithmetic_induction_theory_subset.
Qed.

Lemma arithmetic_sigma_induction_subset_mono : forall T k l,
  k <= l -> forall sigma,
  arithmetic_sigma_induction_theory T k sigma ->
  arithmetic_sigma_induction_theory T l sigma.
Proof.
  intros T k l Hkl. apply arithmetic_induction_theory_subset.
  intros phi Hphi. now apply arithmetic_hierarchy_mono with (s := k).
Qed.

Theorem arithmetic_sigma_induction_weaker_mono : forall T k l,
  k <= l ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_sigma_induction_theory T k)
    (arithmetic_sigma_induction_theory T l).
Proof.
  intros. apply first_order_theory_weaker_of_subset.
  now apply arithmetic_sigma_induction_subset_mono.
Qed.

Lemma arithmetic_open_induction_subset_sigma_zero : forall T sigma,
  arithmetic_open_induction_theory T sigma ->
  arithmetic_sigma_induction_theory T 0 sigma.
Proof.
  intro T. apply arithmetic_induction_theory_subset.
  intros phi Hopen. now apply arithmetic_hierarchy_of_open.
Qed.

Lemma arithmetic_open_induction_subset_hierarchy : forall T pol k sigma,
  arithmetic_open_induction_theory T sigma ->
  arithmetic_hierarchy_induction_theory T pol k sigma.
Proof.
  intros T pol k. apply arithmetic_induction_theory_subset.
  intros phi Hopen. now apply arithmetic_hierarchy_of_open.
Qed.

Lemma arithmetic_sigma_induction_subset_peano : forall T k sigma,
  arithmetic_sigma_induction_theory T k sigma ->
  arithmetic_peano_theory T sigma.
Proof.
  intros T k. apply arithmetic_induction_theory_subset.
  intros phi Hphi. exact I.
Qed.

(** * Concrete PA-minus induction hierarchy *)

Lemma peano_minus_subset_iopen : forall sigma,
  peano_minus_axiom sigma -> arithmetic_iopen sigma.
Proof.
  intros sigma Hsigma. now left.
Qed.

Theorem peano_minus_weaker_than_iopen :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    peano_minus_axiom arithmetic_iopen.
Proof.
  apply first_order_theory_weaker_of_subset.
  exact peano_minus_subset_iopen.
Qed.

Lemma arithmetic_iopen_subset_induction_on_hierarchy : forall pol k sigma,
  arithmetic_iopen sigma -> arithmetic_induction_on_hierarchy pol k sigma.
Proof.
  intros pol k. exact (arithmetic_open_induction_subset_hierarchy
    (T := peano_minus_axiom) pol k).
Qed.

Theorem arithmetic_iopen_weaker_than_induction_on_hierarchy : forall pol k,
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    arithmetic_iopen (arithmetic_induction_on_hierarchy pol k).
Proof.
  intros pol k. apply first_order_theory_weaker_of_subset.
  exact (arithmetic_iopen_subset_induction_on_hierarchy pol k).
Qed.

Lemma arithmetic_isigma_subset_mono : forall k l,
  k <= l -> forall sigma,
  arithmetic_isigma k sigma -> arithmetic_isigma l sigma.
Proof.
  intros k l Hkl. exact (arithmetic_sigma_induction_subset_mono
    (T := peano_minus_axiom) Hkl).
Qed.

Theorem arithmetic_isigma_weaker_mono : forall k l,
  k <= l ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_isigma k) (arithmetic_isigma l).
Proof.
  intros k l Hkl. apply first_order_theory_weaker_of_subset.
  exact (arithmetic_isigma_subset_mono Hkl).
Qed.

Lemma arithmetic_iopen_subset_isigma_zero : forall sigma,
  arithmetic_iopen sigma -> arithmetic_isigma 0 sigma.
Proof.
  exact (arithmetic_open_induction_subset_sigma_zero
    (T := peano_minus_axiom)).
Qed.

Theorem arithmetic_iopen_weaker_than_isigma_zero :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    arithmetic_iopen (arithmetic_isigma 0).
Proof.
  apply first_order_theory_weaker_of_subset.
  exact arithmetic_iopen_subset_isigma_zero.
Qed.

Lemma arithmetic_isigma_subset_peano : forall k sigma,
  arithmetic_isigma k sigma -> first_order_peano_arithmetic sigma.
Proof.
  exact (arithmetic_sigma_induction_subset_peano
    (T := peano_minus_axiom)).
Qed.

Theorem arithmetic_isigma_weaker_than_peano : forall k,
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_isigma k) first_order_peano_arithmetic.
Proof.
  intro k. apply first_order_theory_weaker_of_subset.
  exact (arithmetic_isigma_subset_peano (k := k)).
Qed.

Corollary arithmetic_isigma_zero_weaker_than_isigma_one :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_isigma 0) (arithmetic_isigma 1).
Proof. apply arithmetic_isigma_weaker_mono. now repeat constructor. Qed.

Corollary arithmetic_isigma_one_weaker_than_peano :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_isigma 1) first_order_peano_arithmetic.
Proof. apply arithmetic_isigma_weaker_than_peano. Qed.

Lemma arithmetic_induction_theory_proves_equality : forall T C,
  first_order_theory_proves_equality T oring_language_eq_operator ->
  first_order_theory_proves_equality
    (arithmetic_induction_theory T C) oring_language_eq_operator.
Proof.
  intros T C Heq sigma Hsigma.
  apply (generic_weaker_subset
    (first_order_theory_weaker_than_union_left T
      (arithmetic_successor_induction_scheme C)) sigma).
  exact (Heq sigma Hsigma).
Qed.

Lemma arithmetic_induction_on_hierarchy_proves_equality : forall pol k,
  first_order_theory_proves_equality
    (arithmetic_induction_on_hierarchy pol k)
    oring_language_eq_operator.
Proof.
  intros pol k. apply arithmetic_induction_theory_proves_equality.
  exact peano_minus_proves_equality.
Qed.

Lemma arithmetic_iopen_proves_equality :
  first_order_theory_proves_equality arithmetic_iopen
    oring_language_eq_operator.
Proof.
  apply arithmetic_induction_theory_proves_equality.
  exact peano_minus_proves_equality.
Qed.

Theorem arithmetic_equality_weaker_than_induction_on_hierarchy :
    forall pol k,
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (@first_order_equality_axiom oring_language
      oring_language_eq_operator)
    (arithmetic_induction_on_hierarchy pol k).
Proof.
  intros pol k.
  apply (arithmetic_theory_weaker_of_models
    (arithmetic_induction_on_hierarchy_proves_equality pol k)).
  intros m O Horing Hmodels.
  exact (first_order_model_models_equality_theory_of_interprets_eq
    (structure_oring_eq Horing)).
Qed.

Theorem arithmetic_equality_weaker_than_iopen :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (@first_order_equality_axiom oring_language
      oring_language_eq_operator) arithmetic_iopen.
Proof.
  apply (arithmetic_theory_weaker_of_models
    arithmetic_iopen_proves_equality).
  intros m O Horing Hmodels.
  exact (first_order_model_models_equality_theory_of_interprets_eq
    (structure_oring_eq Horing)).
Qed.

Theorem semiformula_universal_closure_intro : forall L M
    (Str : first_order_structure L M) (p : proposition L),
  inhabited M ->
  (forall f : nat -> M, formula_eval Str f p) ->
  sentence_realize Str (semiformula_universal_closure p).
Proof.
  intros L M Str p [d] Hall.
  apply (proj1 (@first_order_sentence_embed_eval L M Str
    (fun _ => d) (semiformula_universal_closure p))).
  unfold first_order_sentence_embed.
  rewrite semiformula_emb_universal_closure.
  unfold formula_eval, semiformula_universal_closure_open.
  apply (proj2 (@semiformula_eval_all_closure L M nat
    (semiformula_free_bound p) Str
    (fun i : Fin.t 0 => match i with end) (fun _ => d)
    (semiformula_fix_all_free p))).
  intro e. unfold semiformula_fix_all_free.
  rewrite semiformula_eval_rewrite.
  set (g := fun x => semiterm_val Str e (fun _ => d)
    (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
      (Semiterm_fvar x))).
  refine (proj1 (@semiformula_eval_bound_extensional L M nat 0 Str
    (fun i : Fin.t 0 => match i with end)
    (fun i : Fin.t 0 => semiterm_val Str e (fun _ => d)
      (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
        (Semiterm_bvar i))) g p _) (Hall g)).
  intro i. inversion i.
Qed.

Theorem semiformula_universal_closure_elim : forall L M
    (Str : first_order_structure L M) (p : proposition L) (f : nat -> M),
  sentence_realize Str (semiformula_universal_closure p) ->
  formula_eval Str f p.
Proof.
  intros L M Str p f Hreal.
  pose proof (proj2 (@first_order_sentence_embed_eval L M Str f
    (semiformula_universal_closure p)) Hreal) as Hopen.
  unfold first_order_sentence_embed in Hopen.
  rewrite semiformula_emb_universal_closure in Hopen.
  unfold semiformula_universal_closure_open in Hopen.
  pose proof (proj1 (@semiformula_eval_all_closure L M nat
    (semiformula_free_bound p) Str
    (fun i : Fin.t 0 => match i with end) f
    (semiformula_fix_all_free p)) Hopen) as Hall.
  specialize (Hall (fun i => f (fin_value i))).
  unfold semiformula_fix_all_free in Hall.
  rewrite semiformula_eval_rewrite in Hall.
  unfold formula_eval.
  assert (Hfree : forall x, semiformula_free_occurs x p ->
      (fun y => semiterm_val Str (fun i => f (fin_value i)) f
        (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
          (Semiterm_fvar y))) x = f x).
  { intros x Hx.
    pose proof (@semiformula_lt_free_bound_of_occurs L 0 p x Hx) as Hlt.
    rewrite (@rew_fix_iter_fvar_lt L 0 (semiformula_free_bound p) x Hlt).
    cbn [semiterm_val].
    unfold fin_value, fin_add_right_of_lt.
    rewrite Fin.to_nat_of_nat. now simpl. }
  pose proof (proj1 (@semiformula_eval_free_ext L M nat 0 Str
    (fun i => semiterm_val Str (fun j => f (fin_value j)) f
      (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
        (Semiterm_bvar i)))
    (fun x => semiterm_val Str (fun i => f (fin_value i)) f
      (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
    (Semiterm_fvar x))) f p Hfree) Hall) as Hp.
  assert (Hbound : forall i : Fin.t 0,
      semiterm_val Str (fun j => f (fin_value j)) f
        (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
          (Semiterm_bvar i)) = match i with end).
  { intro i. inversion i. }
  exact (proj1 (@semiformula_eval_bound_extensional L M nat 0 Str
    (fun i => semiterm_val Str
      (fun j => f (fin_value j)) f
      (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
        (Semiterm_bvar i)))
    (fun i : Fin.t 0 => match i with end) f p Hbound) Hp).
Qed.

Theorem arithmetic_models_successor_induction : forall
    (m : first_order_model oring_language) (O : oring_carrier
      (first_order_model_domain m)) C
    (phi : arithmetic_semiproposition 1) (f : nat ->
      first_order_model_domain m),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m (arithmetic_successor_induction_scheme C) ->
  C phi ->
  arithmetic_predicate_holds (first_order_model_structure m) f phi
      (oring_zero O) ->
  (forall x, arithmetic_predicate_holds
      (first_order_model_structure m) f phi x ->
    arithmetic_predicate_holds (first_order_model_structure m) f phi
      (oring_add O x (oring_one O))) ->
  forall x, arithmetic_predicate_holds
    (first_order_model_structure m) f phi x.
Proof.
  intros m O C phi f Horing Hmodels HC Hzero Hsucc.
  pose proof (first_order_models_of_member Hmodels
    (arithmetic_successor_induction_scheme_intro HC)) as Haxiom.
  pose proof (@semiformula_universal_closure_elim oring_language
    (first_order_model_domain m) (first_order_model_structure m)
    (arithmetic_successor_induction phi) f Haxiom) as Hind.
  pose proof (proj1 (@arithmetic_successor_induction_eval
    (first_order_model_domain m) nat (first_order_model_structure m)
    f O phi Horing) Hind) as Hinduction.
  exact (Hinduction Hzero Hsucc).
Qed.

Record arithmetic_model_predicate_representation
    (m : first_order_model oring_language)
    (C : arithmetic_semiproposition 1 -> Prop)
    (P : first_order_model_domain m -> Prop) : Type := {
  arithmetic_representation_valuation : nat -> first_order_model_domain m;
  arithmetic_representation_formula : arithmetic_semiproposition 1;
  arithmetic_representation_class :
    C arithmetic_representation_formula;
  arithmetic_representation_spec : forall x,
    P x <-> arithmetic_predicate_holds (first_order_model_structure m)
      arithmetic_representation_valuation arithmetic_representation_formula x
}.

Theorem arithmetic_models_induction_theory_successor : forall
    (m : first_order_model oring_language) (O : oring_carrier
      (first_order_model_domain m)) T C
    (P : first_order_model_domain m -> Prop),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m (arithmetic_induction_theory T C) ->
  @arithmetic_model_predicate_representation m C P ->
  P (oring_zero O) ->
  (forall x, P x -> P (oring_add O x (oring_one O))) ->
  forall x, P x.
Proof.
  intros m O T C P Horing Hmodels
    [f phi HC Hspec] Hzero Hsucc.
  unfold arithmetic_induction_theory, first_order_theory_union in Hmodels.
  pose proof (proj1 (@first_order_models_union_iff oring_language m
    T (arithmetic_successor_induction_scheme C)) Hmodels) as Hparts.
  pose proof (@arithmetic_models_successor_induction m O C phi f
    Horing (proj2 Hparts) HC) as Hind.
  assert (Hzero' : arithmetic_predicate_holds
      (first_order_model_structure m) f phi (oring_zero O)).
  { apply (proj1 (Hspec (oring_zero O))). exact Hzero. }
  assert (Hsucc' : forall x,
      arithmetic_predicate_holds (first_order_model_structure m) f phi x ->
      arithmetic_predicate_holds (first_order_model_structure m) f phi
        (oring_add O x (oring_one O))).
  { intros x Hx. apply (proj1 (Hspec _)).
    apply Hsucc. apply (proj2 (Hspec x)). exact Hx. }
  intro x. apply (proj2 (Hspec x)). exact (Hind Hzero' Hsucc' x).
Qed.

(** Negative induction is the semantic heart of hierarchy duality.  The
    auxiliary predicate [x <= a -> phi (a - x)] is generated by the bounded
    reverse-substitution formula in [PeanoMinus.Definability], so this proof
    works uniformly at every polarity and hierarchy rank. *)
Theorem arithmetic_models_hierarchy_negative_induction : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)) pol rank
    (phi : arithmetic_semiproposition 1)
    (f : nat -> first_order_model_domain m),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m
    (arithmetic_induction_on_hierarchy pol rank) ->
  arithmetic_hierarchy nat pol rank 1 phi ->
  ~ arithmetic_predicate_holds (first_order_model_structure m) f phi
      (oring_zero O) ->
  (forall x,
    ~ arithmetic_predicate_holds (first_order_model_structure m) f phi x ->
    ~ arithmetic_predicate_holds (first_order_model_structure m) f phi
      (oring_add O x (oring_one O))) ->
  forall x,
    ~ arithmetic_predicate_holds (first_order_model_structure m) f phi x.
Proof.
  intros m O pol rank phi f Horing Hmodels Hphi Hzero Hsucc a Ha.
  pose proof (proj1 (@first_order_models_union_iff oring_language m
    peano_minus_axiom
    (arithmetic_successor_induction_scheme
      (fun psi => arithmetic_hierarchy nat pol rank 1 psi))) Hmodels)
    as Hparts.
  pose proof (proj1 (@first_order_model_models_peano_minus_iff m O Horing)
    (proj1 Hparts)) as Hpa.
  pose proof (@arithmetic_models_successor_induction m O
    (fun psi => arithmetic_hierarchy nat pol rank 1 psi)
    (arithmetic_reverse_induction_formula phi) (nat_env_cons a f)
    Horing (proj2 Hparts)
    (arithmetic_reverse_induction_formula_hierarchy Hphi)) as Hind.
  assert (HQzero : arithmetic_predicate_holds
      (first_order_model_structure m) (nat_env_cons a f)
      (arithmetic_reverse_induction_formula phi) (oring_zero O)).
  { apply (proj2 (arithmetic_reverse_induction_formula_eval Horing Hpa
      phi a (oring_zero O) f)).
    intro Hle. rewrite (peano_minus_sub_zero Hpa). exact Ha. }
  assert (HQsucc : forall x,
      arithmetic_predicate_holds (first_order_model_structure m)
        (nat_env_cons a f) (arithmetic_reverse_induction_formula phi) x ->
      arithmetic_predicate_holds (first_order_model_structure m)
        (nat_env_cons a f) (arithmetic_reverse_induction_formula phi)
        (oring_add O x (oring_one O))).
  { intros x Hx.
    apply (proj2 (arithmetic_reverse_induction_formula_eval Horing Hpa
      phi a (oring_add O x (oring_one O)) f)).
    intro Hsxle.
    assert (Hxa : oring_lt O x a).
    { apply (@peano_minus_lt_le_trans _ O Hpa x
        (oring_add O x (oring_one O)) a).
      - apply (peano_minus_lt_add_one Hpa).
      - exact Hsxle. }
    assert (Hxle : peano_minus_le O x a).
    { apply peano_minus_lt_le. exact Hxa. }
    pose proof (proj1
      (arithmetic_reverse_induction_formula_eval Horing Hpa
        phi a x f) Hx Hxle)
      as HPx.
    apply NNPP. intro Hnotpred.
    apply (Hsucc (peano_minus_sub O a
      (oring_add O x (oring_one O))) Hnotpred).
    pose proof (@peano_minus_sub_succ_add_succ _ O Hpa a x
      (oring_zero O) Hxa) as Hstep.
    rewrite (peano_minus_add_zero_left Hpa),
      (peano_minus_add_zero Hpa) in Hstep.
    now rewrite Hstep. }
  pose proof (Hind HQzero HQsucc a) as HQa.
  pose proof (proj1
    (arithmetic_reverse_induction_formula_eval Horing Hpa
      phi a a f) HQa
    (peano_minus_le_refl a)) as HPzero.
  rewrite (peano_minus_sub_self Hpa) in HPzero.
  exact (Hzero HPzero).
Qed.

Theorem arithmetic_models_hierarchy_scheme_alt : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)) pol rank,
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m
    (arithmetic_induction_on_hierarchy pol rank) ->
  first_order_models_theory m
    (arithmetic_successor_induction_scheme
      (fun phi => arithmetic_hierarchy nat
        (arithmetic_polarity_alt pol) rank 1 phi)).
Proof.
  intros m O pol rank Horing Hmodels.
  apply (proj2 (first_order_models_theory_iff m _)).
  intros sigma [phi [Hphi ->]].
  unfold first_order_model_realize.
  apply semiformula_universal_closure_intro.
  - exact (first_order_model_nonempty m).
  - intro f.
    apply (proj2 (@arithmetic_successor_induction_eval
      (first_order_model_domain m) nat (first_order_model_structure m)
      f O phi Horing)).
    intros Hbase Hstep x.
    assert (Hnegphi : arithmetic_hierarchy nat pol rank 1
        (semiformula_neg phi)).
    { pose proof (arithmetic_hierarchy_neg Hphi) as Hneg.
      destruct pol; exact Hneg. }
    pose proof (@arithmetic_models_hierarchy_negative_induction
      m O pol rank (semiformula_neg phi) f Horing Hmodels Hnegphi)
      as Hnegative.
    apply NNPP. intro Hnotx.
    apply (Hnegative
      (fun Hnegzero =>
        (proj1 (@semiformula_eval_neg oring_language
          (first_order_model_domain m) nat 1
          (first_order_model_structure m)
          (fun _ : Fin.t 1 => oring_zero O) f phi) Hnegzero Hbase))
      (fun y Hnotneg Hnegsucc => Hnotneg
        (proj2 (@semiformula_eval_neg oring_language
          (first_order_model_domain m) nat 1
          (first_order_model_structure m)
          (fun _ : Fin.t 1 => y) f phi)
          (fun Hy =>
            (proj1 (@semiformula_eval_neg oring_language
              (first_order_model_domain m) nat 1
              (first_order_model_structure m)
              (fun _ : Fin.t 1 => oring_add O y (oring_one O)) f phi)
              Hnegsucc (Hstep y Hy))))) x).
    apply (proj2 (@semiformula_eval_neg oring_language
      (first_order_model_domain m) nat 1
      (first_order_model_structure m) (fun _ : Fin.t 1 => x) f phi)).
    exact Hnotx.
Qed.

Theorem arithmetic_models_induction_on_hierarchy_alt : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)) pol rank,
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m
    (arithmetic_induction_on_hierarchy pol rank) ->
  first_order_models_theory m
    (arithmetic_induction_on_hierarchy
      (arithmetic_polarity_alt pol) rank).
Proof.
  intros m O pol rank Horing Hmodels.
  pose proof (proj1 (@first_order_models_union_iff oring_language m
    peano_minus_axiom
    (arithmetic_successor_induction_scheme
      (fun phi => arithmetic_hierarchy nat pol rank 1 phi))) Hmodels)
    as Hparts.
  apply (proj2 (@first_order_models_union_iff oring_language m
    peano_minus_axiom
    (arithmetic_successor_induction_scheme
      (fun phi => arithmetic_hierarchy nat
        (arithmetic_polarity_alt pol) rank 1 phi)))).
  split.
  - exact (proj1 Hparts).
  - exact (arithmetic_models_hierarchy_scheme_alt Horing Hmodels).
Qed.

Theorem arithmetic_models_isigma_iff_ipi : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)) rank,
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  (first_order_models_theory m (arithmetic_isigma rank) <->
   first_order_models_theory m (arithmetic_ipi rank)).
Proof.
  intros m O rank Horing. split; intro Hmodels.
  - exact (arithmetic_models_induction_on_hierarchy_alt
      (pol := arithmetic_sigma) Horing Hmodels).
  - exact (arithmetic_models_induction_on_hierarchy_alt
      (pol := arithmetic_pi) Horing Hmodels).
Qed.

Theorem arithmetic_models_hierarchy_successor_induction : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)) pol rank
    (phi : arithmetic_semiproposition 1)
    (f : nat -> first_order_model_domain m),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m
    (arithmetic_induction_on_hierarchy pol rank) ->
  arithmetic_hierarchy nat pol rank 1 phi ->
  arithmetic_predicate_holds (first_order_model_structure m) f phi
      (oring_zero O) ->
  (forall x,
    arithmetic_predicate_holds (first_order_model_structure m) f phi x ->
    arithmetic_predicate_holds (first_order_model_structure m) f phi
      (oring_add O x (oring_one O))) ->
  forall x,
    arithmetic_predicate_holds (first_order_model_structure m) f phi x.
Proof.
  intros m O pol rank phi f Horing Hmodels Hphi.
  pose proof (proj1 (@first_order_models_union_iff oring_language m
    peano_minus_axiom
    (arithmetic_successor_induction_scheme
      (fun psi => arithmetic_hierarchy nat pol rank 1 psi))) Hmodels)
    as Hparts.
  exact (@arithmetic_models_successor_induction m O
    (fun psi => arithmetic_hierarchy nat pol rank 1 psi) phi f
    Horing (proj2 Hparts) Hphi).
Qed.

Theorem arithmetic_models_hierarchy_order_induction : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)) pol rank
    (phi : arithmetic_semiproposition 1)
    (f : nat -> first_order_model_domain m),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m
    (arithmetic_induction_on_hierarchy pol rank) ->
  arithmetic_hierarchy nat pol rank 1 phi ->
  (forall x,
    (forall y, oring_lt O y x ->
      arithmetic_predicate_holds (first_order_model_structure m) f phi y) ->
    arithmetic_predicate_holds (first_order_model_structure m) f phi x) ->
  forall x,
    arithmetic_predicate_holds (first_order_model_structure m) f phi x.
Proof.
  intros m O pol rank phi f Horing Hmodels Hphi Hstep.
  pose proof (proj1 (@first_order_models_union_iff oring_language m
    peano_minus_axiom
    (arithmetic_successor_induction_scheme
      (fun psi => arithmetic_hierarchy nat pol rank 1 psi))) Hmodels)
    as Hparts.
  pose proof (proj1 (@first_order_model_models_peano_minus_iff m O Horing)
    (proj1 Hparts)) as Hpa.
  pose proof (@arithmetic_models_hierarchy_successor_induction
    m O pol rank (arithmetic_predecessor_formula phi) f Horing Hmodels
    (arithmetic_predecessor_formula_hierarchy Hphi)) as Hind.
  assert (HQzero : arithmetic_predicate_holds
      (first_order_model_structure m) f
      (arithmetic_predecessor_formula phi) (oring_zero O)).
  { apply (proj2 (arithmetic_predecessor_formula_eval Horing
      phi f (oring_zero O))).
    intros y Hy. exfalso. exact (peano_minus_not_lt_zero Hpa Hy). }
  assert (HQsucc : forall x,
      arithmetic_predicate_holds (first_order_model_structure m) f
        (arithmetic_predecessor_formula phi) x ->
      arithmetic_predicate_holds (first_order_model_structure m) f
        (arithmetic_predecessor_formula phi)
        (oring_add O x (oring_one O))).
  { intros x Hx.
    apply (proj2 (arithmetic_predecessor_formula_eval Horing
      phi f (oring_add O x (oring_one O)))).
    intros y Hy.
    pose proof (proj1 (arithmetic_predecessor_formula_eval Horing
      phi f x) Hx)
      as Hbelow.
    destruct (proj2 (peano_minus_le_iff_lt_add_one Hpa y x) Hy)
      as [-> | Hyx].
    - apply Hstep. exact Hbelow.
    - exact (Hbelow y Hyx). }
  pose proof (Hind HQzero HQsucc) as Hall.
  intro x. apply Hstep.
  exact (proj1 (arithmetic_predecessor_formula_eval Horing phi f x)
    (Hall x)).
Qed.

Theorem arithmetic_models_hierarchy_least_number : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)) pol rank
    (phi : arithmetic_semiproposition 1)
    (f : nat -> first_order_model_domain m),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  first_order_models_theory m
    (arithmetic_induction_on_hierarchy pol rank) ->
  arithmetic_hierarchy nat pol rank 1 phi ->
  forall x,
  arithmetic_predicate_holds (first_order_model_structure m) f phi x ->
  exists y,
    arithmetic_predicate_holds (first_order_model_structure m) f phi y /\
    forall z, oring_lt O z y ->
      ~ arithmetic_predicate_holds (first_order_model_structure m) f phi z.
Proof.
  intros m O pol rank phi f Horing Hmodels Hphi x Hx.
  destruct (classic (exists y,
      arithmetic_predicate_holds (first_order_model_structure m) f phi y /\
      forall z, oring_lt O z y ->
        ~ arithmetic_predicate_holds (first_order_model_structure m) f phi z))
    as [Hleast | Hnone]; [exact Hleast |].
  exfalso.
  assert (Hnegphi : arithmetic_hierarchy nat
      (arithmetic_polarity_alt pol) rank 1 (semiformula_neg phi)).
  { exact (arithmetic_hierarchy_neg Hphi). }
  pose proof (arithmetic_models_induction_on_hierarchy_alt
    Horing Hmodels) as Hmodels_alt.
  pose proof (@arithmetic_models_hierarchy_order_induction m O
    (arithmetic_polarity_alt pol) rank (semiformula_neg phi) f
    Horing Hmodels_alt Hnegphi) as Horder.
  assert (Hnegall : forall y,
      arithmetic_predicate_holds (first_order_model_structure m) f
        (semiformula_neg phi) y).
  { apply Horder. intros y Hbelow.
    apply (proj2 (@semiformula_eval_neg oring_language
      (first_order_model_domain m) nat 1
      (first_order_model_structure m) (fun _ : Fin.t 1 => y) f phi)).
    intro Hy. apply Hnone. exists y. split; [exact Hy |].
    intros z Hzy Hz.
    exact (proj1 (@semiformula_eval_neg oring_language
      (first_order_model_domain m) nat 1
      (first_order_model_structure m) (fun _ : Fin.t 1 => z) f phi)
      (Hbelow z Hzy) Hz). }
  exact (proj1 (@semiformula_eval_neg oring_language
    (first_order_model_domain m) nat 1
    (first_order_model_structure m) (fun _ : Fin.t 1 => x) f phi)
    (Hnegall x) Hx).
Qed.

Definition arithmetic_successor_induction_principle {M}
    (O : oring_carrier M) : Prop :=
  forall P : M -> Prop,
    P (oring_zero O) ->
    (forall x, P x -> P (oring_add O x (oring_one O))) ->
    forall x, P x.

Definition arithmetic_order_induction_principle {M}
    (O : oring_carrier M) : Prop :=
  forall P : M -> Prop,
    (forall x, (forall y, oring_lt O y x -> P y) -> P x) ->
    forall x, P x.

Definition arithmetic_least_number_principle {M}
    (O : oring_carrier M) : Prop :=
  forall (P : M -> Prop) x,
    P x -> exists y, P y /\ forall z, oring_lt O z y -> ~ P z.

Theorem arithmetic_order_induction_of_successor : forall M
    (O : oring_carrier M),
  peano_minus_laws O ->
  arithmetic_successor_induction_principle O ->
  arithmetic_order_induction_principle O.
Proof.
  intros M O Hpa Hsucc P Hind.
  set (Q := fun x => forall y, oring_lt O y x -> P y).
  assert (HQ : forall x, Q x).
  { apply (Hsucc Q).
    - intros y Hy. exfalso. exact (peano_minus_not_lt_zero Hpa Hy).
    - intros x Hx y Hy.
      destruct (proj2 (peano_minus_le_iff_lt_add_one Hpa y x) Hy)
        as [-> | Hyx].
      + apply Hind. exact Hx.
      + exact (Hx y Hyx). }
  intro x. apply Hind. exact (HQ x).
Qed.

Theorem arithmetic_least_number_of_order_induction : forall M
    (O : oring_carrier M),
  arithmetic_order_induction_principle O ->
  arithmetic_least_number_principle O.
Proof.
  intros M O Horder P x Hx.
  destruct (classic (exists y, P y /\
      forall z, oring_lt O z y -> ~ P z)) as [Hleast | Hnone].
  - exact Hleast.
  - exfalso.
    assert (Hnot : forall y, ~ P y).
    { apply (Horder (fun y => ~ P y)).
      intros y Hbelow Hy.
      apply Hnone. exists y. split; [exact Hy | exact Hbelow]. }
    exact (Hnot x Hx).
Qed.

Corollary arithmetic_least_number_of_successor_induction : forall M
    (O : oring_carrier M),
  peano_minus_laws O ->
  arithmetic_successor_induction_principle O ->
  arithmetic_least_number_principle O.
Proof.
  intros M O Hpa Hsucc.
  apply arithmetic_least_number_of_order_induction.
  now apply (arithmetic_order_induction_of_successor Hpa).
Qed.

Theorem arithmetic_boundary_of_least_number : forall M
    (O : oring_carrier M),
  peano_minus_laws O ->
  arithmetic_least_number_principle O ->
  forall P : M -> Prop,
  P (oring_zero O) ->
  (exists a, ~ P a) ->
  exists x, P x /\ ~ P (oring_add O x (oring_one O)).
Proof.
  intros M O Hpa Hleast P Hzero [a Ha].
  destruct (Hleast (fun x => ~ P x) a Ha)
    as [y [Hy Hmin]].
  destruct (@peano_minus_zero_le M O Hpa y) as [Hyzero | Hypos].
  - symmetry in Hyzero. subst y. contradiction.
  - destruct (peano_minus_positive_eq_add_one Hpa Hypos) as [x Hx].
    exists x. split.
    + apply NNPP. apply (Hmin x).
      rewrite Hx. apply (peano_minus_lt_add_one Hpa).
    + now rewrite <- Hx.
Qed.

(** * The standard model and metatheory *)

Theorem nat_standard_model_realizes_successor_induction : forall
    (phi : arithmetic_semiproposition 1),
  first_order_model_realize nat_standard_model
    (semiformula_universal_closure
      (arithmetic_successor_induction phi)).
Proof.
  intro phi. unfold first_order_model_realize.
  apply semiformula_universal_closure_intro.
  - exact (inhabits 0).
  - intro f.
    apply (proj2 (@arithmetic_successor_induction_eval nat nat
      nat_standard_structure f nat_oring_carrier phi
      nat_standard_structure_interprets)).
    intros Hzero Hsucc x. induction x as [|x IH].
    + exact Hzero.
    + replace (S x) with
          (oring_add nat_oring_carrier x (oring_one nat_oring_carrier)).
      * now apply Hsucc.
      * cbn. apply Nat.add_1_r.
Qed.

Theorem nat_standard_model_models_successor_induction_scheme : forall C,
  first_order_models_theory nat_standard_model
    (arithmetic_successor_induction_scheme C).
Proof.
  intro C. apply (proj2 (first_order_models_theory_iff
    nat_standard_model (arithmetic_successor_induction_scheme C))).
  intros sigma [phi [Hphi ->]].
  apply nat_standard_model_realizes_successor_induction.
Qed.

Theorem nat_standard_model_models_induction_theory : forall C,
  first_order_models_theory nat_standard_model
    (arithmetic_induction_theory peano_minus_axiom C).
Proof.
  intro C. apply (proj2 (@first_order_models_union_iff oring_language
    nat_standard_model peano_minus_axiom
    (arithmetic_successor_induction_scheme C))).
  split.
  - exact nat_standard_model_models_peano_minus.
  - apply nat_standard_model_models_successor_induction_scheme.
Qed.

Theorem nat_standard_model_models_iopen :
  first_order_models_theory nat_standard_model arithmetic_iopen.
Proof. apply nat_standard_model_models_induction_theory. Qed.

Theorem nat_standard_model_models_induction_on_hierarchy : forall pol k,
  first_order_models_theory nat_standard_model
    (arithmetic_induction_on_hierarchy pol k).
Proof.
  intros pol k. apply nat_standard_model_models_induction_theory.
Qed.

Theorem nat_standard_model_models_isigma : forall k,
  first_order_models_theory nat_standard_model (arithmetic_isigma k).
Proof.
  intro k. apply nat_standard_model_models_induction_on_hierarchy.
Qed.

Theorem nat_standard_model_models_ipi : forall k,
  first_order_models_theory nat_standard_model (arithmetic_ipi k).
Proof.
  intro k. apply nat_standard_model_models_induction_on_hierarchy.
Qed.

Theorem nat_standard_model_models_peano :
  first_order_models_theory nat_standard_model
    first_order_peano_arithmetic.
Proof. apply nat_standard_model_models_induction_theory. Qed.

Theorem arithmetic_induction_on_hierarchy_consistent : forall pol k,
  generic_consistent
    (first_order_theory_entailment oring_language)
    (arithmetic_induction_on_hierarchy pol k).
Proof.
  intros pol k. exact (first_order_theory_consistent_of_model
    (nat_standard_model_models_induction_on_hierarchy pol k)).
Qed.

Theorem first_order_peano_arithmetic_consistent :
  generic_consistent
    (first_order_theory_entailment oring_language)
    first_order_peano_arithmetic.
Proof.
  exact (first_order_theory_consistent_of_model
    nat_standard_model_models_peano).
Qed.

Theorem first_order_peano_weaker_than_true_arithmetic :
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    first_order_peano_arithmetic first_order_true_arithmetic.
Proof.
  apply arithmetic_theory_weaker_than_true_arithmetic.
  exact nat_standard_model_models_peano.
Qed.

(** Model inheritance is stated independently of proof-theoretic weakening,
    so clients do not need to invoke soundness merely to forget axioms. *)
Theorem arithmetic_models_isigma_of_le : forall
    (m : first_order_model oring_language) k l,
  k <= l ->
  first_order_models_theory m (arithmetic_isigma l) ->
  first_order_models_theory m (arithmetic_isigma k).
Proof.
  intros m k l Hkl Hmodels.
  eapply first_order_models_of_subset; [exact Hmodels |].
  exact (arithmetic_isigma_subset_mono Hkl).
Qed.

Theorem arithmetic_models_iopen_of_isigma_zero : forall
    (m : first_order_model oring_language),
  first_order_models_theory m (arithmetic_isigma 0) ->
  first_order_models_theory m arithmetic_iopen.
Proof.
  intros m Hmodels.
  eapply first_order_models_of_subset; [exact Hmodels |].
  exact arithmetic_iopen_subset_isigma_zero.
Qed.

Theorem arithmetic_models_peano_minus_of_iopen : forall
    (m : first_order_model oring_language),
  first_order_models_theory m arithmetic_iopen ->
  first_order_models_theory m peano_minus_axiom.
Proof.
  intros m Hmodels.
  eapply first_order_models_of_subset; [exact Hmodels |].
  exact peano_minus_subset_iopen.
Qed.

Theorem r0_weaker_than_of_peano_minus : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    peano_minus_axiom T ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T.
Proof.
  intros T Hweak.
  exact (generic_weaker_than_trans r0_weaker_than_peano_minus Hweak).
Qed.

Theorem peano_minus_weaker_than_of_isigma_zero : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_isigma 0) T ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    peano_minus_axiom T.
Proof.
  intros T Hweak.
  exact (generic_weaker_than_trans peano_minus_weaker_than_iopen
    (generic_weaker_than_trans arithmetic_iopen_weaker_than_isigma_zero
      Hweak)).
Qed.

Theorem peano_minus_weaker_than_of_isigma_one : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    (arithmetic_isigma 1) T ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    peano_minus_axiom T.
Proof.
  intros T Hweak.
  apply peano_minus_weaker_than_of_isigma_zero.
  exact (generic_weaker_than_trans
    arithmetic_isigma_zero_weaker_than_isigma_one Hweak).
Qed.

Theorem peano_minus_weaker_than_of_peano : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    first_order_peano_arithmetic T ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language)
    peano_minus_axiom T.
Proof.
  intros T Hweak.
  exact (generic_weaker_than_trans peano_minus_weaker_than_iopen
    (generic_weaker_than_trans
      (arithmetic_iopen_weaker_than_induction_on_hierarchy
        arithmetic_sigma 0)
      (generic_weaker_than_trans
        (arithmetic_isigma_weaker_than_peano 0) Hweak))).
Qed.
