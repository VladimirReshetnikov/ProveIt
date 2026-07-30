(** Generic axiom schemes underlying arithmetic induction theories. *)

From Stdlib Require Import Logic.Classical_Prop Logic.FunctionalExtensionality.
From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics RewriteClosure OperatorSemantics ModelTheory Elementary.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Hierarchy.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition arithmetic_zero_term {X n} : semiterm oring_language X n :=
  semiterm_operator_const_apply
    (semiterm_zero_operator
      (semiterm_zero_operator_of_language
        (language_oring_zero oring_language_structure))).

Definition arithmetic_one_term {X n} : semiterm oring_language X n :=
  semiterm_one_term
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure)).

Definition arithmetic_add_one_term {X n}
    (t : semiterm oring_language X n) : semiterm oring_language X n :=
  semiterm_add_one
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure))
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure)) t.

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

Lemma arithmetic_zero_term_val : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  semiterm_val Str b f arithmetic_zero_term = oring_zero O.
Proof.
  intros M X n Str b f O Horing.
  unfold arithmetic_zero_term, semiterm_operator_const_apply.
  rewrite semiterm_val_operator_apply, semiterm_val_fin_zero.
  apply structure_zero_operator. exact (structure_oring_zero Horing).
Qed.

Lemma arithmetic_add_one_term_val : forall M X n
    (Str : first_order_structure oring_language M)
    (b : Fin.t n -> M) (f : X -> M) (O : oring_carrier M)
    (t : semiterm oring_language X n),
  structure_interprets_oring Str oring_language_structure O ->
  semiterm_val Str b f (arithmetic_add_one_term t) =
  oring_add O (semiterm_val Str b f t) (oring_one O).
Proof.
  intros M X n Str b f O t Horing. unfold arithmetic_add_one_term.
  apply semiterm_val_add_one.
  - exact (structure_oring_one Horing).
  - exact (structure_oring_add Horing).
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

Definition arithmetic_sigma_induction_theory
    (T : theory oring_language) (k : nat) : theory oring_language :=
  arithmetic_induction_theory T
    (fun phi => arithmetic_hierarchy nat arithmetic_sigma k 1 phi).

Definition arithmetic_peano_theory (T : theory oring_language) :
    theory oring_language :=
  arithmetic_induction_theory T (fun _ => True).

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

Lemma arithmetic_sigma_induction_subset_peano : forall T k sigma,
  arithmetic_sigma_induction_theory T k sigma ->
  arithmetic_peano_theory T sigma.
Proof.
  intros T k. apply arithmetic_induction_theory_subset.
  intros phi Hphi. exact I.
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
