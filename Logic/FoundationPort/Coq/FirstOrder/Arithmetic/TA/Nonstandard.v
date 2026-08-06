(**
  Semantic compactness and nonstandard arithmetic.

  This ports the model-theoretic core of
  [Foundation/FirstOrder/Arithmetic/TA/Nonstandard.lean].  The source uses
  a quotient model carrying a proof-relevant equality instance.  Here the
  compactness theorem already produces a bundled first-order model, so the
  semantic statement is factored through an explicit language-sum reduct and
  does not pretend to provide the source's internal coding interface.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Vectors.Fin.
From Stdlib Require Import Logic.ClassicalEpsilon Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Eq Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics ModelTheory.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Model.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic Theory.
From Foundation.FirstOrder.Arithmetic.TA Require Import Basic.
From Foundation.FirstOrder Require Import Ultraproduct.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

(** * The arithmetic language with one distinguished constant *)

Definition nonstandard_language : language :=
  language_add oring_language unit_language.

Definition nonstandard_arithmetic_embedding :
    language_hom oring_language nonstandard_language :=
  language_hom_add_left oring_language unit_language.

Definition nonstandard_star_symbol :
    language_func nonstandard_language 0 :=
  @language_add_right_func oring_language unit_language 0
    (language_star unit_language_star).

Definition nonstandard_eq_operator :
    semiformula_has_eq_operator nonstandard_language :=
  semiformula_eq_operator_of_language
    (language_add_has_eq unit_language
      (language_oring_eq oring_language_structure)).

Definition nonstandard_lt_symbol :
    language_rel nonstandard_language 2 :=
  @language_add_left_rel oring_language unit_language 2 ORing_lt.

Definition nonstandard_star_term {X n} :
    semiterm nonstandard_language X n :=
  Semiterm_func nonstandard_star_symbol fin_zero.

Definition nonstandard_numeral_term {X n} (k : nat) :
    semiterm nonstandard_language X n :=
  semiterm_language_map nonstandard_arithmetic_embedding
    (arithmetic_numeral_term k).

Definition nonstandard_star_bound_sentence (k : nat) :
    sentence nonstandard_language :=
  @Semiformula_rel nonstandard_language Empty_set 0 2
    nonstandard_lt_symbol
    (fin_two (nonstandard_numeral_term k) nonstandard_star_term).

Definition nonstandard_star_unbounded_theory (c : nat) : theory nonstandard_language :=
  fun sigma => exists i : Fin.t c,
    sigma = nonstandard_star_bound_sentence (proj1_sig (Fin.to_nat i)).

Definition nonstandard_base_theory : theory nonstandard_language :=
  fun sigma =>
    @first_order_equality_axiom nonstandard_language
      nonstandard_eq_operator sigma \/
    theory_language_map nonstandard_arithmetic_embedding
      first_order_true_arithmetic sigma.

Definition nonstandard_bounded_theory (c : nat) : theory nonstandard_language :=
  fun sigma => nonstandard_base_theory sigma \/
    nonstandard_star_unbounded_theory c sigma.

Definition nonstandard_union_theory : theory nonstandard_language :=
  fun sigma => exists c, nonstandard_bounded_theory c sigma.

(** * The finite star models *)

Definition nonstandard_model_structure (c : nat) :
    first_order_structure nonstandard_language nat.
Proof.
  refine {| structure_func := fun k f v => _;
            structure_rel := fun k r v => _ |}.
  - destruct f as [f | f].
    + exact (structure_func nat_standard_structure f v).
    + destruct f. exact c.
  - destruct r as [r | r].
    + exact (structure_rel nat_standard_structure r v).
    + destruct r.
Defined.

Definition nonstandard_model (c : nat) :
    first_order_model nonstandard_language :=
  first_order_model_of_structure (inhabits 0)
    (nonstandard_model_structure c).

Lemma nonstandard_arithmetic_pullback_structure : forall c,
  first_order_structure_language_map nonstandard_arithmetic_embedding
    (nonstandard_model_structure c) = nat_standard_structure.
Proof.
  intro c. apply first_order_structure_ext.
  - intros k f v. reflexivity.
  - intros k r v. reflexivity.
Qed.

Lemma nonstandard_model_models_arithmetic : forall c,
  first_order_models_theory (nonstandard_model c)
    (theory_language_map nonstandard_arithmetic_embedding
      first_order_true_arithmetic).
Proof.
  intro c. rewrite first_order_models_theory_iff. intros sigma Hsigma.
  destruct Hsigma as [p [Hp Heq]]. subst sigma.
  apply (proj2 (first_order_model_realize_language_map
    nonstandard_arithmetic_embedding (nonstandard_model c) p)).
  change (sentence_realize
    (first_order_structure_language_map nonstandard_arithmetic_embedding
      (nonstandard_model_structure c)) p).
  rewrite nonstandard_arithmetic_pullback_structure.
  exact (first_order_models_of_member first_order_true_arithmetic_models Hp).
Qed.

Lemma nonstandard_model_interprets_eq : forall c,
  structure_interprets_eq (nonstandard_model_structure c)
    nonstandard_eq_operator.
Proof.
  intro c. constructor. intros a b. simpl. split; tauto.
Qed.

Lemma nonstandard_model_models_equality : forall c,
  first_order_models_theory (nonstandard_model c)
    (@first_order_equality_axiom nonstandard_language
      nonstandard_eq_operator).
Proof.
  intro c. apply first_order_model_models_equality_theory_of_interprets_eq.
  apply nonstandard_model_interprets_eq.
Qed.

Lemma nonstandard_bound_realize_iff : forall c k,
  first_order_model_realize (nonstandard_model c)
    (nonstandard_star_bound_sentence k) <-> k < c.
Proof.
  intros c k. unfold first_order_model_realize, nonstandard_star_bound_sentence,
    nonstandard_numeral_term, sentence_realize, formula_eval.
  simpl.
  rewrite semiterm_val_language_map.
  rewrite (@arithmetic_numeral_term_val nat Empty_set 0
    (first_order_structure_language_map nonstandard_arithmetic_embedding
      (nonstandard_model_structure c))
    (fun i : Fin.t 0 => match i with end)
    (fun x : Empty_set => match x with end) nat_oring_carrier k).
  - rewrite nat_oring_numeral. reflexivity.
  - apply oring_standard_structure_interprets.
Qed.

Lemma nonstandard_model_models_star_unbounded : forall c,
  first_order_models_theory (nonstandard_model c)
    (nonstandard_star_unbounded_theory c).
Proof.
  intros c. apply (proj2 (first_order_models_theory_iff _ _)).
  intros sigma Hsigma. destruct Hsigma as [i ->].
  apply (proj2 (nonstandard_bound_realize_iff c
    (proj1_sig (Fin.to_nat i)))).
  exact (proj2_sig (Fin.to_nat i)).
Qed.

Lemma nonstandard_model_models_bounded : forall c,
  first_order_models_theory (nonstandard_model c)
    (nonstandard_bounded_theory c).
Proof.
  intros c. apply (proj2 (first_order_models_theory_iff _ _)).
  intros sigma [Hbase | Hbound].
  - destruct Hbase as [Heq | Harith].
    + exact (first_order_models_of_member
        (nonstandard_model_models_equality c) Heq).
    + exact (first_order_models_of_member
        (nonstandard_model_models_arithmetic c) Harith).
  - exact (first_order_models_of_member
      (nonstandard_model_models_star_unbounded c) Hbound).
Qed.

(** A finite list of requirements is bounded by one finite star model. *)
Lemma nonstandard_finite_satisfiable : forall (Gamma : list (sentence nonstandard_language)),
  (forall sigma, In sigma Gamma -> nonstandard_union_theory sigma) ->
  exists c, first_order_models_theory (nonstandard_model c)
    (fun sigma => In sigma Gamma).
Proof.
  induction Gamma as [|sigma Gamma IH].
  - exists 0.
    apply (proj2 (first_order_models_theory_iff _ _)).
    intros q Hq. contradiction.
  - intros HGamma.
    destruct (HGamma sigma (or_introl eq_refl)) as [c Hc].
    destruct (IH (fun q Hq => HGamma q (or_intror Hq))) as [d Hd].
    exists (Nat.max c d).
    apply (proj2 (first_order_models_theory_iff _ _)).
    intros q [-> | Hq].
    + destruct Hc as [Hbase | Hbound].
      * destruct Hbase as [Heq | Harith].
        (* equality axioms hold in every finite model *)
        exact (first_order_models_of_member
          (nonstandard_model_models_equality (Nat.max c d)) Heq).
        (* true arithmetic holds in every finite model *)
        exact (first_order_models_of_member
          (nonstandard_model_models_arithmetic (Nat.max c d)) Harith).
      * destruct Hbound as [i ->].
        apply (proj2 (nonstandard_bound_realize_iff (Nat.max c d)
          (proj1_sig (Fin.to_nat i)))).
        pose proof (proj2_sig (Fin.to_nat i)) as Hi.
        apply Nat.lt_le_trans with c; [exact Hi|apply Nat.le_max_l].
    + destruct (HGamma q (or_intror Hq)) as [e He].
      destruct He as [Hbase | Hbound].
      * destruct Hbase as [Heq | Harith].
        (* equality axioms hold in every finite model *)
        exact (first_order_models_of_member
          (nonstandard_model_models_equality (Nat.max c d)) Heq).
        (* true arithmetic holds in every finite model *)
        exact (first_order_models_of_member
          (nonstandard_model_models_arithmetic (Nat.max c d)) Harith).
      * destruct Hbound as [i ->].
        apply (proj2 (nonstandard_bound_realize_iff (Nat.max c d)
          (proj1_sig (Fin.to_nat i)))).
        pose proof (first_order_models_of_member Hd Hq) as Hqd.
        pose proof (proj1 (nonstandard_bound_realize_iff d
          (proj1_sig (Fin.to_nat i))) Hqd) as Hid.
        apply Nat.lt_le_trans with d; [exact Hid|apply Nat.le_max_r].
Qed.

Theorem nonstandard_union_satisfiable :
  first_order_satisfiable nonstandard_union_theory.
Proof.
  apply (proj2 (first_order_compactness nonstandard_union_theory)).
  intros Gamma HGamma.
  destruct (@nonstandard_finite_satisfiable Gamma HGamma) as [c Hc].
  exists (nonstandard_model c). exact Hc.
Qed.

(** * The compactness-produced nonstandard model and its reduct *)

Definition nonstandard_model_package : Type :=
  { m : first_order_model nonstandard_language |
    first_order_models_theory m nonstandard_union_theory }.

Definition nonstandard_model_package_choose : nonstandard_model_package :=
  constructive_indefinite_description _ nonstandard_union_satisfiable.

Definition nonstandard_reduct (N : nonstandard_model_package) :
    first_order_model oring_language :=
  first_order_model_language_pullback nonstandard_arithmetic_embedding
    (proj1_sig N).

Definition nonstandard_star_value (N : nonstandard_model_package) :
    first_order_model_domain (proj1_sig N) :=
  structure_func (first_order_model_structure (proj1_sig N))
    nonstandard_star_symbol fin_zero.

Definition nonstandard_numeral_value (N : nonstandard_model_package) (k : nat) :
    first_order_model_domain (proj1_sig N) :=
  semiterm_val (first_order_model_structure (proj1_sig N))
    (fun i : Fin.t 0 => match i with end)
    (fun x : Empty_set => match x with end)
    (nonstandard_numeral_term k).

Definition nonstandard_lt (N : nonstandard_model_package)
    (a b : first_order_model_domain (proj1_sig N)) : Prop :=
  structure_rel (first_order_model_structure (proj1_sig N))
    nonstandard_lt_symbol (fin_two a b).

Lemma nonstandard_reduct_models_true_arithmetic :
  first_order_models_theory (nonstandard_reduct nonstandard_model_package_choose)
    first_order_true_arithmetic.
Proof.
  apply (proj2 (first_order_models_theory_iff _ _)).
  intros sigma Hsigma.
  apply (proj1 (first_order_model_realize_language_map
    nonstandard_arithmetic_embedding
    (proj1_sig nonstandard_model_package_choose) sigma)).
  apply (first_order_models_of_member
    (proj2_sig nonstandard_model_package_choose)).
  exists 0. left. right. exists sigma. split; [exact Hsigma|reflexivity].
Qed.

Lemma nonstandard_reduct_models_peano_minus :
  first_order_models_theory (nonstandard_reduct nonstandard_model_package_choose)
    peano_minus_axiom.
Proof.
  apply (proj2 (first_order_models_theory_iff _ _)).
  intros sigma Hsigma.
  apply (proj1 (first_order_model_realize_language_map
    nonstandard_arithmetic_embedding
    (proj1_sig nonstandard_model_package_choose) sigma)).
  apply (first_order_models_of_member
    (proj2_sig nonstandard_model_package_choose)).
  exists 0. left. right. exists sigma. split.
  - apply (proj1 (first_order_model_theory_spec nat_standard_model sigma)).
    apply (first_order_models_of_member
      nat_standard_model_models_peano_minus Hsigma).
  - reflexivity.
Qed.

Lemma nonstandard_star_unbounded : forall k,
  @nonstandard_lt nonstandard_model_package_choose
    (nonstandard_numeral_value nonstandard_model_package_choose k)
    (nonstandard_star_value nonstandard_model_package_choose).
Proof.
  intro k.
  assert (Hstar : nonstandard_star_unbounded_theory (S k)
      (nonstandard_star_bound_sentence k)).
  { exists (Fin.of_nat_lt (Nat.lt_succ_diag_r k)).
    rewrite Fin.to_nat_of_nat. reflexivity. }
  pose proof (first_order_models_of_member
    (proj2_sig nonstandard_model_package_choose)
    (ex_intro (fun c => nonstandard_bounded_theory c
      (nonstandard_star_bound_sentence k)) (S k) (or_intror Hstar))) as Hbound.
  unfold first_order_model_realize, nonstandard_star_bound_sentence,
    sentence_realize, formula_eval in Hbound.
  unfold nonstandard_lt, nonstandard_numeral_value,
    nonstandard_star_value.
  simpl in Hbound.
  rewrite semiterm_val_fin_two in Hbound.
  unfold nonstandard_star_term in Hbound.
  simpl in Hbound.
  rewrite semiterm_val_fin_zero in Hbound.
  cbn in *.
  exact Hbound.
Qed.
