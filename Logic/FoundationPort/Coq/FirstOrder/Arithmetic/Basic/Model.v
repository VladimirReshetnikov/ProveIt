(**
  The canonical ordered-ring first-order structure.

  This ports the semantic construction and uniqueness core of
  [Foundation/FirstOrder/Arithmetic/Basic/Model.lean].  Structures and their
  operation packages are explicit, allowing several interpretations on one
  carrier to be compared directly.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics ModelTheory.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition oring_standard_structure {M} (O : oring_carrier M) :
    first_order_structure oring_language M.
Proof.
  refine {| structure_func := fun k f v => _;
            structure_rel := fun k r v => _ |}.
  - destruct f.
    + exact (oring_zero O).
    + exact (oring_one O).
    + exact (oring_add O (v Fin.F1) (v (Fin.FS Fin.F1))).
    + exact (oring_mul O (v Fin.F1) (v (Fin.FS Fin.F1))).
  - destruct r.
    + exact (v Fin.F1 = v (Fin.FS Fin.F1)).
    + exact (oring_lt O (v Fin.F1) (v (Fin.FS Fin.F1))).
Defined.

Lemma oring_standard_structure_zero : forall M (O : oring_carrier M)
    (v : Fin.t 0 -> M),
  structure_func (oring_standard_structure O) ORing_zero v = oring_zero O.
Proof. reflexivity. Qed.

Lemma oring_standard_structure_one : forall M (O : oring_carrier M)
    (v : Fin.t 0 -> M),
  structure_func (oring_standard_structure O) ORing_one v = oring_one O.
Proof. reflexivity. Qed.

Lemma oring_standard_structure_add : forall M (O : oring_carrier M)
    (v : Fin.t 2 -> M),
  structure_func (oring_standard_structure O) ORing_add v =
  oring_add O (v Fin.F1) (v (Fin.FS Fin.F1)).
Proof. reflexivity. Qed.

Lemma oring_standard_structure_mul : forall M (O : oring_carrier M)
    (v : Fin.t 2 -> M),
  structure_func (oring_standard_structure O) ORing_mul v =
  oring_mul O (v Fin.F1) (v (Fin.FS Fin.F1)).
Proof. reflexivity. Qed.

Lemma oring_standard_structure_eq : forall M (O : oring_carrier M)
    (v : Fin.t 2 -> M),
  structure_rel (oring_standard_structure O) ORing_eq v <->
  v Fin.F1 = v (Fin.FS Fin.F1).
Proof. reflexivity. Qed.

Lemma oring_standard_structure_lt : forall M (O : oring_carrier M)
    (v : Fin.t 2 -> M),
  structure_rel (oring_standard_structure O) ORing_lt v <->
  oring_lt O (v Fin.F1) (v (Fin.FS Fin.F1)).
Proof. reflexivity. Qed.

Lemma oring_standard_structure_interprets : forall M (O : oring_carrier M),
  structure_interprets_oring (oring_standard_structure O)
    oring_language_structure O.
Proof.
  intros. constructor; constructor; intros; reflexivity.
Qed.

(** Extensionality is factored once because relation interpretations are
    proposition-valued. *)
Lemma first_order_structure_ext : forall L M
    (S T : first_order_structure L M),
  (forall k (f : language_func L k) v,
    structure_func S f v = structure_func T f v) ->
  (forall k (r : language_rel L k) v,
    structure_rel S r v <-> structure_rel T r v) ->
  S = T.
Proof.
  intros L M [Sf Sr] [Tf Tr] Hf Hr; simpl in *.
  assert (HSf : Sf = Tf).
  { apply functional_extensionality_dep. intro k.
    apply functional_extensionality. intro f.
    apply functional_extensionality. intro v. apply Hf. }
  subst Tf.
  assert (HSr : Sr = Tr).
  { apply functional_extensionality_dep. intro k.
    apply functional_extensionality. intro r.
    apply functional_extensionality. intro v.
    apply propositional_extensionality. apply Hr. }
  now subst Tr.
Qed.

Lemma fin_zero_eta : forall A (v : Fin.t 0 -> A), v = fin_zero.
Proof.
  intros. apply functional_extensionality. intro i. inversion i.
Qed.

Theorem oring_standard_structure_unique : forall M (O : oring_carrier M)
    (S : first_order_structure oring_language M),
  structure_interprets_oring S oring_language_structure O ->
  S = oring_standard_structure O.
Proof.
  intros M O S Horing. apply first_order_structure_ext.
  - intros k f v. destruct f.
    + change (structure_func S ORing_zero v = oring_zero O).
      rewrite (fin_zero_eta v).
      exact (structure_zero_operator (structure_oring_zero Horing)).
    + change (structure_func S ORing_one v = oring_one O).
      rewrite (fin_zero_eta v).
      exact (structure_one_operator (structure_oring_one Horing)).
    + change (structure_func S ORing_add v =
        oring_add O (v Fin.F1) (v (Fin.FS Fin.F1))).
      rewrite (fin_two_eta v).
      exact (structure_add_operator (structure_oring_add Horing)
        (v Fin.F1) (v (Fin.FS Fin.F1))).
    + change (structure_func S ORing_mul v =
        oring_mul O (v Fin.F1) (v (Fin.FS Fin.F1))).
      rewrite (fin_two_eta v).
      exact (structure_mul_operator (structure_oring_mul Horing)
        (v Fin.F1) (v (Fin.FS Fin.F1))).
  - intros k r v. destruct r.
    + change (structure_rel S ORing_eq v <->
        v Fin.F1 = v (Fin.FS Fin.F1)).
      rewrite (fin_two_eta v).
      change (semiformula_operator_eval S
        (fin_two (v Fin.F1) (v (Fin.FS Fin.F1)))
        (semiformula_eq_operator
          (semiformula_eq_operator_of_language
            (language_oring_eq oring_language_structure))) <->
        v Fin.F1 = v (Fin.FS Fin.F1)).
      apply structure_eq_operator. exact (structure_oring_eq Horing).
    + change (structure_rel S ORing_lt v <->
        oring_lt O (v Fin.F1) (v (Fin.FS Fin.F1))).
      rewrite (fin_two_eta v).
      change (semiformula_operator_eval S
        (fin_two (v Fin.F1) (v (Fin.FS Fin.F1)))
        (semiformula_lt_operator
          (semiformula_lt_operator_of_language
            (language_oring_lt oring_language_structure))) <->
        oring_lt O (v Fin.F1) (v (Fin.FS Fin.F1))).
      apply structure_relation_operator. exact (structure_oring_lt Horing).
Qed.

Definition nat_standard_structure : first_order_structure oring_language nat :=
  oring_standard_structure nat_oring_carrier.

Lemma nat_standard_structure_interprets :
  structure_interprets_oring nat_standard_structure
    oring_language_structure nat_oring_carrier.
Proof. apply oring_standard_structure_interprets. Qed.

(** The natural-number model used by arithmetic soundness. *)
Definition nat_standard_model : first_order_model oring_language :=
  first_order_model_of_structure (inhabits 0) nat_standard_structure.

(** Soundness restricted to a selected syntactic class of arithmetic
    sentences.  Keeping the class explicit mirrors Foundation's [SoundOn]
    interface without introducing global typeclass state. *)
Record arithmetic_theory_sound_on
    (T : theory oring_language)
    (F : sentence oring_language -> Prop) : Prop := {
  arithmetic_theory_sound_on_elim :
    forall sigma : sentence oring_language,
      first_order_theory_provable T sigma ->
      F sigma ->
      first_order_model_realize nat_standard_model sigma
}.

Arguments arithmetic_theory_sound_on_elim {T F} _ {sigma} _ _.

Definition arithmetic_theory_sound_on_of_models
    (T : theory oring_language)
    (F : sentence oring_language -> Prop)
    (Hmodels : first_order_models_theory nat_standard_model T) :
    arithmetic_theory_sound_on T F.
Proof.
  constructor. intros sigma Hproof _.
  exact (first_order_models_of_provable Hmodels Hproof).
Defined.

Theorem arithmetic_theory_consistent_of_sound_on :
  forall (T : theory oring_language)
         (F : sentence oring_language -> Prop),
    arithmetic_theory_sound_on T F ->
    F (@Semiformula_falsum oring_language Empty_set 0) ->
    generic_consistent (first_order_theory_entailment oring_language) T.
Proof.
  intros T F Hsound Hfalse. constructor. intro Hinc.
  exact (arithmetic_theory_sound_on_elim Hsound
    (Hinc (@Semiformula_falsum oring_language Empty_set 0)) Hfalse).
Qed.
