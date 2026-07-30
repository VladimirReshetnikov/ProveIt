(**
  Bundled first-order models and semantic consequence.

  This ports the global model/theory layer of
  [Foundation/FirstOrder/Basic/Semantics/Semantics.lean] by instantiating the
  already audited generic semantics API.  A bundled model retains the
  source's nonempty-domain invariant, while the carrier and structure remain
  available explicitly for theorem statements and construction.
*)

From FoundationModal Require Import GenericSemantics.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Bundled nonempty models *)

Record first_order_model (L : language) : Type := {
  first_order_model_domain : Type;
  first_order_model_nonempty : inhabited first_order_model_domain;
  first_order_model_structure :
    first_order_structure L first_order_model_domain
}.

Arguments first_order_model_domain {L} _.
Arguments first_order_model_nonempty {L} _.
Arguments first_order_model_structure {L} _.

Definition first_order_model_of_structure {L M}
    (Hinh : inhabited M) (Str : first_order_structure L M) :
    first_order_model L :=
  {| first_order_model_domain := M;
     first_order_model_nonempty := Hinh;
     first_order_model_structure := Str |}.

Definition first_order_model_realize {L}
    (m : first_order_model L) (p : sentence L) : Prop :=
  sentence_realize (first_order_model_structure m) p.

Definition first_order_semantics (L : language) :
    generic_semantics (first_order_model L) (sentence L) :=
  {| generic_models := first_order_model_realize |}.

Definition sentence_connectives (L : language) :
    generic_connectives (sentence L) :=
  semiformula_connectives L Empty_set 0.

(** The bundled models form a classical Tarski semantics because formulas
    are stored in negation normal form. *)
Definition first_order_semantics_top (L : language) :
    generic_semantics_top (sentence_connectives L) (first_order_semantics L).
Proof. constructor. intros m. exact I. Defined.

Definition first_order_semantics_bottom (L : language) :
    generic_semantics_bottom (sentence_connectives L) (first_order_semantics L).
Proof. constructor. intros m H. exact H. Defined.

Definition first_order_semantics_and (L : language) :
    generic_semantics_and (sentence_connectives L) (first_order_semantics L).
Proof. constructor. intros m p q. reflexivity. Defined.

Definition first_order_semantics_or (L : language) :
    generic_semantics_or (sentence_connectives L) (first_order_semantics L).
Proof. constructor. intros m p q. reflexivity. Defined.

Definition first_order_semantics_imp (L : language) :
    generic_semantics_imp (sentence_connectives L) (first_order_semantics L).
Proof.
  constructor. intros m p q. apply semiformula_eval_imp.
Defined.

Definition first_order_semantics_neg (L : language) :
    generic_semantics_neg (sentence_connectives L) (first_order_semantics L).
Proof.
  constructor. intros m p. apply semiformula_eval_neg.
Defined.

Definition first_order_tarski (L : language) :
    generic_tarski (sentence_connectives L) (first_order_semantics L) :=
  {| generic_tarski_top := first_order_semantics_top L;
     generic_tarski_bottom := first_order_semantics_bottom L;
     generic_tarski_and := first_order_semantics_and L;
     generic_tarski_or := first_order_semantics_or L;
     generic_tarski_imp := first_order_semantics_imp L;
     generic_tarski_neg := first_order_semantics_neg L |}.

(** * Models, validity, satisfiability, and consequence *)

Definition first_order_models_theory {L}
    (m : first_order_model L) (T : theory L) : Prop :=
  generic_models_set (first_order_semantics L) m T.

Definition first_order_valid {L} (p : sentence L) : Prop :=
  generic_valid (first_order_semantics L) p.

Definition first_order_satisfiable {L} (T : theory L) : Prop :=
  generic_satisfiable (first_order_semantics L) T.

Definition first_order_consequence {L}
    (T : theory L) (p : sentence L) : Prop :=
  generic_consequence (first_order_semantics L) T p.

Lemma first_order_models_theory_iff :
  forall L (m : first_order_model L) (T : theory L),
    first_order_models_theory m T <->
    forall p, T p -> first_order_model_realize m p.
Proof. intros; apply generic_models_set_iff. Qed.

Lemma first_order_models_of_member :
  forall L (m : first_order_model L) (T : theory L) p,
    first_order_models_theory m T -> T p ->
    first_order_model_realize m p.
Proof.
  intros L m T p Hmodels Hp.
  exact (generic_models_set_elim Hmodels Hp).
Qed.

Lemma first_order_models_of_subset :
  forall L (m : first_order_model L) (T U : theory L),
    first_order_models_theory m U ->
    (forall p, T p -> U p) ->
    first_order_models_theory m T.
Proof.
  intros. eapply generic_models_set_of_subset; eauto.
Qed.

Lemma first_order_models_union_iff :
  forall L (m : first_order_model L) (T U : theory L),
    first_order_models_theory m (fun p => T p \/ U p) <->
    first_order_models_theory m T /\ first_order_models_theory m U.
Proof. intros; apply generic_models_set_union_iff. Qed.

Lemma first_order_valid_iff :
  forall L (p : sentence L),
    first_order_valid p <->
    forall m : first_order_model L, first_order_model_realize m p.
Proof. reflexivity. Qed.

Lemma first_order_satisfiable_iff :
  forall L (T : theory L),
    first_order_satisfiable T <->
    exists m : first_order_model L, first_order_models_theory m T.
Proof. reflexivity. Qed.

Lemma first_order_unsatisfiable_iff :
  forall L (T : theory L),
    ~ first_order_satisfiable T <->
    forall m : first_order_model L, ~ first_order_models_theory m T.
Proof.
  intros. unfold first_order_satisfiable. split.
  - intros H m Hm. apply H. now exists m.
  - intros H [m Hm]. exact (H m Hm).
Qed.

Lemma first_order_satisfiable_intro :
  forall L (T : theory L) (m : first_order_model L),
    first_order_models_theory m T -> first_order_satisfiable T.
Proof. intros; now exists m. Qed.

Lemma first_order_consequence_iff :
  forall L (T : theory L) (p : sentence L),
    first_order_consequence T p <->
    forall m : first_order_model L,
      first_order_models_theory m T -> first_order_model_realize m p.
Proof. reflexivity. Qed.

Lemma first_order_consequence_iff_unsatisfiable :
  forall L (T : theory L) (p : sentence L),
    first_order_consequence T p <->
    ~ first_order_satisfiable
      (fun q => q = semiformula_neg p \/ T q).
Proof.
  intros. unfold first_order_consequence, first_order_satisfiable.
  change
    (generic_consequence (first_order_semantics L) T p <->
     ~ generic_satisfiable (first_order_semantics L)
       (fun q => q = generic_neg (sentence_connectives L) p \/ T q)).
  apply generic_consequence_iff_not_satisfiable.
  apply first_order_semantics_neg.
Qed.

Lemma first_order_consequence_weakening :
  forall L (T U : theory L) (p : sentence L),
    first_order_consequence T p ->
    (forall q, T q -> U q) ->
    first_order_consequence U p.
Proof.
  intros L T U p HT Hsubset.
  exact (generic_consequence_weakening HT Hsubset).
Qed.

Lemma first_order_consequence_of_member :
  forall L (T : theory L) (p : sentence L),
    T p -> first_order_consequence T p.
Proof.
  intros L T p Hp. exact (generic_consequence_of_mem Hp).
Qed.

(** A model's complete theory and its immediate laws. *)
Definition first_order_model_theory {L}
    (m : first_order_model L) : theory L :=
  generic_theory (first_order_semantics L) m.

Lemma first_order_model_theory_spec :
  forall L (m : first_order_model L) p,
    first_order_model_theory m p <-> first_order_model_realize m p.
Proof. reflexivity. Qed.

Lemma first_order_model_models_own_theory :
  forall L (m : first_order_model L),
    first_order_models_theory m (first_order_model_theory m).
Proof. intros; apply generic_models_theory. Qed.

Lemma first_order_model_theory_satisfiable :
  forall L (m : first_order_model L),
    first_order_satisfiable (first_order_model_theory m).
Proof. intros; apply generic_theory_satisfiable. Qed.

Lemma first_order_theory_subset_model_theory_iff :
  forall L (m : first_order_model L) (T : theory L),
    (forall p, T p -> first_order_model_theory m p) <->
    first_order_models_theory m T.
Proof.
  intros; split.
  - intro H. constructor. intros p Hp. apply H. exact Hp.
  - intros H p Hp. exact (generic_models_set_elim H Hp).
Qed.

(** * Change of language *)

Definition first_order_model_language_pullback {L K}
    (h : language_hom L K) (m : first_order_model K) :
    first_order_model L :=
  {| first_order_model_domain := first_order_model_domain m;
     first_order_model_nonempty := first_order_model_nonempty m;
     first_order_model_structure :=
       first_order_structure_language_map h
         (first_order_model_structure m) |}.

Lemma first_order_model_realize_language_map :
  forall L K (h : language_hom L K) (m : first_order_model K)
         (p : sentence L),
    first_order_model_realize m (semiformula_language_map h p) <->
    first_order_model_realize (first_order_model_language_pullback h m) p.
Proof.
  intros. unfold first_order_model_realize, sentence_realize, formula_eval.
  apply semiformula_eval_language_map.
Qed.

Theorem first_order_consequence_language_map :
  forall L K (h : language_hom L K) (T : theory L) (p : sentence L),
    first_order_consequence T p ->
    first_order_consequence (theory_language_map h T)
      (semiformula_language_map h p).
Proof.
  intros L K h T p Hconsequence m Hmapped.
  apply (proj2 (first_order_model_realize_language_map h m p)).
  apply Hconsequence.
  constructor. intros q Hq.
  apply (proj1 (first_order_model_realize_language_map h m q)).
  apply (generic_models_set_elim Hmapped).
  exists q. split; [exact Hq | reflexivity].
Qed.
