(** Semantic Zermelo and Zermelo--Fraenkel axiom families.

    The Lean source first represents these axioms as first-order sentences
    and then groups the sentences into theories.  This module factors out
    the representation-independent content: axiom codes are interpreted
    directly over an arbitrary membership structure, while theory inclusion
    and model transport are proved once for every axiom family.

    Separation and replacement are indexed by arbitrary predicates and
    relations.  A later syntax adapter may restrict those indices to the
    predicates represented by first-order formulas without changing any of
    the hierarchy proofs below. *)

From Foundation.FirstOrder.SetTheory.Basic Require Import Model.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition set_model_successor {m : membership_structure}
    (successor x : membership_carrier m) : Prop :=
  forall z, membership_rel z successor <->
    z = x \/ membership_rel z x.

Inductive set_axiom_code (m : membership_structure) : Type :=
| set_axiom_equality_logic
| set_axiom_empty
| set_axiom_extensionality
| set_axiom_pairing
| set_axiom_union
| set_axiom_power
| set_axiom_infinity
| set_axiom_foundation
| set_axiom_separation (P : membership_carrier m -> Prop)
| set_axiom_replacement
    (R : membership_carrier m -> membership_carrier m -> Prop)
| set_axiom_choice.

Arguments set_axiom_equality_logic {m}.
Arguments set_axiom_empty {m}.
Arguments set_axiom_extensionality {m}.
Arguments set_axiom_pairing {m}.
Arguments set_axiom_union {m}.
Arguments set_axiom_power {m}.
Arguments set_axiom_infinity {m}.
Arguments set_axiom_foundation {m}.
Arguments set_axiom_separation {m} P.
Arguments set_axiom_replacement {m} R.
Arguments set_axiom_choice {m}.

Definition set_axiom_holds {m : membership_structure}
    (a : set_axiom_code m) : Prop :=
  match a with
  | set_axiom_equality_logic => True
  | set_axiom_empty =>
      exists e : membership_carrier m, @set_model_is_empty m e
  | set_axiom_extensionality =>
      membership_extensional m
  | set_axiom_pairing =>
      forall x y : membership_carrier m,
        exists p : membership_carrier m,
          forall z : membership_carrier m,
            @membership_rel m z p <-> z = x \/ z = y
  | set_axiom_union =>
      forall x : membership_carrier m,
        exists u : membership_carrier m,
          forall z : membership_carrier m,
            @membership_rel m z u <->
              exists y : membership_carrier m,
                @membership_rel m y x /\ @membership_rel m z y
  | set_axiom_power =>
      forall x : membership_carrier m,
        exists p : membership_carrier m,
          forall z : membership_carrier m,
            @membership_rel m z p <-> @set_model_subset m z x
  | set_axiom_infinity =>
      exists i : membership_carrier m,
        (forall e : membership_carrier m,
          @set_model_is_empty m e -> @membership_rel m e i) /\
        (forall x : membership_carrier m, @membership_rel m x i ->
          forall successor : membership_carrier m,
            @set_model_successor m successor x ->
            @membership_rel m successor i)
  | set_axiom_foundation =>
      forall x : membership_carrier m, @set_model_is_nonempty m x ->
        exists y : membership_carrier m, @membership_rel m y x /\
          forall z : membership_carrier m,
            @membership_rel m z x -> ~ @membership_rel m z y
  | set_axiom_separation P =>
      forall x : membership_carrier m,
        exists y : membership_carrier m,
          forall z : membership_carrier m,
            @membership_rel m z y <-> @membership_rel m z x /\ P z
  | set_axiom_replacement R =>
      (forall x : membership_carrier m,
        exists! y : membership_carrier m, R x y) ->
      forall x : membership_carrier m,
        exists y : membership_carrier m,
          forall z : membership_carrier m,
            @membership_rel m z y <->
              exists w : membership_carrier m,
                @membership_rel m w x /\ R w z
  | set_axiom_choice =>
      forall collection : membership_carrier m,
        (forall x : membership_carrier m,
          @membership_rel m x collection -> @set_model_is_nonempty m x) ->
        (forall x y : membership_carrier m,
          @membership_rel m x collection ->
          @membership_rel m y collection ->
          (exists z : membership_carrier m,
            @membership_rel m z x /\ @membership_rel m z y) ->
          x = y) ->
        exists choice : membership_carrier m,
          forall x : membership_carrier m,
            @membership_rel m x collection ->
            exists! z : membership_carrier m,
              @membership_rel m z choice /\ @membership_rel m z x
  end.

Definition set_axiom_family (m : membership_structure) : Type :=
  set_axiom_code m -> Prop.

Definition set_axiom_family_subset {m : membership_structure}
    (T U : set_axiom_family m) : Prop :=
  forall a, T a -> U a.

Definition set_axiom_family_union {m : membership_structure}
    (T U : set_axiom_family m) : set_axiom_family m :=
  fun a => T a \/ U a.

Definition set_theory_model {m : membership_structure}
    (T : set_axiom_family m) : Prop :=
  forall a, T a -> set_axiom_holds a.

Lemma set_axiom_family_subset_refl : forall m (T : set_axiom_family m),
  set_axiom_family_subset T T.
Proof. firstorder. Qed.

Lemma set_axiom_family_subset_trans : forall m
    (T U V : set_axiom_family m),
  set_axiom_family_subset T U ->
  set_axiom_family_subset U V ->
  set_axiom_family_subset T V.
Proof. firstorder. Qed.

Lemma set_theory_model_of_subset : forall m
    (T U : set_axiom_family m),
  set_axiom_family_subset T U ->
  set_theory_model U -> set_theory_model T.
Proof. firstorder. Qed.

Lemma set_theory_model_union_iff : forall m
    (T U : set_axiom_family m),
  set_theory_model (set_axiom_family_union T U) <->
  set_theory_model T /\ set_theory_model U.
Proof.
  intros m T U. split.
  - intro H. split; intros a Ha; apply H; [left | right]; exact Ha.
  - intros [HT HU] a [Ha | Ha]; [now apply HT | now apply HU].
Qed.

Inductive zermelo_axiom {m : membership_structure} :
    set_axiom_family m :=
| za_equality_logic : zermelo_axiom set_axiom_equality_logic
| za_empty : zermelo_axiom set_axiom_empty
| za_extensionality : zermelo_axiom set_axiom_extensionality
| za_pairing : zermelo_axiom set_axiom_pairing
| za_union : zermelo_axiom set_axiom_union
| za_power : zermelo_axiom set_axiom_power
| za_infinity : zermelo_axiom set_axiom_infinity
| za_foundation : zermelo_axiom set_axiom_foundation
| za_separation : forall P, zermelo_axiom (set_axiom_separation P).

Inductive zf_axiom {m : membership_structure} : set_axiom_family m :=
| zfa_equality_logic : zf_axiom set_axiom_equality_logic
| zfa_empty : zf_axiom set_axiom_empty
| zfa_extensionality : zf_axiom set_axiom_extensionality
| zfa_pairing : zf_axiom set_axiom_pairing
| zfa_union : zf_axiom set_axiom_union
| zfa_power : zf_axiom set_axiom_power
| zfa_infinity : zf_axiom set_axiom_infinity
| zfa_foundation : zf_axiom set_axiom_foundation
| zfa_separation : forall P, zf_axiom (set_axiom_separation P)
| zfa_replacement : forall R, zf_axiom (set_axiom_replacement R).

Inductive choice_axiom {m : membership_structure} : set_axiom_family m :=
| ca_choice : choice_axiom set_axiom_choice.

Definition zermelo_choice_axiom {m : membership_structure} :
    set_axiom_family m :=
  set_axiom_family_union zermelo_axiom choice_axiom.

Definition zfc_axiom {m : membership_structure} : set_axiom_family m :=
  set_axiom_family_union zf_axiom choice_axiom.

Lemma zermelo_axiom_subset_zf : forall m,
  @set_axiom_family_subset m zermelo_axiom zf_axiom.
Proof.
  intros m a H. destruct H.
  - apply zfa_equality_logic.
  - apply zfa_empty.
  - apply zfa_extensionality.
  - apply zfa_pairing.
  - apply zfa_union.
  - apply zfa_power.
  - apply zfa_infinity.
  - apply zfa_foundation.
  - apply zfa_separation.
Qed.

Lemma zermelo_axiom_subset_zc : forall m,
  @set_axiom_family_subset m zermelo_axiom zermelo_choice_axiom.
Proof. intros m a Ha. now left. Qed.

Lemma zf_axiom_subset_zfc : forall m,
  @set_axiom_family_subset m zf_axiom zfc_axiom.
Proof. intros m a Ha. now left. Qed.

Lemma choice_axiom_subset_zc : forall m,
  @set_axiom_family_subset m choice_axiom zermelo_choice_axiom.
Proof. intros m a Ha. now right. Qed.

Lemma choice_axiom_subset_zfc : forall m,
  @set_axiom_family_subset m choice_axiom zfc_axiom.
Proof. intros m a Ha. now right. Qed.

Lemma zermelo_choice_axiom_subset_zfc : forall m,
  @set_axiom_family_subset m zermelo_choice_axiom zfc_axiom.
Proof.
  intros m a [Ha | Ha].
  - left. now apply zermelo_axiom_subset_zf.
  - now right.
Qed.

Lemma set_zf_model_is_zermelo : forall m,
  @set_theory_model m zf_axiom ->
  @set_theory_model m zermelo_axiom.
Proof.
  intros m. apply set_theory_model_of_subset.
  apply zermelo_axiom_subset_zf.
Qed.

Lemma set_zc_model_iff_zermelo_and_choice : forall m,
  @set_theory_model m zermelo_choice_axiom <->
  @set_theory_model m zermelo_axiom /\
  @set_theory_model m choice_axiom.
Proof. intros m. apply set_theory_model_union_iff. Qed.

Lemma set_zfc_model_iff_zf_and_choice : forall m,
  @set_theory_model m zfc_axiom <->
  @set_theory_model m zf_axiom /\
  @set_theory_model m choice_axiom.
Proof. intros m. apply set_theory_model_union_iff. Qed.

Lemma set_zfc_model_is_zc : forall m,
  @set_theory_model m zfc_axiom ->
  @set_theory_model m zermelo_choice_axiom.
Proof.
  intros m. apply set_theory_model_of_subset.
  apply zermelo_choice_axiom_subset_zfc.
Qed.

Lemma set_zermelo_choice_model : forall m,
  @set_theory_model m zermelo_axiom ->
  @set_theory_model m choice_axiom ->
  @set_theory_model m zermelo_choice_axiom.
Proof.
  intros m HZ HC. apply (proj2 (set_zc_model_iff_zermelo_and_choice m)).
  now split.
Qed.

Lemma set_zf_choice_model : forall m,
  @set_theory_model m zf_axiom ->
  @set_theory_model m choice_axiom ->
  @set_theory_model m zfc_axiom.
Proof.
  intros m HZF HC. apply (proj2 (set_zfc_model_iff_zf_and_choice m)).
  now split.
Qed.

Print Assumptions zermelo_axiom_subset_zf.
Print Assumptions zermelo_choice_axiom_subset_zfc.
Print Assumptions set_zfc_model_is_zc.
