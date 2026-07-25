(**
  The standard translation from modal logic into first-order logic.

  The target is a genuine deep syntax for the relational first-order fragment
  needed by modal logic: one unary predicate for each modal atom, one binary
  accessibility relation, falsity, implication, and universal quantification.
  Variables are De Bruijn indices.  This keeps the development independent of
  the repository's set-theoretic first-order language, whose single binary
  predicate cannot directly represent the family of modal valuations.

  The construction ports the semantic correspondence in
  FormalizedFormalLogic/Foundation/Modal/VanBentham/StandardTranslation.lean
  at the repository's pinned, read-only upstream revision.  Foundation states
  the translation for negation-normal formulas; translating this repository's
  primitive [Atom]/[Bottom]/[Imp]/[Box] syntax directly gives a slightly
  stronger and smaller theorem.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax Kripke.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * A deep relational first-order fragment *)

Inductive fo_formula (AtomType : Type) : Type :=
| FOPred : AtomType -> nat -> fo_formula AtomType
| FOEdge : nat -> nat -> fo_formula AtomType
| FOBottom : fo_formula AtomType
| FOImp : fo_formula AtomType -> fo_formula AtomType -> fo_formula AtomType
| FOAll : fo_formula AtomType -> fo_formula AtomType.

Arguments FOPred {AtomType} _ _.
Arguments FOEdge {AtomType} _ _.
Arguments FOBottom {AtomType}.
Arguments FOImp {AtomType} _ _.
Arguments FOAll {AtomType} _.

Definition FONeg {AtomType} (p : fo_formula AtomType) : fo_formula AtomType :=
  FOImp p FOBottom.

(** Classical conjunction and existential quantification are definable from
    the primitive fragment.  They are used only to display the familiar
    existential standard translation of diamond. *)
Definition FOAnd {AtomType} (p q : fo_formula AtomType)
    : fo_formula AtomType :=
  FONeg (FOImp p (FONeg q)).

Definition FOEx {AtomType} (p : fo_formula AtomType) : fo_formula AtomType :=
  FONeg (FOAll (FONeg p)).

Record fo_structure (AtomType : Type) : Type := {
  fo_domain : Type;
  fo_predicate : AtomType -> fo_domain -> Prop;
  fo_accessibility : fo_domain -> fo_domain -> Prop
}.

Arguments fo_domain {AtomType} _.
Arguments fo_predicate {AtomType} _ _ _.
Arguments fo_accessibility {AtomType} _ _ _.

(** Extend an environment underneath one quantifier.  Index [0] denotes the
    newly bound element and index [S n] denotes the old index [n]. *)
Definition push_env {D : Type} (d : D) (e : nat -> D) : nat -> D :=
  fun n =>
    match n with
    | 0 => d
    | S k => e k
    end.

Lemma push_env_zero :
  forall (D : Type) (d : D) (e : nat -> D), push_env d e 0 = d.
Proof. reflexivity. Qed.

Lemma push_env_succ :
  forall (D : Type) (d : D) (e : nat -> D) n,
    push_env d e (S n) = e n.
Proof. reflexivity. Qed.

Fixpoint fo_satisfies {AtomType} (S : fo_structure AtomType)
    (e : nat -> fo_domain S) (p : fo_formula AtomType) : Prop :=
  match p with
  | FOPred a x => fo_predicate S a (e x)
  | FOEdge x y => fo_accessibility S (e x) (e y)
  | FOBottom => False
  | FOImp q r => @fo_satisfies AtomType S e q ->
                 @fo_satisfies AtomType S e r
  | FOAll q => forall d, @fo_satisfies AtomType S (push_env d e) q
  end.

Arguments fo_satisfies {AtomType} S e p.

Definition fo_valid {AtomType} (S : fo_structure AtomType)
    (p : fo_formula AtomType) : Prop :=
  forall e : nat -> fo_domain S, fo_satisfies S e p.

Lemma fo_satisfies_neg :
  forall AtomType (S : fo_structure AtomType) e (p : fo_formula AtomType),
    fo_satisfies S e (FONeg p) <-> ~ fo_satisfies S e p.
Proof. reflexivity. Qed.

Lemma fo_satisfies_and :
  forall AtomType (S : fo_structure AtomType) e
         (p q : fo_formula AtomType),
    fo_satisfies S e (FOAnd p q) <->
      fo_satisfies S e p /\ fo_satisfies S e q.
Proof.
  intros; unfold FOAnd, FONeg; simpl; tauto.
Qed.

Lemma fo_satisfies_ex :
  forall AtomType (S : fo_structure AtomType) e (p : fo_formula AtomType),
    fo_satisfies S e (FOEx p) <->
      exists d, fo_satisfies S (push_env d e) p.
Proof.
  intros AtomType S e p; unfold FOEx, FONeg; simpl.
  split.
  - intro H. apply NNPP. intro Hnone. apply H.
    intros d Hd. apply Hnone. now exists d.
  - intros [d Hd] Hall. exact (Hall d Hd).
Qed.

(** * Translation and its induced structure *)

Fixpoint standard_translation {AtomType} (p : formula AtomType)
    : fo_formula AtomType :=
  match p with
  | Atom a => FOPred a 0
  | Bottom => FOBottom
  | Imp q r => FOImp (standard_translation q) (standard_translation r)
  | Box q =>
      FOAll (FOImp (FOEdge 1 0) (standard_translation q))
  end.

Definition universal_closure {AtomType} (p : formula AtomType)
    : fo_formula AtomType :=
  FOAll (standard_translation p).

Definition modal_fo_structure {AtomType} (F : frame)
    (V : valuation AtomType F) : fo_structure AtomType :=
  {| fo_domain := World F;
     fo_predicate := V;
     fo_accessibility := Rel F |}.

Arguments modal_fo_structure {AtomType} F V.

(** Satisfaction of the translated formula at an arbitrary environment is
    exactly modal satisfaction at the environment's current world [e 0].
    Generalizing over [e] is the key De Bruijn invariant: in the box case,
    [push_env u e] maps [0] to the successor [u] and [1] to the old current
    world [e 0]. *)
Theorem standard_translation_correct :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (e : nat -> World F) (p : formula AtomType),
    satisfies F V (e 0) p <->
      fo_satisfies (modal_fo_structure F V) e (standard_translation p).
Proof.
  intros AtomType F V e p; revert e.
  induction p as [a | | p IHp q IHq | p IHp]; intro e; simpl.
  - reflexivity.
  - tauto.
  - rewrite <- (IHp e), <- (IHq e). reflexivity.
  - split.
    + intros H u Rwu.
      apply (proj1 (IHp (push_env u e))).
      apply H. exact Rwu.
    + intros H u Rwu.
      apply (proj2 (IHp (push_env u e))).
      apply H. exact Rwu.
Qed.

Corollary standard_translation_at_current_world :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (w : World F) (e : nat -> World F) (p : formula AtomType),
    satisfies F V w p <->
      fo_satisfies (modal_fo_structure F V) (push_env w e)
        (standard_translation p).
Proof.
  intros AtomType F V w e p.
  exact (@standard_translation_correct AtomType F V (push_env w e) p).
Qed.

(** Universal closure removes the distinguished current-world variable.  The
    statement is independent of the otherwise arbitrary outer environment. *)
Theorem universal_closure_correct :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (e : nat -> World F) (p : formula AtomType),
    fo_satisfies (modal_fo_structure F V) e (universal_closure p) <->
      @model_valid AtomType F V p.
Proof.
  intros AtomType F V e p; unfold universal_closure, model_valid; simpl.
  split.
  - intros H w.
    apply (proj2 (@standard_translation_correct
      AtomType F V (push_env w e) p)).
    apply H.
  - intros H w.
    apply (proj1 (@standard_translation_correct
      AtomType F V (push_env w e) p)).
    apply H.
Qed.

Theorem standard_translation_model_validity :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (p : formula AtomType),
    @model_valid AtomType F V p <->
      fo_valid (modal_fo_structure F V) (universal_closure p).
Proof.
  intros AtomType F V p; split.
  - intros H e.
    apply (proj2 (@universal_closure_correct AtomType F V e p)). exact H.
  - intros H w.
    pose (e := fun _ : nat => w).
    pose proof (H e) as Hclosed.
    pose proof (proj1 (@universal_closure_correct AtomType F V e p) Hclosed)
      as Hvalid.
    exact (Hvalid w).
Qed.

(** * The familiar existential translation of diamond *)

Definition diamond_existential_translation {AtomType}
    (p : formula AtomType) : fo_formula AtomType :=
  FOEx (FOAnd (FOEdge 1 0) (standard_translation p)).

Theorem diamond_existential_translation_correct :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (e : nat -> World F) (p : formula AtomType),
    satisfies F V (e 0) (Dia p) <->
      fo_satisfies (modal_fo_structure F V) e
        (diamond_existential_translation p).
Proof.
  intros AtomType F V e p.
  rewrite satisfies_dia.
  unfold diamond_existential_translation.
  rewrite fo_satisfies_ex.
  split.
  - intros [u [Rwu Hu]]. exists u.
    apply (proj2 (@fo_satisfies_and AtomType
      (modal_fo_structure F V) (push_env u e)
      (FOEdge 1 0) (standard_translation p))).
    split.
    + exact Rwu.
    + apply (proj1 (@standard_translation_correct
        AtomType F V (push_env u e) p)).
      exact Hu.
  - intros [u Hu].
    apply (proj1 (@fo_satisfies_and AtomType
      (modal_fo_structure F V) (push_env u e)
      (FOEdge 1 0) (standard_translation p))) in Hu.
    destruct Hu as [Rwu Hu]. exists u; split.
    + exact Rwu.
    + apply (proj2 (@standard_translation_correct
        AtomType F V (push_env u e) p)).
      exact Hu.
Qed.

Corollary standard_translation_diamond_is_existential :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (e : nat -> World F) (p : formula AtomType),
    fo_satisfies (modal_fo_structure F V) e
        (standard_translation (Dia p)) <->
      fo_satisfies (modal_fo_structure F V) e
        (diamond_existential_translation p).
Proof.
  intros AtomType F V e p.
  rewrite <- diamond_existential_translation_correct.
  symmetry. apply (@standard_translation_correct AtomType F V e (Dia p)).
Qed.
