(**
  Set-theoretic wrappers for the semantic Skolem hull.

  This ports the mathematical content of
  [Foundation/FirstOrder/SetTheory/LoewenheimSkolem.lean] after factoring
  the generic construction into [FirstOrder/Skolemization/Hull.v].  The
  concrete SetStructure/typeclass and countability packaging is deliberately
  replaced by an explicit membership structure and an optional seed predicate.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics ModelTheory Elementary OperatorSemantics.
From Foundation.FirstOrder.SetTheory Require Import Basic.
From Foundation.FirstOrder.Skolemization Require Import Hull.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ModelTheory.

Definition set_theory_eq_operator : semiformula_has_eq_operator set_language :=
  semiformula_eq_operator_of_language set_language_eq.

Lemma set_standard_structure_interprets_eq : forall m,
  structure_interprets_eq (set_standard_structure m)
    set_theory_eq_operator.
Proof.
  intros m. constructor. intros a b.
  unfold semiformula_operator_eval, set_theory_eq_operator,
    semiformula_eq_operator_of_language.
  simpl.
  change (structure_rel (set_standard_structure m) SetEq
    (fin_two a b) <-> a = b).
  rewrite set_standard_structure_eq.
  reflexivity.
Qed.

Definition set_hull {m : membership_structure}
    (Hinh : inhabited (membership_carrier m))
    (seed : membership_carrier m -> Prop)
    (x : membership_carrier m) : Prop :=
  skolem_hull Hinh (set_standard_structure m) seed x.

Definition set_hull_structure {m : membership_structure}
    (Hinh : inhabited (membership_carrier m))
    (seed : membership_carrier m -> Prop) :
    first_order_structure set_language
      {x : membership_carrier m | set_hull Hinh seed x} :=
  @skolem_hull_structure set_language (membership_carrier m) Hinh
    (set_standard_structure m) seed set_theory_eq_operator
    (set_standard_structure_interprets_eq m).

Lemma set_hull_subset : forall m (Hinh : inhabited (membership_carrier m)) seed x,
  seed x -> set_hull Hinh seed x.
Proof.
  intros. unfold set_hull. apply skolem_hull_subset; assumption.
Qed.

Lemma set_hull_closed : forall m (Hinh : inhabited (membership_carrier m)) seed
    k (phi : set_semisentence (Datatypes.S k)) (v : Fin.t k -> membership_carrier m),
  (forall i, set_hull Hinh seed (v i)) ->
  (exists z, semiformula_eval (set_standard_structure m)
      (fin_env_cons z v) (fun x : Empty_set => match x with end) phi) ->
  exists z, set_hull Hinh seed z /\
    semiformula_eval (set_standard_structure m)
      (fin_env_cons z v) (fun x : Empty_set => match x with end) phi.
Proof.
  intros m Hinh seed k phi v Hv Hex.
  unfold set_hull in *. apply (@skolem_hull_closed set_language
    (membership_carrier m) Hinh (set_standard_structure m) seed k phi v Hv Hex).
Qed.

Lemma set_hull_models_iff : forall m (Hinh : inhabited (membership_carrier m)) seed
    n (b : Fin.t n -> {x : membership_carrier m | set_hull Hinh seed x})
    (phi : set_semisentence n),
  semiformula_eval (set_hull_structure Hinh seed) b
    (fun x : Empty_set => match x with end) phi <->
  semiformula_eval (set_standard_structure m)
    (fun i => proj1_sig (b i)) (fun x : Empty_set => match x with end) phi.
Proof.
  intros m Hinh seed n b phi.
  unfold set_hull_structure, set_hull.
  apply (@skolem_hull_semiformula_eval set_language
    (membership_carrier m) Hinh (set_standard_structure m) seed
    set_theory_eq_operator (set_standard_structure_interprets_eq m)
    n b phi).
Qed.

Lemma set_hull_nonempty : forall m (Hinh : inhabited (membership_carrier m)) seed,
  exists x, set_hull Hinh seed x.
Proof.
  intros. unfold set_hull. apply (skolem_hull_nonempty Hinh
    (set_standard_structure m) seed).
Qed.

Definition set_hull_inhabited : forall m
    (Hinh : inhabited (membership_carrier m)) seed,
  inhabited {x : membership_carrier m | set_hull Hinh seed x} :=
  fun m Hinh seed =>
    @skolem_hull_inhabited set_language (membership_carrier m) Hinh
      (set_standard_structure m) seed.

Theorem set_hull_elementary_equiv : forall m
    (Hinh : inhabited (membership_carrier m)) seed,
  first_order_elementary_equiv
    (first_order_model_of_structure (set_hull_inhabited Hinh seed)
      (set_hull_structure Hinh seed))
    (first_order_model_of_structure Hinh (set_standard_structure m)).
Proof.
  intros. unfold set_hull_inhabited, set_hull_structure, set_hull.
  apply (@skolem_hull_elementary_equiv set_language
    (membership_carrier m) Hinh (set_standard_structure m) seed
    set_theory_eq_operator (set_standard_structure_interprets_eq m)).
Qed.
