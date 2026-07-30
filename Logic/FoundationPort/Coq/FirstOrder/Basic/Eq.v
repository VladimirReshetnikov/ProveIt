(**
  Semantic equality axioms and congruence.

  This ports the central semantic layer of
  [Foundation/FirstOrder/Basic/Eq.lean].  Rather than tying the results to a
  particular syntactic presentation of the equality-axiom theory, the model
  laws are an explicit capability record.  This both generalizes the source
  lemmas and isolates the exact hypotheses needed by later quotient work.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Classes.RelationClasses.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_eqv {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) (a b : M) : Prop :=
  semiformula_operator_eval Str (fin_two a b)
    (semiformula_eq_operator Heq).

(** Exact semantic content of reflexivity, symmetry, transitivity, and the
    function/relation congruence axiom families. *)
Record first_order_models_equality_axioms {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) : Prop := {
  first_order_eqv_refl : forall a, first_order_eqv Str Heq a a;
  first_order_eqv_symm : forall a b,
    first_order_eqv Str Heq a b -> first_order_eqv Str Heq b a;
  first_order_eqv_trans : forall a b c,
    first_order_eqv Str Heq a b ->
    first_order_eqv Str Heq b c ->
    first_order_eqv Str Heq a c;
  first_order_eqv_func_ext : forall k (F : language_func L k)
    (v w : Fin.t k -> M),
    (forall i, first_order_eqv Str Heq (v i) (w i)) ->
    first_order_eqv Str Heq
      (structure_func Str F v) (structure_func Str F w);
  first_order_eqv_rel_ext : forall k (R : language_rel L k)
    (v w : Fin.t k -> M),
    (forall i, first_order_eqv Str Heq (v i) (w i)) ->
    (structure_rel Str R v <-> structure_rel Str R w)
}.

Arguments first_order_eqv_refl {L M Str Heq} _ _.
Arguments first_order_eqv_symm {L M Str Heq} _ _ _ _.
Arguments first_order_eqv_trans {L M Str Heq} _ _ _ _ _ _.
Arguments first_order_eqv_func_ext {L M Str Heq} _ {k} _ _ _ _.
Arguments first_order_eqv_rel_ext {L M Str Heq} _ {k} _ _ _ _.

Lemma first_order_eqv_equivalence : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L),
  first_order_models_equality_axioms Str Heq ->
  Equivalence (first_order_eqv Str Heq).
Proof.
  intros L M Str Heq H. constructor.
  - exact (first_order_eqv_refl H).
  - exact (first_order_eqv_symm H).
  - exact (first_order_eqv_trans H).
Qed.

Lemma first_order_eqv_rel_ext_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    k (R : language_rel L k) (v w : Fin.t k -> M),
  (forall i, first_order_eqv Str Heq (v i) (w i)) ->
  (structure_rel Str R v <-> structure_rel Str R w).
Proof. intros. now apply (first_order_eqv_rel_ext H). Qed.

(** A structure interpreting the chosen equality operator as Coq equality
    automatically validates every equality axiom. *)
Definition first_order_models_equality_axioms_of_interprets_eq
    {L M} (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq Str Heq) :
    first_order_models_equality_axioms Str Heq.
Proof.
  constructor.
  - intro a. unfold first_order_eqv.
    apply (proj2 (structure_eq_operator Hstd a a)). reflexivity.
  - intros a b Hab. unfold first_order_eqv in *.
    apply (proj2 (structure_eq_operator Hstd b a)). symmetry.
    now apply (proj1 (structure_eq_operator Hstd a b)).
  - intros a b c Hab Hbc. unfold first_order_eqv in *.
    apply (proj2 (structure_eq_operator Hstd a c)).
    transitivity b.
    + now apply (proj1 (structure_eq_operator Hstd a b)).
    + now apply (proj1 (structure_eq_operator Hstd b c)).
  - intros k F v w Hvw. unfold first_order_eqv in *.
    apply (proj2 (structure_eq_operator Hstd
      (structure_func Str F v) (structure_func Str F w))).
    f_equal. apply functional_extensionality. intro i.
    now apply (proj1 (structure_eq_operator Hstd (v i) (w i))).
  - intros k R v w Hvw.
    assert (Henv : v = w).
    { apply functional_extensionality. intro i.
      unfold first_order_eqv in Hvw.
      now apply (proj1 (structure_eq_operator Hstd (v i) (w i))). }
    now subst w.
Defined.

Lemma first_order_eqv_fin_env_cons : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    n (a a' : M) (b b' : Fin.t n -> M),
  first_order_eqv Str Heq a a' ->
  (forall i, first_order_eqv Str Heq (b i) (b' i)) ->
  forall i, first_order_eqv Str Heq
    (fin_env_cons a b i) (fin_env_cons a' b' i).
Proof.
  intros L M Str Heq H n a a' b b' Ha Hb i.
  refine (@Fin.caseS' n i (fun j => first_order_eqv Str Heq
    (fin_env_cons a b j) (fin_env_cons a' b' j)) Ha _).
  exact Hb.
Qed.

(** Every term respects equality-equivalent bound and free environments. *)
Theorem semiterm_val_eqv : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (b b' : Fin.t n -> M) (f f' : X -> M)
    (t : semiterm L X n),
  (forall i, first_order_eqv Str Heq (b i) (b' i)) ->
  (forall x, first_order_eqv Str Heq (f x) (f' x)) ->
  first_order_eqv Str Heq
    (semiterm_val Str b f t) (semiterm_val Str b' f' t).
Proof.
  intros L M X n Str Heq H b b' f f' t Hb Hf.
  induction t as [i | x | k F v IH]; simpl.
  - exact (Hb i).
  - exact (Hf x).
  - apply (first_order_eqv_func_ext H). exact IH.
Qed.

(** Consequently every formula is invariant under pointwise
    equality-equivalent environments. *)
Theorem semiformula_eval_eqv : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (p : semiformula L X n) (b b' : Fin.t n -> M)
    (f f' : X -> M),
  (forall i, first_order_eqv Str Heq (b i) (b' i)) ->
  (forall x, first_order_eqv Str Heq (f x) (f' x)) ->
  (semiformula_eval Str b f p <-> semiformula_eval Str b' f' p).
Proof.
  intros L M X n Str Heq H p.
  induction p as [n0 | n0 | n0 k R v | n0 k R v |
    n0 p IHp q IHq | n0 p IHp q IHq | n0 p IHp | n0 p IHp];
    intros b b' f f' Hb Hf; simpl; try tauto.
  - apply (first_order_eqv_rel_ext H). intro i.
    exact (@semiterm_val_eqv L M X n0 Str Heq H
      b b' f f' (v i) Hb Hf).
  - pose proof (first_order_eqv_rel_ext H R
      (fun i => semiterm_val Str b f (v i))
      (fun i => semiterm_val Str b' f' (v i))) as Hrel.
    specialize (Hrel (fun i => @semiterm_val_eqv L M X n0 Str Heq H
      b b' f f' (v i) Hb Hf)). tauto.
  - rewrite (IHp b b' f f' Hb Hf), (IHq b b' f f' Hb Hf).
    tauto.
  - rewrite (IHp b b' f f' Hb Hf), (IHq b b' f f' Hb Hf).
    tauto.
  - split; intros Hall x.
    + apply (proj1 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)).
      exact (Hall x).
    + apply (proj2 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)).
      exact (Hall x).
  - split; intros Hex.
    + destruct Hex as [x Hx]. exists x.
      apply (proj1 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)). exact Hx.
    + destruct Hex as [x Hx]. exists x.
      apply (proj2 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)). exact Hx.
Qed.
