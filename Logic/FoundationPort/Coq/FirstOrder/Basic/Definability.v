(**
  Formula definability over an arbitrary first-order structure.

  This ports the foundational closure layer of
  [Foundation/FirstOrder/Basic/Definability.lean].  Witnesses live in [Type],
  so finite constructions can carry formulas directly without choice.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Closed definitions and definitions with parameters *)

Definition first_order_is_defined_by {L M k}
    (Str : first_order_structure L M) (P : (Fin.t k -> M) -> Prop)
    (p : semisentence L k) : Prop :=
  forall v, semiformula_eval Str v
    (fun x : Empty_set => match x with end) p <-> P v.

Record first_order_defined {L M k} (Str : first_order_structure L M)
    (P : (Fin.t k -> M) -> Prop) (p : semisentence L k) : Prop := {
  first_order_defined_spec : first_order_is_defined_by Str P p
}.

Definition first_order_is_defined_by_with_params {L M k}
    (Str : first_order_structure L M) (P : (Fin.t k -> M) -> Prop)
    (p : semiformula L M k) : Prop :=
  forall v, semiformula_eval Str v (fun x => x) p <-> P v.

(** Unlike Lean's Prop-valued class, this witness package is data.  Closure
    constructions therefore need neither choice nor proof-to-data
    elimination. *)
Record first_order_definable {L M k} (Str : first_order_structure L M)
    (P : (Fin.t k -> M) -> Prop) : Type := {
  first_order_definable_formula : semiformula L M k;
  first_order_definable_spec :
    first_order_is_defined_by_with_params Str P
      first_order_definable_formula
}.

Definition first_order_defined_function {L M k}
    (Str : first_order_structure L M) (f : (Fin.t k -> M) -> M)
    (p : semisentence L (S k)) : Prop :=
  first_order_defined Str
    (fun v => v Fin.F1 = f (fun i => v (Fin.FS i))) p.

Definition first_order_definable_function {L M k}
    (Str : first_order_structure L M) (f : (Fin.t k -> M) -> M) : Type :=
  first_order_definable Str
    (fun v : Fin.t (S k) -> M =>
      v Fin.F1 = f (fun i => v (Fin.FS i))).

Definition first_order_definable_predicate {L M}
    (Str : first_order_structure L M) (P : M -> Prop) : Type :=
  first_order_definable Str (fun v : Fin.t 1 -> M => P (v Fin.F1)).

Definition first_order_definable_relation {L M}
    (Str : first_order_structure L M) (R : M -> M -> Prop) : Type :=
  first_order_definable Str
    (fun v : Fin.t 2 -> M => R (v Fin.F1) (v (Fin.FS Fin.F1))).

Definition semiformula_embed_empty {L X n}
    (p : semiformula L Empty_set n) : semiformula L X n :=
  semiformula_rewrite
    (@rew_emb L Empty_set X n (fun x => match x with end)) p.

Lemma semiformula_eval_embed_empty :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M) (p : semiformula L Empty_set n),
    semiformula_eval Str b f (semiformula_embed_empty p) <->
    semiformula_eval Str b (fun x : Empty_set => match x with end) p.
Proof.
  intros. unfold semiformula_embed_empty.
  rewrite semiformula_eval_rewrite.
  assert (Hb :
    (fun i => semiterm_val Str b f
      (rew_apply
        (@rew_emb L Empty_set X n (fun x => match x with end))
        (@Semiterm_bvar L Empty_set n i))) = b).
  { apply functional_extensionality. intro i. reflexivity. }
  assert (Hf :
    (fun x : Empty_set => semiterm_val Str b f
      (rew_apply
        (@rew_emb L Empty_set X n (fun y => match y with end))
        (@Semiterm_fvar L Empty_set n x))) =
    (fun x : Empty_set => match x with end)).
  { apply functional_extensionality. intros []. }
  now rewrite Hb, Hf.
Qed.

Theorem first_order_defined_to_definable :
  forall L M k (Str : first_order_structure L M)
         (P : (Fin.t k -> M) -> Prop) (p : semisentence L k),
    first_order_defined Str P p -> first_order_definable Str P.
Proof.
  intros L M k Str P p Hp.
  refine {| first_order_definable_formula := semiformula_embed_empty p |}.
  intro v. rewrite semiformula_eval_embed_empty.
  apply first_order_defined_spec. exact Hp.
Defined.

(** * Logical closure *)

Definition first_order_definable_of_iff {L M k}
    {Str : first_order_structure L M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HQ : first_order_definable Str Q)
    (Hiff : forall v, P v <-> Q v) : first_order_definable Str P.
Proof.
  destruct HQ as [q Hq].
  unfold first_order_is_defined_by_with_params in Hq.
  refine {| first_order_definable_formula := q |}.
  intro v. rewrite Hq. symmetry. apply Hiff.
Defined.

Definition first_order_definable_const {L M k}
    (Str : first_order_structure L M) (p : Prop) (Hp : {p} + {~ p}) :
    first_order_definable Str (fun _ : Fin.t k -> M => p).
Proof.
  destruct Hp as [Hp | Hp].
  - refine {| first_order_definable_formula := Semiformula_verum k |}.
    intro v. simpl. tauto.
  - refine {| first_order_definable_formula := Semiformula_falsum k |}.
    intro v. simpl. tauto.
Defined.

Definition first_order_definable_and {L M k}
    {Str : first_order_structure L M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : first_order_definable Str P)
    (HQ : first_order_definable Str Q) :
    first_order_definable Str (fun v => P v /\ Q v).
Proof.
  destruct HP as [p Hp], HQ as [q Hq].
  unfold first_order_is_defined_by_with_params in Hp, Hq.
  refine {| first_order_definable_formula := Semiformula_and p q |}.
  intro v. simpl. now rewrite Hp, Hq.
Defined.

Definition first_order_definable_or {L M k}
    {Str : first_order_structure L M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : first_order_definable Str P)
    (HQ : first_order_definable Str Q) :
    first_order_definable Str (fun v => P v \/ Q v).
Proof.
  destruct HP as [p Hp], HQ as [q Hq].
  unfold first_order_is_defined_by_with_params in Hp, Hq.
  refine {| first_order_definable_formula := Semiformula_or p q |}.
  intro v. simpl. now rewrite Hp, Hq.
Defined.

Definition first_order_definable_imp {L M k}
    {Str : first_order_structure L M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : first_order_definable Str P)
    (HQ : first_order_definable Str Q) :
    first_order_definable Str (fun v => P v -> Q v).
Proof.
  destruct HP as [p Hp], HQ as [q Hq].
  unfold first_order_is_defined_by_with_params in Hp, Hq.
  refine {| first_order_definable_formula := semiformula_imp p q |}.
  intro v. rewrite semiformula_eval_imp, Hp, Hq. reflexivity.
Defined.

Definition first_order_definable_not {L M k}
    {Str : first_order_structure L M}
    {P : (Fin.t k -> M) -> Prop}
    (HP : first_order_definable Str P) :
    first_order_definable Str (fun v => ~ P v).
Proof.
  destruct HP as [p Hp].
  unfold first_order_is_defined_by_with_params in Hp.
  refine {| first_order_definable_formula := semiformula_neg p |}.
  intro v. rewrite semiformula_eval_neg, Hp. reflexivity.
Defined.

Definition first_order_definable_iff {L M k}
    {Str : first_order_structure L M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : first_order_definable Str P)
    (HQ : first_order_definable Str Q) :
    first_order_definable Str (fun v => P v <-> Q v) :=
  first_order_definable_and
    (first_order_definable_imp HP HQ)
    (first_order_definable_imp HQ HP).

(** Quantifier closure is stated with the exact head/tail environment layout
    used by [semiformula_eval]. *)
Definition first_order_definable_all {L M k}
    {Str : first_order_structure L M}
    {R : (Fin.t k -> M) -> M -> Prop}
    (HR : first_order_definable Str
      (fun w : Fin.t (S k) -> M =>
        R (fun i => w (Fin.FS i)) (w Fin.F1))) :
    first_order_definable Str
      (fun v : Fin.t k -> M => forall x, R v x).
Proof.
  destruct HR as [p Hp].
  unfold first_order_is_defined_by_with_params in Hp.
  refine {| first_order_definable_formula := Semiformula_all p |}.
  intro v. simpl. setoid_rewrite Hp. reflexivity.
Defined.

Definition first_order_definable_exists {L M k}
    {Str : first_order_structure L M}
    {R : (Fin.t k -> M) -> M -> Prop}
    (HR : first_order_definable Str
      (fun w : Fin.t (S k) -> M =>
        R (fun i => w (Fin.FS i)) (w Fin.F1))) :
    first_order_definable Str
      (fun v : Fin.t k -> M => exists x, R v x).
Proof.
  destruct HR as [p Hp].
  unfold first_order_is_defined_by_with_params in Hp.
  refine {| first_order_definable_formula := Semiformula_exists p |}.
  intro v. simpl. setoid_rewrite Hp. reflexivity.
Defined.

(** * Variable retraction *)

Definition first_order_definable_retraction {L M k n}
    {Str : first_order_structure L M}
    {P : (Fin.t k -> M) -> Prop}
    (HP : first_order_definable Str P) (r : Fin.t k -> Fin.t n) :
    first_order_definable Str (fun v => P (fun i => v (r i))).
Proof.
  destruct HP as [p Hp].
  unfold first_order_is_defined_by_with_params in Hp.
  refine {| first_order_definable_formula :=
    semiformula_rewrite (rew_map r (fun x => x)) p |}.
  intro v. rewrite semiformula_eval_map. apply Hp.
Defined.

(** * Primitive and arbitrary relation operators *)

Definition first_order_definable_operator_relation {L M}
    {Str : first_order_structure L M} (o : semiformula_operator L 2)
    (R : M -> M -> Prop) (HR : structure_interprets_relation Str o R) :
    first_order_definable_relation Str R.
Proof.
  refine {| first_order_definable_formula :=
    semiformula_embed_empty (semiformula_operator_sentence o) |}.
  intro v. rewrite semiformula_eval_embed_empty.
  change (semiformula_operator_eval Str v o <->
    R (v Fin.F1) (v (Fin.FS Fin.F1))).
  assert (Hv : v = fin_two (v Fin.F1) (v (Fin.FS Fin.F1))).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      v j = fin_two (v Fin.F1) (v (Fin.FS Fin.F1)) j) eq_refl _).
    intro j. refine (@Fin.caseS' 0 j (fun q =>
      v (Fin.FS q) = fin_two (v Fin.F1) (v (Fin.FS Fin.F1)) (Fin.FS q))
      eq_refl _).
    intros q; inversion q. }
  rewrite Hv. apply structure_relation_operator. exact HR.
Defined.

Definition first_order_definable_eq {L M}
    {Str : first_order_structure L M} (H : semiformula_has_eq_operator L)
    (HEq : structure_interprets_eq Str H) :
    first_order_definable_relation Str eq.
Proof.
  apply first_order_definable_operator_relation
    with (o := semiformula_eq_operator H).
  constructor. apply structure_eq_operator. exact HEq.
Defined.

Definition first_order_definable_lt {L M}
    {Str : first_order_structure L M} (H : semiformula_has_lt_operator L)
    (lt : M -> M -> Prop) (HLt : structure_interprets_lt Str H lt) :
  first_order_definable_relation Str lt :=
  first_order_definable_operator_relation
    (o := semiformula_lt_operator H) (R := lt) HLt.

Definition first_order_definable_mem {L M}
    {Str : first_order_structure L M} (H : semiformula_has_mem_operator L)
    (mem : M -> M -> Prop) (HMem : structure_interprets_mem Str H mem) :
  first_order_definable_relation Str mem :=
  first_order_definable_operator_relation
    (o := semiformula_mem_operator H) (R := mem) HMem.
