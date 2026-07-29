(**
  Semantic interpretation of first-order term and formula operators.

  This layer completes the semantic half of
  [Foundation/FirstOrder/Basic/Operator.lean].  Operator interpretation is
  defined once from the generic Tarski semantics, and the six bounded
  quantifier laws are factored through two arbitrary binary-operator lemmas.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Term operators *)

Definition semiterm_operator_val {L M k}
    (Str : first_order_structure L M) (v : Fin.t k -> M)
    (o : semiterm_operator L k) : M :=
  closed_semiterm_val Str v (semiterm_operator_term o).

Lemma semiterm_val_operator_apply :
  forall L M X n k (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (o : semiterm_operator L k) (v : Fin.t k -> semiterm L X n),
    semiterm_val Str b f (semiterm_operator_apply o v) =
    semiterm_operator_val Str
      (fun i => semiterm_val Str b f (v i)) o.
Proof.
  intros. unfold semiterm_operator_apply, semiterm_operator_val.
  apply semiterm_val_emb_substs.
Qed.

Lemma semiterm_operator_val_comp :
  forall L M k l (Str : first_order_structure L M)
         (o : semiterm_operator L k)
         (w : Fin.t k -> semiterm_operator L l) (v : Fin.t l -> M),
    semiterm_operator_val Str v (semiterm_operator_comp o w) =
    semiterm_operator_val Str
      (fun i => semiterm_operator_val Str v (w i)) o.
Proof.
  intros.
  change
    (semiterm_val Str v (fun x : Empty_set => match x with end)
      (semiterm_operator_apply o (fun i => semiterm_operator_term (w i))) =
     semiterm_operator_val Str
       (fun i => semiterm_operator_val Str v (w i)) o).
  rewrite semiterm_val_operator_apply. reflexivity.
Qed.

Lemma semiterm_operator_val_bvar :
  forall L M n (Str : first_order_structure L M)
         (i : Fin.t n) (v : Fin.t n -> M),
    semiterm_operator_val Str v
      (semiterm_operator_bvar (L := L) i) = v i.
Proof. reflexivity. Qed.

Lemma semiterm_operator_val_fn :
  forall L M k (Str : first_order_structure L M)
         (F : language_func L k) (v : Fin.t k -> M),
    semiterm_operator_val Str v (semiterm_operator_fn F) =
    structure_func Str F v.
Proof. reflexivity. Qed.

(** * Formula operators *)

Definition semiformula_operator_eval {L M k}
    (Str : first_order_structure L M) (v : Fin.t k -> M)
    (o : semiformula_operator L k) : Prop :=
  semiformula_eval Str v (fun x : Empty_set => match x with end)
    (semiformula_operator_sentence o).

Lemma semiformula_eval_operator_apply :
  forall L M X n k (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (o : semiformula_operator L k) (v : Fin.t k -> semiterm L X n),
    semiformula_eval Str b f (semiformula_operator_apply o v) <->
    semiformula_operator_eval Str
      (fun i => semiterm_val Str b f (v i)) o.
Proof.
  intros. unfold semiformula_operator_apply, semiformula_operator_eval.
  apply semiformula_eval_emb_substs.
Qed.

Lemma semiformula_operator_eval_comp :
  forall L M k l (Str : first_order_structure L M)
         (o : semiformula_operator L k)
         (w : Fin.t k -> semiterm_operator L l) (v : Fin.t l -> M),
    semiformula_operator_eval Str v (semiformula_operator_comp o w) <->
    semiformula_operator_eval Str
      (fun i => semiterm_operator_val Str v (w i)) o.
Proof.
  intros. unfold semiformula_operator_eval, semiformula_operator_comp; simpl.
  rewrite semiformula_eval_operator_apply. reflexivity.
Qed.

Lemma semiformula_operator_eval_and :
  forall L M k (Str : first_order_structure L M)
         (o p : semiformula_operator L k) (v : Fin.t k -> M),
    semiformula_operator_eval Str v (semiformula_operator_and o p) <->
    semiformula_operator_eval Str v o /\ semiformula_operator_eval Str v p.
Proof. reflexivity. Qed.

Lemma semiformula_operator_eval_or :
  forall L M k (Str : first_order_structure L M)
         (o p : semiformula_operator L k) (v : Fin.t k -> M),
    semiformula_operator_eval Str v (semiformula_operator_or o p) <->
    semiformula_operator_eval Str v o \/ semiformula_operator_eval Str v p.
Proof. reflexivity. Qed.

(** Canonical primitive relation operators expose precisely the relation
    interpretation stored in the structure. *)
Lemma semiformula_eq_operator_eval_of_language :
  forall L M (Str : first_order_structure L M) (H : language_has_eq L)
         (v : Fin.t 2 -> M),
    semiformula_operator_eval Str v
      (semiformula_eq_operator (semiformula_eq_operator_of_language H)) <->
    structure_rel Str (language_eq H) v.
Proof. reflexivity. Qed.

Lemma semiformula_lt_operator_eval_of_language :
  forall L M (Str : first_order_structure L M) (H : language_has_lt L)
         (v : Fin.t 2 -> M),
    semiformula_operator_eval Str v
      (semiformula_lt_operator (semiformula_lt_operator_of_language H)) <->
    structure_rel Str (language_lt H) v.
Proof. reflexivity. Qed.

Lemma semiformula_mem_operator_eval_of_language :
  forall L M (Str : first_order_structure L M) (H : language_has_mem L)
         (v : Fin.t 2 -> M),
    semiformula_operator_eval Str v
      (semiformula_mem_operator (semiformula_mem_operator_of_language H)) <->
    structure_rel Str (language_mem H) v.
Proof. reflexivity. Qed.

(** * Semantic capability records *)

Record structure_interprets_zero {L M} (Str : first_order_structure L M)
    (H : semiterm_has_zero_operator L) (zero : M) : Prop := {
  structure_zero_operator :
    semiterm_operator_val Str fin_zero (semiterm_zero_operator H) = zero
}.

Record structure_interprets_one {L M} (Str : first_order_structure L M)
    (H : semiterm_has_one_operator L) (one : M) : Prop := {
  structure_one_operator :
    semiterm_operator_val Str fin_zero (semiterm_one_operator H) = one
}.

Record structure_interprets_add {L M} (Str : first_order_structure L M)
    (H : semiterm_has_add_operator L) (add : M -> M -> M) : Prop := {
  structure_add_operator : forall a b,
    semiterm_operator_val Str (fin_two a b) (semiterm_add_operator H) =
    add a b
}.

Record structure_interprets_mul {L M} (Str : first_order_structure L M)
    (H : semiterm_has_mul_operator L) (mul : M -> M -> M) : Prop := {
  structure_mul_operator : forall a b,
    semiterm_operator_val Str (fin_two a b) (semiterm_mul_operator H) =
    mul a b
}.

Record structure_interprets_exp {L M} (Str : first_order_structure L M)
    (H : semiterm_has_exp_operator L) (exp : M -> M) : Prop := {
  structure_exp_operator : forall a,
    semiterm_operator_val Str (fin_one a) (semiterm_exp_operator H) = exp a
}.

Record structure_interprets_eq {L M} (Str : first_order_structure L M)
    (H : semiformula_has_eq_operator L) : Prop := {
  structure_eq_operator : forall a b,
    semiformula_operator_eval Str (fin_two a b)
      (semiformula_eq_operator H) <-> a = b
}.

Record structure_interprets_relation {L M} (Str : first_order_structure L M)
    (o : semiformula_operator L 2) (R : M -> M -> Prop) : Prop := {
  structure_relation_operator : forall a b,
    semiformula_operator_eval Str (fin_two a b) o <-> R a b
}.

Definition structure_interprets_lt {L M} (Str : first_order_structure L M)
    (H : semiformula_has_lt_operator L) (lt : M -> M -> Prop) : Prop :=
  structure_interprets_relation Str (semiformula_lt_operator H) lt.

Definition structure_interprets_le {L M} (Str : first_order_structure L M)
    (H : semiformula_has_le_operator L) (le : M -> M -> Prop) : Prop :=
  structure_interprets_relation Str (semiformula_le_operator H) le.

Definition structure_interprets_mem {L M} (Str : first_order_structure L M)
    (H : semiformula_has_mem_operator L) (mem : M -> M -> Prop) : Prop :=
  structure_interprets_relation Str (semiformula_mem_operator H) mem.

(** The equality-or-order construction receives its semantics from only the
    two component interpretations; no order laws are needed. *)
Lemma structure_interprets_le_of_eq_lt :
  forall L M (Str : first_order_structure L M)
         (Heq : semiformula_has_eq_operator L)
         (Hlt : semiformula_has_lt_operator L) (lt : M -> M -> Prop),
    structure_interprets_eq Str Heq ->
    structure_interprets_lt Str Hlt lt ->
    structure_interprets_le Str
      (semiformula_le_operator_of_eq_lt Heq Hlt)
      (fun a b => a = b \/ lt a b).
Proof.
  intros L M Str Heq Hlt lt HSemEq HSemLt.
  constructor. intros a b. simpl.
  rewrite semiformula_operator_eval_or.
  rewrite (structure_eq_operator HSemEq a b).
  rewrite (structure_relation_operator HSemLt a b).
  reflexivity.
Qed.

(** * Bounded quantifiers *)

Lemma semiterm_val_binary_bound :
  forall L M X n (Str : first_order_structure L M)
         (x : M) (b : Fin.t n -> M) (f : X -> M) (t : semiterm L X n),
    (fun i => semiterm_val Str (fin_env_cons x b) f
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t) i)) =
    fin_two x (semiterm_val Str b f t).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' 1 i (fun j =>
    semiterm_val Str (fin_env_cons x b) f
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t) j) =
    fin_two x (semiterm_val Str b f t) j) eq_refl _).
  intro j. refine (@Fin.caseS' 0 j (fun q =>
    semiterm_val Str (fin_env_cons x b) f
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t) (Fin.FS q)) =
    fin_two x (semiterm_val Str b f t) (Fin.FS q)) _ _).
  - apply semiterm_val_bshift.
  - intros q; inversion q.
Qed.

Lemma semiformula_eval_bounded_operator_all :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (o : semiformula_operator L 2) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f
      (semiformula_bounded_all
        (semiformula_operator_apply o
          (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t))) p) <->
    forall x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t)) o ->
      semiformula_eval Str (fin_env_cons x b) f p.
Proof.
  intros. rewrite semiformula_eval_bounded_all.
  setoid_rewrite semiformula_eval_operator_apply.
  setoid_rewrite semiterm_val_binary_bound.
  reflexivity.
Qed.

Lemma semiformula_eval_bounded_operator_exists :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (o : semiformula_operator L 2) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f
      (semiformula_bounded_exists
        (semiformula_operator_apply o
          (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t))) p) <->
    exists x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t)) o /\
      semiformula_eval Str (fin_env_cons x b) f p.
Proof.
  intros. rewrite semiformula_eval_bounded_exists.
  setoid_rewrite semiformula_eval_operator_apply.
  setoid_rewrite semiterm_val_binary_bound.
  reflexivity.
Qed.

Lemma semiformula_eval_ball_lt :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (H : semiformula_has_lt_operator L) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f (semiformula_ball_lt H t p) <->
    forall x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t))
        (semiformula_lt_operator H) ->
      semiformula_eval Str (fin_env_cons x b) f p.
Proof. intros; apply semiformula_eval_bounded_operator_all. Qed.

Lemma semiformula_eval_bex_lt :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (H : semiformula_has_lt_operator L) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f (semiformula_bex_lt H t p) <->
    exists x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t))
        (semiformula_lt_operator H) /\
      semiformula_eval Str (fin_env_cons x b) f p.
Proof. intros; apply semiformula_eval_bounded_operator_exists. Qed.

Lemma semiformula_eval_ball_le :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (H : semiformula_has_le_operator L) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f (semiformula_ball_le H t p) <->
    forall x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t))
        (semiformula_le_operator H) ->
      semiformula_eval Str (fin_env_cons x b) f p.
Proof. intros; apply semiformula_eval_bounded_operator_all. Qed.

Lemma semiformula_eval_bex_le :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (H : semiformula_has_le_operator L) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f (semiformula_bex_le H t p) <->
    exists x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t))
        (semiformula_le_operator H) /\
      semiformula_eval Str (fin_env_cons x b) f p.
Proof. intros; apply semiformula_eval_bounded_operator_exists. Qed.

Lemma semiformula_eval_ball_mem :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (H : semiformula_has_mem_operator L) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f (semiformula_ball_mem H t p) <->
    forall x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t))
        (semiformula_mem_operator H) ->
      semiformula_eval Str (fin_env_cons x b) f p.
Proof. intros; apply semiformula_eval_bounded_operator_all. Qed.

Lemma semiformula_eval_bex_mem :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (H : semiformula_has_mem_operator L) (t : semiterm L X n)
         (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f (semiformula_bex_mem H t p) <->
    exists x : M,
      semiformula_operator_eval Str (fin_two x (semiterm_val Str b f t))
        (semiformula_mem_operator H) /\
      semiformula_eval Str (fin_env_cons x b) f p.
Proof. intros; apply semiformula_eval_bounded_operator_exists. Qed.

(** Semantic relation capabilities turn the abstract guard laws into the
    familiar relational notation, without imposing any order or membership
    laws on the carrier. *)
Lemma semiformula_eval_ball_relation :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (o : semiformula_operator L 2) (R : M -> M -> Prop)
         (Hsem : structure_interprets_relation Str o R)
         (t : semiterm L X n) (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f
      (semiformula_bounded_all
        (semiformula_operator_apply o
          (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t))) p) <->
    forall x : M, R x (semiterm_val Str b f t) ->
      semiformula_eval Str (fin_env_cons x b) f p.
Proof.
  intros. rewrite semiformula_eval_bounded_operator_all.
  setoid_rewrite (structure_relation_operator Hsem).
  reflexivity.
Qed.

Lemma semiformula_eval_bex_relation :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (o : semiformula_operator L 2) (R : M -> M -> Prop)
         (Hsem : structure_interprets_relation Str o R)
         (t : semiterm L X n) (p : semiformula L X (Datatypes.S n)),
    semiformula_eval Str b f
      (semiformula_bounded_exists
        (semiformula_operator_apply o
          (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t))) p) <->
    exists x : M, R x (semiterm_val Str b f t) /\
      semiformula_eval Str (fin_env_cons x b) f p.
Proof.
  intros. rewrite semiformula_eval_bounded_operator_exists.
  setoid_rewrite (structure_relation_operator Hsem).
  reflexivity.
Qed.
