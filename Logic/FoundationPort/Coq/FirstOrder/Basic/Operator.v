(**
  First-order term and formula operators.

  This ports the foundational operator algebra from
  [Foundation/FirstOrder/Basic/Operator.lean].  Operators are closed templates
  whose bound variables are their argument slots.  Their action is therefore
  simultaneous instantiation by [rew_emb_substs].  Keeping this description
  explicit makes composition, rewrite naturality, occurrence, and positivity
  consequences of the generic rewrite algebra, without decidable equality or
  equality of proof-carrying rewrite records.
*)

From Stdlib Require Import Lists.List Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Small finite argument vectors *)

Definition fin_zero {A : Type} (i : Fin.t 0) : A := match i with end.

Definition fin_two {A : Type} (x y : A) (i : Fin.t 2) : A :=
  @Fin.caseS' 1 i (fun _ => A) x
    (fun j => @Fin.caseS' 0 j (fun _ => A) y (fun z => match z with end)).

Lemma fin_two_first : forall A (x y : A), fin_two x y Fin.F1 = x.
Proof. reflexivity. Qed.

Lemma fin_two_second : forall A (x y : A),
  fin_two x y (Fin.FS Fin.F1) = y.
Proof. reflexivity. Qed.

(** * Semiterm operators *)

Record semiterm_operator (L : language) (arity : nat) : Type := {
  semiterm_operator_term : closed_semiterm L arity
}.

Arguments semiterm_operator_term {L arity} _.

Definition semiterm_const_operator L := semiterm_operator L 0.

Definition semiterm_operator_fn {L k}
    (f : language_func L k) : semiterm_operator L k :=
  {| semiterm_operator_term := Semiterm_func f (fun i => Semiterm_bvar i) |}.

Definition semiterm_operator_apply {L k X n}
    (o : semiterm_operator L k) (v : Fin.t k -> semiterm L X n) :
    semiterm L X n :=
  rew_apply (rew_emb_substs v) (semiterm_operator_term o).

Definition semiterm_operator_const_apply {L X n}
    (c : semiterm_const_operator L) : semiterm L X n :=
  semiterm_operator_apply c fin_zero.

Lemma semiterm_operator_ext : forall L k (o p : semiterm_operator L k),
  semiterm_operator_term o = semiterm_operator_term p -> o = p.
Proof. intros L k [o] [p]; simpl; now intros ->. Qed.

Lemma semiterm_operator_fn_apply : forall L k X n
    (f : language_func L k) (v : Fin.t k -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_fn f) v =
  Semiterm_func f v.
Proof.
  intros. unfold semiterm_operator_apply, semiterm_operator_fn; simpl.
  reflexivity.
Qed.

(** Every rewrite acts homomorphically on every operator.  The statement is
    more general than the source's specialized syntactic rewrite wrappers: the
    free-variable types and both bound arities may all change. *)
Lemma rew_semiterm_operator_apply : forall L X n Y m k
    (w : rew L X n Y m) (o : semiterm_operator L k)
    (v : Fin.t k -> semiterm L X n),
  rew_apply w (semiterm_operator_apply o v) =
  semiterm_operator_apply o (fun i => rew_apply w (v i)).
Proof.
  intros L X n Y m k w o v.
  unfold semiterm_operator_apply.
  change
    (rew_apply (rew_comp w (rew_emb_substs v))
      (semiterm_operator_term o) =
     rew_apply (rew_emb_substs (fun i => rew_apply w (v i)))
      (semiterm_operator_term o)).
  apply rew_comp_emb_substs.
Qed.

Definition semiterm_operator_comp {L k l}
    (o : semiterm_operator L k)
    (w : Fin.t k -> semiterm_operator L l) : semiterm_operator L l :=
  {| semiterm_operator_term :=
       semiterm_operator_apply o (fun i => semiterm_operator_term (w i)) |}.

Lemma semiterm_operator_comp_apply : forall L k l X n
    (o : semiterm_operator L k) (w : Fin.t k -> semiterm_operator L l)
    (v : Fin.t l -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_comp o w) v =
  semiterm_operator_apply o
    (fun i => semiterm_operator_apply (w i) v).
Proof.
  intros. unfold semiterm_operator_comp; simpl.
  apply rew_semiterm_operator_apply.
Qed.

Definition semiterm_operator_bvar {L n}
    (i : Fin.t n) : semiterm_operator L n :=
  {| semiterm_operator_term := Semiterm_bvar i |}.

Lemma semiterm_operator_bvar_apply : forall L k X n (i : Fin.t k)
    (v : Fin.t k -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_bvar (L := L) i) v = v i.
Proof. reflexivity. Qed.

Lemma semiterm_operator_comp_bvar_left : forall L k l (i : Fin.t k)
    (w : Fin.t k -> semiterm_operator L l),
  semiterm_operator_comp (semiterm_operator_bvar (L := L) i) w = w i.
Proof.
  intros. apply semiterm_operator_ext. simpl.
  apply semiterm_operator_bvar_apply.
Qed.

Lemma semiterm_operator_comp_bvar_right : forall L k
    (o : semiterm_operator L k),
  semiterm_operator_comp o
    (fun i => semiterm_operator_bvar (L := L) i) = o.
Proof.
  intros. apply semiterm_operator_ext. simpl.
  apply rew_emb_substs_variables_empty.
Qed.

Lemma semiterm_operator_comp_assoc : forall L k l r
    (o : semiterm_operator L k)
    (w : Fin.t k -> semiterm_operator L l)
    (u : Fin.t l -> semiterm_operator L r),
  semiterm_operator_comp (semiterm_operator_comp o w) u =
  semiterm_operator_comp o (fun i => semiterm_operator_comp (w i) u).
Proof.
  intros. apply semiterm_operator_ext. simpl.
  apply semiterm_operator_comp_apply.
Qed.

(** Exact occurrence and positivity laws.  Predicate-valued occurrence avoids
    the source's finite-set and decidable-equality side conditions. *)
Lemma semiterm_operator_apply_bound_occurs : forall L k X n
    (o : semiterm_operator L k) (v : Fin.t k -> semiterm L X n) j,
  semiterm_bound_occurs j (semiterm_operator_apply o v) <->
  exists i : Fin.t k,
    semiterm_bound_occurs i (semiterm_operator_term o) /\
    semiterm_bound_occurs j (v i).
Proof.
  intros. apply rew_emb_substs_bound_occurs.
Qed.

Lemma semiterm_operator_apply_positive : forall L k X n
    (o : semiterm_operator L k) (v : Fin.t k -> semiterm L X (S n)),
  semiterm_positive (semiterm_operator_apply o v) <->
  forall i, semiterm_bound_occurs i (semiterm_operator_term o) ->
    semiterm_positive (v i).
Proof.
  intros. apply rew_emb_substs_positive.
Qed.

Lemma semiterm_const_operator_positive : forall L X n
    (c : semiterm_const_operator L),
  semiterm_positive (@semiterm_operator_const_apply L X (S n) c).
Proof.
  intros. apply (proj2 (semiterm_operator_apply_positive c fin_zero)).
  intros i. inversion i.
Qed.

Fixpoint semiterm_operator_foldr {L k}
    (f : semiterm_operator L 2) (z : semiterm_operator L k)
    (os : list (semiterm_operator L k)) : semiterm_operator L k :=
  match os with
  | [] => z
  | o :: tail =>
      semiterm_operator_comp f
        (fin_two (semiterm_operator_foldr f z tail) o)
  end.

Lemma semiterm_operator_foldr_nil : forall L k
    (f : semiterm_operator L 2) (z : semiterm_operator L k),
  semiterm_operator_foldr f z [] = z.
Proof. reflexivity. Qed.

Lemma semiterm_operator_foldr_cons_apply : forall L k X n
    (f : semiterm_operator L 2) (z o : semiterm_operator L k)
    (os : list (semiterm_operator L k))
    (v : Fin.t k -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_foldr f z (o :: os)) v =
  semiterm_operator_apply f
    (fin_two
      (semiterm_operator_apply (semiterm_operator_foldr f z os) v)
      (semiterm_operator_apply o v)).
Proof.
  intros. simpl. rewrite semiterm_operator_comp_apply.
  f_equal. apply functional_extensionality. intro i.
  refine (@Fin.caseS' 1 i (fun j =>
    semiterm_operator_apply (fin_two (semiterm_operator_foldr f z os) o j) v =
    fin_two
      (semiterm_operator_apply (semiterm_operator_foldr f z os) v)
      (semiterm_operator_apply o v) j) _ _).
  - reflexivity.
  - intro j. refine (@Fin.caseS' 0 j (fun q => _) _ _).
    + reflexivity.
    + intros q; inversion q.
Qed.

(** * Semiformula operators *)

Record semiformula_operator (L : language) (arity : nat) : Type := {
  semiformula_operator_sentence : semisentence L arity
}.

Arguments semiformula_operator_sentence {L arity} _.

Definition semiformula_const_operator L := semiformula_operator L 0.

Definition semiformula_operator_apply {L k X n}
    (o : semiformula_operator L k) (v : Fin.t k -> semiterm L X n) :
    semiformula L X n :=
  semiformula_rewrite (rew_emb_substs v) (semiformula_operator_sentence o).

Definition semiformula_operator_const_apply {L X n}
    (c : semiformula_const_operator L) : semiformula L X n :=
  semiformula_operator_apply c fin_zero.

Lemma semiformula_operator_ext : forall L k (o p : semiformula_operator L k),
  semiformula_operator_sentence o = semiformula_operator_sentence p -> o = p.
Proof. intros L k [o] [p]; simpl; now intros ->. Qed.

Lemma rew_semiformula_operator_apply : forall L X n Y m k
    (w : rew L X n Y m) (o : semiformula_operator L k)
    (v : Fin.t k -> semiterm L X n),
  semiformula_rewrite w (semiformula_operator_apply o v) =
  semiformula_operator_apply o (fun i => rew_apply w (v i)).
Proof.
  intros. unfold semiformula_operator_apply.
  rewrite <- semiformula_rewrite_comp.
  apply semiformula_rewrite_ext.
  apply rew_comp_emb_substs.
Qed.

Definition semiformula_operator_comp {L k l}
    (o : semiformula_operator L k)
    (w : Fin.t k -> semiterm_operator L l) : semiformula_operator L l :=
  {| semiformula_operator_sentence :=
       semiformula_operator_apply o
         (fun i => semiterm_operator_term (w i)) |}.

Lemma semiformula_operator_comp_apply : forall L k l X n
    (o : semiformula_operator L k) (w : Fin.t k -> semiterm_operator L l)
    (v : Fin.t l -> semiterm L X n),
  semiformula_operator_apply (semiformula_operator_comp o w) v =
  semiformula_operator_apply o
    (fun i => semiterm_operator_apply (w i) v).
Proof.
  intros. unfold semiformula_operator_comp; simpl.
  apply rew_semiformula_operator_apply.
Qed.

Lemma semiformula_operator_comp_bvar_right : forall L k
    (o : semiformula_operator L k),
  semiformula_operator_comp o
    (fun i => semiterm_operator_bvar (L := L) i) = o.
Proof.
  intros. apply semiformula_operator_ext. simpl.
  transitivity
    (semiformula_rewrite (@rew_id L Empty_set k)
      (semiformula_operator_sentence o)).
  - apply semiformula_rewrite_ext.
    apply rew_emb_substs_variables_empty.
  - apply semiformula_rewrite_id.
Qed.

Lemma semiformula_operator_comp_assoc : forall L k l r
    (o : semiformula_operator L k)
    (w : Fin.t k -> semiterm_operator L l)
    (u : Fin.t l -> semiterm_operator L r),
  semiformula_operator_comp (semiformula_operator_comp o w) u =
  semiformula_operator_comp o (fun i => semiterm_operator_comp (w i) u).
Proof.
  intros. apply semiformula_operator_ext. simpl.
  apply semiformula_operator_comp_apply.
Qed.

Definition semiformula_operator_and {L k}
    (o p : semiformula_operator L k) : semiformula_operator L k :=
  {| semiformula_operator_sentence :=
       Semiformula_and (semiformula_operator_sentence o)
         (semiformula_operator_sentence p) |}.

Definition semiformula_operator_or {L k}
    (o p : semiformula_operator L k) : semiformula_operator L k :=
  {| semiformula_operator_sentence :=
       Semiformula_or (semiformula_operator_sentence o)
         (semiformula_operator_sentence p) |}.

Lemma semiformula_operator_and_apply : forall L k X n
    (o p : semiformula_operator L k) (v : Fin.t k -> semiterm L X n),
  semiformula_operator_apply (semiformula_operator_and o p) v =
  Semiformula_and (semiformula_operator_apply o v)
    (semiformula_operator_apply p v).
Proof. reflexivity. Qed.

Lemma semiformula_operator_or_apply : forall L k X n
    (o p : semiformula_operator L k) (v : Fin.t k -> semiterm L X n),
  semiformula_operator_apply (semiformula_operator_or o p) v =
  Semiformula_or (semiformula_operator_apply o v)
    (semiformula_operator_apply p v).
Proof. reflexivity. Qed.
