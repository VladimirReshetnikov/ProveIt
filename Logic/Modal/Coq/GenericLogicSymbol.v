(**
  Generic logical connectives and their homomorphisms.

  This module ports the pinned Foundation module
  [Logic/LogicSymbol.lean].  The primitive six-operation structure itself is
  [generic_connectives], defined in [GenericSemantics] and reused here.  This
  tranche centralizes the independent negation/De Morgan abbreviation laws,
  proves the involution consequences, and ports the full connective
  homomorphism identity/composition core and predicate-closure interfaces.

  Foundation proves equality of homomorphism records via function and proof
  extensionality.  Coq uses pointwise equality as the operational interface,
  so the algebra remains constructive and does not identify proof-carrying
  records merely because their underlying functions agree.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat Vectors.Fin.
From FoundationModal Require Import GenericSemantics.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Foundation's [TildeInvolutive] and five-field [DeMorgan] classes are
    split into independent laws, allowing every consumer to request only the
    equations it uses. *)
Definition generic_neg_involutive_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p, generic_neg C (generic_neg C p) = p.

Definition generic_neg_top_law {F : Type}
    (C : generic_connectives F) : Prop :=
  generic_neg C (generic_top C) = generic_bottom C.

Definition generic_neg_bottom_law {F : Type}
    (C : generic_connectives F) : Prop :=
  generic_neg C (generic_bottom C) = generic_top C.

Definition generic_imp_as_or_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p q,
    generic_imp C p q = generic_or C (generic_neg C p) q.

Definition generic_neg_and_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p q,
    generic_neg C (generic_and C p q) =
    generic_or C (generic_neg C p) (generic_neg C q).

Definition generic_neg_or_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p q,
    generic_neg C (generic_or C p q) =
    generic_and C (generic_neg C p) (generic_neg C q).

Record generic_de_morgan_laws {F : Type}
    (C : generic_connectives F) : Prop := {
  generic_de_morgan_neg_top : generic_neg_top_law C;
  generic_de_morgan_neg_bottom : generic_neg_bottom_law C;
  generic_de_morgan_imp : generic_imp_as_or_law C;
  generic_de_morgan_neg_and : generic_neg_and_law C;
  generic_de_morgan_neg_or : generic_neg_or_law C
}.

(** Foundation [NegAbbrev]. *)
Definition generic_neg_abbrev_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p,
    generic_neg C p = generic_imp C p (generic_bottom C).

(** Foundation [LukasiewiczAbbrev], with each derived connective equation
    retained explicitly. *)
Record generic_lukasiewicz_abbrev {F : Type}
    (C : generic_connectives F) : Prop := {
  generic_lukasiewicz_neg : generic_neg_abbrev_law C;
  generic_lukasiewicz_top :
    generic_top C = generic_neg C (generic_bottom C);
  generic_lukasiewicz_or :
    forall p q,
      generic_or C p q = generic_imp C (generic_neg C p) q;
  generic_lukasiewicz_and :
    forall p q,
      generic_and C p q =
      generic_neg C (generic_imp C p (generic_neg C q))
}.

(** Involutive negation is injective; no equality decision is needed. *)
Lemma generic_neg_injective :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    forall p q : F,
      generic_neg C p = generic_neg C q -> p = q.
Proof.
  intros F C Hinv p q Heq.
  pose proof (f_equal (generic_neg C) Heq) as Hneg.
  now rewrite (Hinv p), (Hinv q) in Hneg.
Qed.

Lemma generic_neg_equal_iff :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    forall p q : F,
      generic_neg C p = generic_neg C q <-> p = q.
Proof.
  intros F C Hinv p q; split.
  - exact (@generic_neg_injective F C Hinv p q).
  - now intros ->.
Qed.

(** Foundation [Tilde.invol] is represented directly by the negation map;
    injectivity is supplied by [generic_neg_injective]. *)
Definition generic_neg_embedding {F : Type}
    (C : generic_connectives F) : F -> F := generic_neg C.

Lemma generic_neg_embedding_apply :
  forall (F : Type) (C : generic_connectives F) (p : F),
    generic_neg_embedding C p = generic_neg C p.
Proof. reflexivity. Qed.

(** Foundation's derived biconditional connective. *)
Definition generic_formula_iff {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_and C (generic_imp C p q) (generic_imp C q p).

(** The direct counterpart of [LogicalConnective.Hom]. *)
Record generic_connective_hom {F G : Type}
    (CF : generic_connectives F) (CG : generic_connectives G) : Type := {
  generic_connective_hom_apply : F -> G;
  generic_connective_hom_top :
    generic_connective_hom_apply (generic_top CF) = generic_top CG;
  generic_connective_hom_bottom :
    generic_connective_hom_apply (generic_bottom CF) = generic_bottom CG;
  generic_connective_hom_neg :
    forall p,
      generic_connective_hom_apply (generic_neg CF p) =
      generic_neg CG (generic_connective_hom_apply p);
  generic_connective_hom_imp :
    forall p q,
      generic_connective_hom_apply (generic_imp CF p q) =
      generic_imp CG
        (generic_connective_hom_apply p)
        (generic_connective_hom_apply q);
  generic_connective_hom_and :
    forall p q,
      generic_connective_hom_apply (generic_and CF p q) =
      generic_and CG
        (generic_connective_hom_apply p)
        (generic_connective_hom_apply q);
  generic_connective_hom_or :
    forall p q,
      generic_connective_hom_apply (generic_or CF p q) =
      generic_or CG
        (generic_connective_hom_apply p)
        (generic_connective_hom_apply q)
}.

Arguments generic_connective_hom_apply {F G CF CG} _ _.
Arguments generic_connective_hom_top {F G CF CG} _.
Arguments generic_connective_hom_bottom {F G CF CG} _.
Arguments generic_connective_hom_neg {F G CF CG} _ _.
Arguments generic_connective_hom_imp {F G CF CG} _ _ _.
Arguments generic_connective_hom_and {F G CF CG} _ _ _.
Arguments generic_connective_hom_or {F G CF CG} _ _ _.

Lemma generic_connective_hom_iff :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (f : generic_connective_hom CF CG) (p q : F),
    generic_connective_hom_apply f (generic_formula_iff CF p q) =
    generic_formula_iff CG
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q).
Proof.
  intros F G CF CG f p q. unfold generic_formula_iff.
  rewrite (generic_connective_hom_and f),
    (generic_connective_hom_imp f),
    (generic_connective_hom_imp f).
  reflexivity.
Qed.

(** Pointwise equality replaces equality of proof-carrying homomorphism
    records and therefore needs no functional or proof extensionality. *)
Definition generic_connective_hom_equiv {F G : Type}
    {CF : generic_connectives F} {CG : generic_connectives G}
    (f g : generic_connective_hom CF CG) : Prop :=
  forall p, generic_connective_hom_apply f p =
            generic_connective_hom_apply g p.

Definition generic_connective_hom_id {F : Type}
    (C : generic_connectives F) : generic_connective_hom C C.
Proof.
  refine {| generic_connective_hom_apply := fun p => p |}; reflexivity.
Defined.

Definition generic_connective_hom_compose {F G H : Type}
    {CF : generic_connectives F}
    {CG : generic_connectives G}
    {CH : generic_connectives H}
    (g : generic_connective_hom CG CH)
    (f : generic_connective_hom CF CG) :
    generic_connective_hom CF CH.
Proof.
  refine {| generic_connective_hom_apply :=
      fun p => generic_connective_hom_apply g
        (generic_connective_hom_apply f p) |}.
  - now rewrite (generic_connective_hom_top f),
      (generic_connective_hom_top g).
  - now rewrite (generic_connective_hom_bottom f),
      (generic_connective_hom_bottom g).
  - intro p. now rewrite (generic_connective_hom_neg f),
      (generic_connective_hom_neg g).
  - intros p q. now rewrite (generic_connective_hom_imp f),
      (generic_connective_hom_imp g).
  - intros p q. now rewrite (generic_connective_hom_and f),
      (generic_connective_hom_and g).
  - intros p q. now rewrite (generic_connective_hom_or f),
      (generic_connective_hom_or g).
Defined.

Lemma generic_connective_hom_id_apply :
  forall (F : Type) (C : generic_connectives F) (p : F),
    generic_connective_hom_apply (generic_connective_hom_id C) p = p.
Proof. reflexivity. Qed.

Lemma generic_connective_hom_compose_apply :
  forall (F G H : Type)
         (CF : generic_connectives F)
         (CG : generic_connectives G)
         (CH : generic_connectives H)
         (g : generic_connective_hom CG CH)
         (f : generic_connective_hom CF CG) (p : F),
    generic_connective_hom_apply
      (generic_connective_hom_compose g f) p =
    generic_connective_hom_apply g (generic_connective_hom_apply f p).
Proof. reflexivity. Qed.

(** Foundation [LogicalConnective.AndOrClosed]. *)
Record generic_and_or_closed {F : Type}
    (C : generic_connectives F) (P : F -> Prop) : Prop := {
  generic_closed_top : P (generic_top C);
  generic_closed_bottom : P (generic_bottom C);
  generic_closed_and :
    forall p q, P p -> P q -> P (generic_and C p q);
  generic_closed_or :
    forall p q, P p -> P q -> P (generic_or C p q)
}.

(** Foundation [LogicalConnective.Closed]. *)
Record generic_connective_closed {F : Type}
    (C : generic_connectives F) (P : F -> Prop) : Prop := {
  generic_connective_closed_and_or : generic_and_or_closed C P;
  generic_closed_neg : forall p, P p -> P (generic_neg C p);
  generic_closed_imp :
    forall p q, P p -> P q -> P (generic_imp C p q)
}.

Arguments generic_de_morgan_neg_top {F C} _.
Arguments generic_de_morgan_neg_bottom {F C} _.
Arguments generic_de_morgan_imp {F C} _.
Arguments generic_de_morgan_neg_and {F C} _.
Arguments generic_de_morgan_neg_or {F C} _.
Arguments generic_lukasiewicz_neg {F C} _.
Arguments generic_lukasiewicz_top {F C} _.
Arguments generic_lukasiewicz_or {F C} _ _ _.
Arguments generic_lukasiewicz_and {F C} _ _ _.
Arguments generic_closed_top {F C P} _.
Arguments generic_closed_bottom {F C P} _.
Arguments generic_closed_and {F C P} _ _ _ _ _.
Arguments generic_closed_or {F C P} _ _ _ _ _.
Arguments generic_connective_closed_and_or {F C P} _.
Arguments generic_closed_neg {F C P} _ _ _.
Arguments generic_closed_imp {F C P} _ _ _ _ _.

(** * Natural-arity conjunction and disjunction *)

(** Foundation [conjLt]: formulas [phi 0] through [phi (k-1)] are folded in
    descending index order, with top at arity zero. *)
Fixpoint generic_conj_lt {F : Type}
    (C : generic_connectives F) (phi : nat -> F) (k : nat) : F :=
  match k with
  | 0 => generic_top C
  | S n => generic_and C (phi n) (generic_conj_lt C phi n)
  end.

Lemma generic_conj_lt_zero :
  forall (F : Type) (C : generic_connectives F) (phi : nat -> F),
    generic_conj_lt C phi 0 = generic_top C.
Proof. reflexivity. Qed.

Lemma generic_conj_lt_succ :
  forall (F : Type) (C : generic_connectives F)
         (phi : nat -> F) (k : nat),
    generic_conj_lt C phi (S k) =
    generic_and C (phi k) (generic_conj_lt C phi k).
Proof. reflexivity. Qed.

Fixpoint generic_disj_lt {F : Type}
    (C : generic_connectives F) (phi : nat -> F) (k : nat) : F :=
  match k with
  | 0 => generic_bottom C
  | S n => generic_or C (phi n) (generic_disj_lt C phi n)
  end.

Lemma generic_disj_lt_zero :
  forall (F : Type) (C : generic_connectives F) (phi : nat -> F),
    generic_disj_lt C phi 0 = generic_bottom C.
Proof. reflexivity. Qed.

Lemma generic_disj_lt_succ :
  forall (F : Type) (C : generic_connectives F)
         (phi : nat -> F) (k : nat),
    generic_disj_lt C phi (S k) =
    generic_or C (phi k) (generic_disj_lt C phi k).
Proof. reflexivity. Qed.

(** The source specializes these results to proposition-valued
    homomorphisms.  The equalities below hold for every target connective
    algebra and therefore strictly generalize both source theorems. *)
Lemma generic_connective_hom_conj_lt :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (phi : nat -> F) (k : nat),
    generic_connective_hom_apply h (generic_conj_lt CF phi k) =
    generic_conj_lt CG
      (fun i => generic_connective_hom_apply h (phi i)) k.
Proof.
  intros F G CF CG h phi k; induction k as [|k IH]; simpl.
  - exact (generic_connective_hom_top h).
  - now rewrite (generic_connective_hom_and h), IH.
Qed.

Lemma generic_connective_hom_disj_lt :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (phi : nat -> F) (k : nat),
    generic_connective_hom_apply h (generic_disj_lt CF phi k) =
    generic_disj_lt CG
      (fun i => generic_connective_hom_apply h (phi i)) k.
Proof.
  intros F G CF CG h phi k; induction k as [|k IH]; simpl.
  - exact (generic_connective_hom_bottom h).
  - now rewrite (generic_connective_hom_or h), IH.
Qed.

(** * List folds *)

(** Ordinary source [List.conj]/[List.disj] folds.  The singleton-normalized
    [generic_list_conj2]/[generic_list_disj2] operations are shared with
    [GenericSemantics]. *)
Definition generic_list_conj {F : Type}
    (C : generic_connectives F) (gamma : list F) : F :=
  fold_right (generic_and C) (generic_top C) gamma.

Definition generic_list_disj {F : Type}
    (C : generic_connectives F) (gamma : list F) : F :=
  fold_right (generic_or C) (generic_bottom C) gamma.

Lemma generic_list_conj_nil :
  forall (F : Type) (C : generic_connectives F),
    generic_list_conj C [] = generic_top C.
Proof. reflexivity. Qed.

Lemma generic_list_conj_cons :
  forall (F : Type) (C : generic_connectives F)
         (p : F) (gamma : list F),
    generic_list_conj C (p :: gamma) =
    generic_and C p (generic_list_conj C gamma).
Proof. reflexivity. Qed.

Lemma generic_list_disj_nil :
  forall (F : Type) (C : generic_connectives F),
    generic_list_disj C [] = generic_bottom C.
Proof. reflexivity. Qed.

Lemma generic_list_disj_cons :
  forall (F : Type) (C : generic_connectives F)
         (p : F) (gamma : list F),
    generic_list_disj C (p :: gamma) =
    generic_or C p (generic_list_disj C gamma).
Proof. reflexivity. Qed.

Lemma generic_connective_hom_list_conj :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG) (gamma : list F),
    generic_connective_hom_apply h (generic_list_conj CF gamma) =
    generic_list_conj CG (map (generic_connective_hom_apply h) gamma).
Proof.
  intros F G CF CG h gamma; induction gamma as [|p gamma IH]; simpl.
  - exact (generic_connective_hom_top h).
  - now rewrite (generic_connective_hom_and h), IH.
Qed.

Lemma generic_connective_hom_list_disj :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG) (gamma : list F),
    generic_connective_hom_apply h (generic_list_disj CF gamma) =
    generic_list_disj CG (map (generic_connective_hom_apply h) gamma).
Proof.
  intros F G CF CG h gamma; induction gamma as [|p gamma IH]; simpl.
  - exact (generic_connective_hom_bottom h).
  - now rewrite (generic_connective_hom_or h), IH.
Qed.

Lemma generic_connective_hom_list_conj2 :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG) (gamma : list F),
    generic_connective_hom_apply h (generic_list_conj2 CF gamma) =
    generic_list_conj2 CG (map (generic_connective_hom_apply h) gamma).
Proof.
  intros F G CF CG h gamma; induction gamma as [|p gamma IH].
  - simpl. exact (generic_connective_hom_top h).
  - destruct gamma as [|q gamma].
    + reflexivity.
    + simpl generic_list_conj2 in IH |- *.
      now rewrite (generic_connective_hom_and h), IH.
Qed.

Lemma generic_connective_hom_list_disj2 :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG) (gamma : list F),
    generic_connective_hom_apply h (generic_list_disj2 CF gamma) =
    generic_list_disj2 CG (map (generic_connective_hom_apply h) gamma).
Proof.
  intros F G CF CG h gamma; induction gamma as [|p gamma IH].
  - simpl. exact (generic_connective_hom_bottom h).
  - destruct gamma as [|q gamma].
    + reflexivity.
    + simpl generic_list_disj2 in IH |- *.
      now rewrite (generic_connective_hom_or h), IH.
Qed.

(** Indexed list folds, corresponding to source [List.conj']/[List.disj']. *)
Definition generic_list_conj_map {I F : Type}
    (C : generic_connectives F) (f : I -> F) (xs : list I) : F :=
  generic_list_conj2 C (map f xs).

Definition generic_list_disj_map {I F : Type}
    (C : generic_connectives F) (f : I -> F) (xs : list I) : F :=
  generic_list_disj2 C (map f xs).

Lemma generic_connective_hom_list_conj_map :
  forall (I F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (f : I -> F) (xs : list I),
    generic_connective_hom_apply h (generic_list_conj_map CF f xs) =
    generic_list_conj_map CG
      (fun i => generic_connective_hom_apply h (f i)) xs.
Proof.
  intros I F G CF CG h f xs. unfold generic_list_conj_map.
  rewrite generic_connective_hom_list_conj2, map_map. reflexivity.
Qed.

Lemma generic_connective_hom_list_disj_map :
  forall (I F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (f : I -> F) (xs : list I),
    generic_connective_hom_apply h (generic_list_disj_map CF f xs) =
    generic_list_disj_map CG
      (fun i => generic_connective_hom_apply h (f i)) xs.
Proof.
  intros I F G CF CG h f xs. unfold generic_list_disj_map.
  rewrite generic_connective_hom_list_disj2, map_map. reflexivity.
Qed.

(** * Finite-vector folds *)

(** Foundation [Matrix.conj].  An arbitrary finite vector is represented by
    its lookup function on [Fin.t n], preserving the source's extensional
    interface without a separate vector container. *)
Fixpoint generic_matrix_conj {F : Type}
    (C : generic_connectives F) (n : nat) : (Fin.t n -> F) -> F :=
  match n as n0 return (Fin.t n0 -> F) -> F with
  | 0 => fun _ => generic_top C
  | S k => fun v =>
      generic_and C (v Fin.F1)
        (@generic_matrix_conj F C k (fun i => v (Fin.FS i)))
  end.

Arguments generic_matrix_conj {F} C n v.

Lemma generic_matrix_conj_zero :
  forall (F : Type) (C : generic_connectives F)
         (v : Fin.t 0 -> F),
    generic_matrix_conj C 0 v = generic_top C.
Proof. reflexivity. Qed.

Lemma generic_matrix_conj_succ :
  forall (F : Type) (C : generic_connectives F)
         (n : nat) (v : Fin.t (S n) -> F),
    generic_matrix_conj C (S n) v =
    generic_and C (v Fin.F1)
      (generic_matrix_conj C n (fun i => v (Fin.FS i))).
Proof. reflexivity. Qed.

Fixpoint generic_matrix_disj {F : Type}
    (C : generic_connectives F) (n : nat) : (Fin.t n -> F) -> F :=
  match n as n0 return (Fin.t n0 -> F) -> F with
  | 0 => fun _ => generic_bottom C
  | S k => fun v =>
      generic_or C (v Fin.F1)
        (@generic_matrix_disj F C k (fun i => v (Fin.FS i)))
  end.

Arguments generic_matrix_disj {F} C n v.

Lemma generic_matrix_disj_zero :
  forall (F : Type) (C : generic_connectives F)
         (v : Fin.t 0 -> F),
    generic_matrix_disj C 0 v = generic_bottom C.
Proof. reflexivity. Qed.

Lemma generic_matrix_disj_succ :
  forall (F : Type) (C : generic_connectives F)
         (n : nat) (v : Fin.t (S n) -> F),
    generic_matrix_disj C (S n) v =
    generic_or C (v Fin.F1)
      (generic_matrix_disj C n (fun i => v (Fin.FS i))).
Proof. reflexivity. Qed.

Lemma generic_connective_hom_matrix_conj :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (n : nat) (v : Fin.t n -> F),
    generic_connective_hom_apply h (generic_matrix_conj CF n v) =
    generic_matrix_conj CG n
      (fun i => generic_connective_hom_apply h (v i)).
Proof.
  intros F G CF CG h n; induction n as [|n IH]; intro v; simpl.
  - exact (generic_connective_hom_top h).
  - rewrite (generic_connective_hom_and h), IH. reflexivity.
Qed.

Lemma generic_connective_hom_matrix_disj :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (n : nat) (v : Fin.t n -> F),
    generic_connective_hom_apply h (generic_matrix_disj CF n v) =
    generic_matrix_disj CG n
      (fun i => generic_connective_hom_apply h (v i)).
Proof.
  intros F G CF CG h n; induction n as [|n IH]; intro v; simpl.
  - exact (generic_connective_hom_bottom h).
  - rewrite (generic_connective_hom_or h), IH. reflexivity.
Qed.

(** * List negation and De Morgan laws *)

Definition generic_list_neg {F : Type}
    (C : generic_connectives F) (gamma : list F) : list F :=
  map (generic_neg C) gamma.

Lemma generic_list_neg_nil :
  forall (F : Type) (C : generic_connectives F),
    generic_list_neg C [] = [].
Proof. reflexivity. Qed.

Lemma generic_list_neg_cons :
  forall (F : Type) (C : generic_connectives F)
         (p : F) (gamma : list F),
    generic_list_neg C (p :: gamma) =
    generic_neg C p :: generic_list_neg C gamma.
Proof. reflexivity. Qed.

Lemma generic_list_neg_app :
  forall (F : Type) (C : generic_connectives F)
         (gamma delta : list F),
    generic_list_neg C (gamma ++ delta) =
    generic_list_neg C gamma ++ generic_list_neg C delta.
Proof.
  intros F C gamma delta. unfold generic_list_neg. apply map_app.
Qed.

Lemma generic_list_member_neg_iff :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    forall (p : F) (gamma : list F),
      In p (generic_list_neg C gamma) <->
      In (generic_neg C p) gamma.
Proof.
  intros F C Hinv p gamma; split.
  - intro Hp. unfold generic_list_neg in Hp.
    apply in_map_iff in Hp. destruct Hp as [q [Hqp Hq]].
    assert (Hneg : generic_neg C p = q).
    { pose proof (f_equal (generic_neg C) Hqp) as H.
      rewrite (Hinv q) in H. exact (eq_sym H). }
    now rewrite Hneg.
  - intro Hp. unfold generic_list_neg. apply in_map_iff.
    exists (generic_neg C p). split.
    + exact (Hinv p).
    + exact Hp.
Qed.

Lemma generic_list_neg_involutive :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    forall gamma : list F,
      generic_list_neg C (generic_list_neg C gamma) = gamma.
Proof.
  intros F C Hinv gamma; induction gamma as [|p gamma IH]; simpl.
  - reflexivity.
  - now rewrite (Hinv p), IH.
Qed.

Lemma generic_neg_list_disj :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_bottom_law C ->
    generic_neg_or_law C ->
    forall gamma : list F,
      generic_neg C (generic_list_disj C gamma) =
      generic_list_conj C (generic_list_neg C gamma).
Proof.
  intros F C Hneg_bottom Hneg_or gamma.
  induction gamma as [|p gamma IH]; simpl.
  - exact Hneg_bottom.
  - now rewrite Hneg_or, IH.
Qed.

Lemma generic_neg_list_conj :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_top_law C ->
    generic_neg_and_law C ->
    forall gamma : list F,
      generic_neg C (generic_list_conj C gamma) =
      generic_list_disj C (generic_list_neg C gamma).
Proof.
  intros F C Hneg_top Hneg_and gamma.
  induction gamma as [|p gamma IH]; simpl.
  - exact Hneg_top.
  - now rewrite Hneg_and, IH.
Qed.

(** Singleton-normalized list De Morgan, corresponding to source
    [List.tilde_conj2] and [List.tilde_disj2]. *)
Lemma generic_neg_list_disj2 :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_bottom_law C ->
    generic_neg_or_law C ->
    forall gamma : list F,
      generic_neg C (generic_list_disj2 C gamma) =
      generic_list_conj2 C (generic_list_neg C gamma).
Proof.
  intros F C Hneg_bottom Hneg_or gamma.
  induction gamma as [|p ps IH].
  - simpl. exact Hneg_bottom.
  - destruct ps as [|q qs].
    + reflexivity.
    + simpl in IH |- *. rewrite Hneg_or, IH. reflexivity.
Qed.

Lemma generic_neg_list_conj2 :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_top_law C ->
    generic_neg_and_law C ->
    forall gamma : list F,
      generic_neg C (generic_list_conj2 C gamma) =
      generic_list_disj2 C (generic_list_neg C gamma).
Proof.
  intros F C Hneg_top Hneg_and gamma.
  induction gamma as [|p ps IH].
  - simpl. exact Hneg_top.
  - destruct ps as [|q qs].
    + reflexivity.
    + simpl in IH |- *. rewrite Hneg_and, IH. reflexivity.
Qed.

Lemma generic_neg_mapped_list_disj2 :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    generic_neg_bottom_law C ->
    generic_neg_or_law C ->
    forall gamma : list F,
      generic_neg C
        (generic_list_disj2 C (map (generic_neg C) gamma)) =
      generic_list_conj2 C gamma.
Proof.
  intros F C Hinv Hneg_bottom Hneg_or gamma.
  change (generic_neg C
    (generic_list_disj2 C (generic_list_neg C gamma)) =
    generic_list_conj2 C gamma).
  rewrite (@generic_neg_list_disj2 F C Hneg_bottom Hneg_or
    (generic_list_neg C gamma)).
  rewrite generic_list_neg_involutive; [reflexivity | exact Hinv].
Qed.

Lemma generic_connective_hom_list_neg :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG) (gamma : list F),
    map (generic_connective_hom_apply h) (generic_list_neg CF gamma) =
    generic_list_neg CG (map (generic_connective_hom_apply h) gamma).
Proof.
  intros F G CF CG h gamma; induction gamma as [|p gamma IH]; simpl.
  - reflexivity.
  - now rewrite (generic_connective_hom_neg h), IH.
Qed.

(** * Finite-set conveniences *)

(** Foundation's [Finset] layer is represented by duplicate-tolerant lists.
    Every observable theorem below is phrased through [In], so order and
    multiplicity are immaterial.  This removes both the source's
    noncomputability and all [DecidableEq] premises. *)
Definition generic_finset_neg {F : Type}
    (C : generic_connectives F) (s : list F) : list F :=
  generic_list_neg C s.

Lemma generic_finset_neg_member_iff :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    forall (p : F) (s : list F),
      In p (generic_finset_neg C s) <-> In (generic_neg C p) s.
Proof. exact generic_list_member_neg_iff. Qed.

Lemma generic_finset_neg_involutive :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    forall s : list F,
      generic_finset_neg C (generic_finset_neg C s) = s.
Proof. exact generic_list_neg_involutive. Qed.

Lemma generic_finset_neg_empty :
  forall (F : Type) (C : generic_connectives F),
    generic_finset_neg C [] = [].
Proof. reflexivity. Qed.

Lemma generic_finset_neg_insert :
  forall (F : Type) (C : generic_connectives F)
         (p : F) (s : list F),
    generic_finset_neg C (p :: s) =
    generic_neg C p :: generic_finset_neg C s.
Proof. reflexivity. Qed.

(** Append represents finite union. *)
Lemma generic_finset_neg_union :
  forall (F : Type) (C : generic_connectives F)
         (s t : list F),
    generic_finset_neg C (s ++ t) =
    generic_finset_neg C s ++ generic_finset_neg C t.
Proof. exact generic_list_neg_app. Qed.

(** Singleton-normalized folds match Foundation [Finset.conj]/[disj]. *)
Definition generic_finset_conj {F : Type}
    (C : generic_connectives F) (s : list F) : F :=
  generic_list_conj2 C s.

Definition generic_finset_conj_map {I F : Type}
    (C : generic_connectives F) (s : list I) (f : I -> F) : F :=
  generic_list_conj_map C f s.

(** A supplied finite enumeration replaces the source's implicit [Fintype]
    universe and works even when the index type has no decidable equality. *)
Definition generic_finset_uconj {I F : Type}
    (C : generic_connectives F) (universe : list I) (f : I -> F) : F :=
  generic_finset_conj_map C universe f.

Definition generic_finset_disj {F : Type}
    (C : generic_connectives F) (s : list F) : F :=
  generic_list_disj2 C s.

Definition generic_finset_disj_map {I F : Type}
    (C : generic_connectives F) (s : list I) (f : I -> F) : F :=
  generic_list_disj_map C f s.

Definition generic_finset_udisj {I F : Type}
    (C : generic_connectives F) (universe : list I) (f : I -> F) : F :=
  generic_finset_disj_map C universe f.

Lemma generic_finset_conj_empty :
  forall (F : Type) (C : generic_connectives F),
    generic_finset_conj C [] = generic_top C.
Proof. reflexivity. Qed.

Lemma generic_finset_conj_singleton :
  forall (F : Type) (C : generic_connectives F) (p : F),
    generic_finset_conj C [p] = p.
Proof. reflexivity. Qed.

Lemma generic_finset_conj_map_empty :
  forall (I F : Type) (C : generic_connectives F) (f : I -> F),
    generic_finset_conj_map C [] f = generic_top C.
Proof. reflexivity. Qed.

Lemma generic_finset_conj_map_singleton :
  forall (I F : Type) (C : generic_connectives F)
         (f : I -> F) (i : I),
    generic_finset_conj_map C [i] f = f i.
Proof. reflexivity. Qed.

Lemma generic_finset_uconj_empty :
  forall (I F : Type) (C : generic_connectives F) (f : I -> F),
    generic_finset_uconj C [] f = generic_top C.
Proof. reflexivity. Qed.

Lemma generic_finset_uconj_singleton :
  forall (I F : Type) (C : generic_connectives F)
         (f : I -> F) (i : I),
    generic_finset_uconj C [i] f = f i.
Proof. reflexivity. Qed.

Lemma generic_finset_disj_empty :
  forall (F : Type) (C : generic_connectives F),
    generic_finset_disj C [] = generic_bottom C.
Proof. reflexivity. Qed.

Lemma generic_finset_disj_singleton :
  forall (F : Type) (C : generic_connectives F) (p : F),
    generic_finset_disj C [p] = p.
Proof. reflexivity. Qed.

Lemma generic_finset_disj_map_empty :
  forall (I F : Type) (C : generic_connectives F) (f : I -> F),
    generic_finset_disj_map C [] f = generic_bottom C.
Proof. reflexivity. Qed.

Lemma generic_finset_disj_map_singleton :
  forall (I F : Type) (C : generic_connectives F)
         (f : I -> F) (i : I),
    generic_finset_disj_map C [i] f = f i.
Proof. reflexivity. Qed.

Lemma generic_finset_udisj_empty :
  forall (I F : Type) (C : generic_connectives F) (f : I -> F),
    generic_finset_udisj C [] f = generic_bottom C.
Proof. reflexivity. Qed.

Lemma generic_finset_udisj_singleton :
  forall (I F : Type) (C : generic_connectives F)
         (f : I -> F) (i : I),
    generic_finset_udisj C [i] f = f i.
Proof. reflexivity. Qed.

(** Homomorphism preservation is generalized from proposition-valued maps
    to an arbitrary target connective algebra. *)
Lemma generic_connective_hom_finset_conj :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG) (s : list F),
    generic_connective_hom_apply h (generic_finset_conj CF s) =
    generic_finset_conj CG (map (generic_connective_hom_apply h) s).
Proof. exact generic_connective_hom_list_conj2. Qed.

Lemma generic_connective_hom_finset_disj :
  forall (F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG) (s : list F),
    generic_connective_hom_apply h (generic_finset_disj CF s) =
    generic_finset_disj CG (map (generic_connective_hom_apply h) s).
Proof. exact generic_connective_hom_list_disj2. Qed.

Lemma generic_connective_hom_finset_conj_map :
  forall (I F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (s : list I) (f : I -> F),
    generic_connective_hom_apply h (generic_finset_conj_map CF s f) =
    generic_finset_conj_map CG s
      (fun i => generic_connective_hom_apply h (f i)).
Proof.
  intros I F G CF CG h s f. unfold generic_finset_conj_map.
  apply generic_connective_hom_list_conj_map.
Qed.

Lemma generic_connective_hom_finset_disj_map :
  forall (I F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (s : list I) (f : I -> F),
    generic_connective_hom_apply h (generic_finset_disj_map CF s f) =
    generic_finset_disj_map CG s
      (fun i => generic_connective_hom_apply h (f i)).
Proof.
  intros I F G CF CG h s f. unfold generic_finset_disj_map.
  apply generic_connective_hom_list_disj_map.
Qed.

Lemma generic_connective_hom_finset_uconj :
  forall (I F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (universe : list I) (f : I -> F),
    generic_connective_hom_apply h
      (generic_finset_uconj CF universe f) =
    generic_finset_uconj CG universe
      (fun i => generic_connective_hom_apply h (f i)).
Proof. exact generic_connective_hom_finset_conj_map. Qed.

Lemma generic_connective_hom_finset_udisj :
  forall (I F G : Type)
         (CF : generic_connectives F) (CG : generic_connectives G)
         (h : generic_connective_hom CF CG)
         (universe : list I) (f : I -> F),
    generic_connective_hom_apply h
      (generic_finset_udisj CF universe f) =
    generic_finset_udisj CG universe
      (fun i => generic_connective_hom_apply h (f i)).
Proof. exact generic_connective_hom_finset_disj_map. Qed.

(** Predicate readback reuses the independently factored semantic clauses,
    requiring only top/and or bottom/or rather than a full homomorphism. *)
Lemma generic_finset_conj_models_iff :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (s : list F),
      generic_models S m (generic_finset_conj C s) <->
      forall p, In p s -> generic_models S m p.
Proof. exact generic_models_finset_conj. Qed.

Lemma generic_finset_conj_map_models_iff :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (s : list I) (f : I -> F),
      generic_models S m (generic_finset_conj_map C s f) <->
      forall i, In i s -> generic_models S m (f i).
Proof. exact generic_models_finset_conj_map. Qed.

Lemma generic_finset_disj_models_iff :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (s : list F),
      generic_models S m (generic_finset_disj C s) <->
      exists p, In p s /\ generic_models S m p.
Proof. exact generic_models_finset_disj. Qed.

Lemma generic_finset_disj_map_models_iff :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (s : list I) (f : I -> F),
      generic_models S m (generic_finset_disj_map C s f) <->
      exists i, In i s /\ generic_models S m (f i).
Proof. exact generic_models_finset_disj_map. Qed.

Lemma generic_finset_uconj_models_iff :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (universe : list I) (f : I -> F),
      generic_models S m (generic_finset_uconj C universe f) <->
      forall i, In i universe -> generic_models S m (f i).
Proof. exact generic_finset_conj_map_models_iff. Qed.

Lemma generic_finset_udisj_models_iff :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (universe : list I) (f : I -> F),
      generic_models S m (generic_finset_udisj C universe f) <->
      exists i, In i universe /\ generic_models S m (f i).
Proof. exact generic_finset_disj_map_models_iff. Qed.

Lemma generic_finset_conj_union_models_iff :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (s t : list F),
      generic_models S m (generic_finset_conj C (s ++ t)) <->
      generic_models S m
        (generic_and C (generic_finset_conj C s)
          (generic_finset_conj C t)).
Proof.
  intros M F C S Htop Hand m s t.
  rewrite (generic_finset_conj_models_iff Htop Hand m (s ++ t)),
    (generic_models_and Hand m
      (generic_finset_conj C s) (generic_finset_conj C t)),
    (generic_finset_conj_models_iff Htop Hand m s),
    (generic_finset_conj_models_iff Htop Hand m t).
  split.
  - intro Hall; split; intros p Hp; apply Hall; apply in_app_iff;
      [now left | now right].
  - intros [Hs Ht] p Hp. apply in_app_iff in Hp.
    destruct Hp as [Hp | Hp]; [now apply Hs | now apply Ht].
Qed.

Lemma generic_finset_disj_union_models_iff :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (s t : list F),
      generic_models S m (generic_finset_disj C (s ++ t)) <->
      generic_models S m
        (generic_or C (generic_finset_disj C s)
          (generic_finset_disj C t)).
Proof.
  intros M F C S Hbottom Hor m s t.
  rewrite (generic_finset_disj_models_iff Hbottom Hor m (s ++ t)),
    (generic_models_or Hor m
      (generic_finset_disj C s) (generic_finset_disj C t)),
    (generic_finset_disj_models_iff Hbottom Hor m s),
    (generic_finset_disj_models_iff Hbottom Hor m t).
  split.
  - intros [p [Hp Hmodel]]. apply in_app_iff in Hp.
    destruct Hp as [Hp | Hp].
    + left. now exists p.
    + right. now exists p.
  - intros [[p [Hp Hmodel]] | [p [Hp Hmodel]]]; exists p; split.
    + apply in_app_iff. now left.
    + exact Hmodel.
    + apply in_app_iff. now right.
    + exact Hmodel.
Qed.

(** If the supplied enumeration is complete, the source's quantification
    over an implicit finite universe is recovered exactly. *)
Lemma generic_finset_uconj_complete_models_iff :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (universe : list I) (f : I -> F),
      (forall i, In i universe) ->
      (generic_models S m (generic_finset_uconj C universe f) <->
       forall i, generic_models S m (f i)).
Proof.
  intros M F I C S Htop Hand m universe f Hcover.
  rewrite (generic_finset_uconj_models_iff Htop Hand m universe f).
  split.
  - intros Hall i. apply Hall, Hcover.
  - intros Hall i _. apply Hall.
Qed.

Lemma generic_finset_udisj_complete_models_iff :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (universe : list I) (f : I -> F),
      (forall i, In i universe) ->
      (generic_models S m (generic_finset_udisj C universe f) <->
       exists i, generic_models S m (f i)).
Proof.
  intros M F I C S Hbottom Hor m universe f Hcover.
  rewrite (generic_finset_udisj_models_iff Hbottom Hor m universe f).
  split.
  - intros [i [_ Hi]]. now exists i.
  - intros [i Hi]. exists i. split; [apply Hcover | exact Hi].
Qed.
