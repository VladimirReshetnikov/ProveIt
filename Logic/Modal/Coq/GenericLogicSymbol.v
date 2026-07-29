(**
  Generic logical connectives and their homomorphisms.

  This module begins the port of the pinned Foundation module
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

From FoundationModal Require Import GenericSemantics.

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
