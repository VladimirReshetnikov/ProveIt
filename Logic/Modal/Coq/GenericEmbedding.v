(**
  Faithful embeddings between heterogeneous proof systems.

  This module ports the complete five-declaration active surface of the pinned
  [Foundation/Logic/Embedding.lean].  Source and target systems may use
  unrelated formula and system types; an embedding preserves and reflects
  provability after translating formulas.  The source imports a classical
  propositional layer, but none of its declarations needs connectives,
  classical logic, choice, extensionality, or decidable equality.
*)

From FoundationModal Require Import GenericEntailment.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source declaration 1/5: [Entailment.IsFaithfulEmbedding].  Preserve the
    source orientation: target provability of the translation is equivalent
    to source provability of the original formula. *)
Definition generic_is_faithful_embedding
    {S1 S2 F1 F2 : Type}
    (E1 : generic_entailment S1 F1)
    (E2 : generic_entailment S2 F2)
    (s1 : S1) (s2 : S2) (f : F1 -> F2) : Prop :=
  forall p,
    generic_provable E2 s2 (f p) <-> generic_provable E1 s1 p.

(** Source declaration 2/5: [Entailment.FaithfullyEmbeddable].  The explicit
    Prop-valued dictionary replaces Lean's type-class search while retaining
    the formula translation as a witness. *)
Record generic_faithfully_embeddable
    {S1 S2 F1 F2 : Type}
    (E1 : generic_entailment S1 F1)
    (E2 : generic_entailment S2 F2)
    (s1 : S1) (s2 : S2) : Prop := {
  generic_faithfully_embeddable_prop :
    exists f : F1 -> F2,
      generic_is_faithful_embedding E1 E2 s1 s2 f
}.

(** Source declaration 3/5: [FaithfullyEmbeddable.fun_exists]. *)
Lemma generic_faithfully_embeddable_fun_exists :
  forall (S1 S2 F1 F2 : Type)
         (E1 : generic_entailment S1 F1)
         (E2 : generic_entailment S2 F2)
         (s1 : S1) (s2 : S2),
    generic_faithfully_embeddable E1 E2 s1 s2 ->
    exists f : F1 -> F2,
      generic_is_faithful_embedding E1 E2 s1 s2 f.
Proof.
  intros S1 S2 F1 F2 E1 E2 s1 s2 H.
  exact (generic_faithfully_embeddable_prop H).
Qed.

(** Source declaration 4/5: [FaithfullyEmbeddable.refl]. *)
Lemma generic_faithfully_embeddable_refl :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_faithfully_embeddable E E s s.
Proof.
  intros S F E s. constructor.
  exists (fun p => p). intro p; split; intro H; exact H.
Qed.

(** Source declaration 5/5: [FaithfullyEmbeddable.trans].  Formula-map
    composition is enough; no equality or extensionality reasoning enters. *)
Lemma generic_faithfully_embeddable_trans :
  forall (S1 S2 S3 F1 F2 F3 : Type)
         (E1 : generic_entailment S1 F1)
         (E2 : generic_entailment S2 F2)
         (E3 : generic_entailment S3 F3)
         (s1 : S1) (s2 : S2) (s3 : S3),
    generic_faithfully_embeddable E1 E2 s1 s2 ->
    generic_faithfully_embeddable E2 E3 s2 s3 ->
    generic_faithfully_embeddable E1 E3 s1 s3.
Proof.
  intros S1 S2 S3 F1 F2 F3 E1 E2 E3 s1 s2 s3 H12 H23.
  destruct H12 as [[f12 H12]].
  destruct H23 as [[f23 H23]].
  constructor. exists (fun p => f23 (f12 p)).
  intro p; split; intro H.
  - exact (proj1 (H12 p) (proj1 (H23 (f12 p)) H)).
  - exact (proj2 (H23 (f12 p)) (proj2 (H12 p) H)).
Qed.

Arguments generic_is_faithful_embedding
  {S1 S2 F1 F2} E1 E2 s1 s2 f.
Arguments generic_faithfully_embeddable
  {S1 S2 F1 F2} E1 E2 s1 s2.
Arguments generic_faithfully_embeddable_prop
  {S1 S2 F1 F2} E1 E2 s1 s2 _.
Arguments generic_faithfully_embeddable_fun_exists
  {S1 S2 F1 F2} E1 E2 s1 s2 _.
Arguments generic_faithfully_embeddable_refl {S F} E s.
Arguments generic_faithfully_embeddable_trans
  {S1 S2 S3 F1 F2 F3} E1 E2 E3 s1 s2 s3 _ _.
