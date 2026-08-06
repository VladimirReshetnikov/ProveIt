(** Abstract and standard-natural consistency semantics.

    Foundation defines these formulas through a bootstrapped Π1 proof
    predicate.  Once the resulting provability endomorphism is exposed, the
    semantic theorems use only classical explosion and the truth laws for
    negation and that endomorphism.

    The second half of this module gives the concrete external semantics at
    the standard natural numbers.  Its predicates inspect the already checked
    raw proof codes, but are Coq propositions rather than internal arithmetic
    formulas.  Thus they support exact quotation, theoremhood, consistency,
    and one-sentence-extension laws without pretending to supply the source's
    internal Pi-one formulas or their definability certificates. *)

From FoundationModal Require Import
  Syntax LogicInfrastructure GenericAdjunctiveSet GenericEntailment
  PropositionalEntailmentClassical.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2.
From Foundation.FirstOrder.Bootstrapping Require Import Syntax.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import
  D1.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma pa_logic_consistent_iff_unprovable_bottom : forall (A : Type)
    (L : modal_logic_set A),
  classical_logic L ->
  (logic_consistent L <-> ~ L Bottom).
Proof.
  intros A L Hclass. split.
  - now apply logic_no_bot.
  - intros Hnot_bottom Hinc.
    exact (Hnot_bottom (Hinc Bottom)).
Qed.

(** Consistency with [p] is unprovability of its negation; this is exactly
    the source predicate after quotation/substitution is erased. *)
Definition pa_consistent_with {A L0 L}
    (B : pa_provability L0 L)
    (p : FoundationModal.Syntax.formula A) :
    FoundationModal.Syntax.formula A :=
  pa_dia B p.

Lemma pa_consistent_with_unfold : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L) p,
  pa_consistent_with B p = Neg (pa_box B (Neg p)).
Proof. reflexivity. Qed.

Lemma pa_consistent_with_truth_iff : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L)
    (truth : modal_logic_set A),
  (forall p, truth (Neg p) <-> ~ truth p) ->
  (forall p, truth (pa_box B p) <-> L p) ->
  forall p,
  truth (pa_consistent_with B p) <-> ~ L (Neg p).
Proof.
  intros A L0 L B truth Hneg Hbox p.
  unfold pa_consistent_with, pa_dia.
  rewrite Hneg, Hbox. reflexivity.
Qed.

(** Foundation's [standard_consistent], generalized from arithmetic truth in
    naturals to any truth predicate satisfying the two exact readback laws. *)
Theorem pa_con_truth_iff_logic_consistent : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (B : pa_provability L0 L) (truth : modal_logic_set A),
  (forall p, truth (Neg p) <-> ~ truth p) ->
  (forall p, truth (pa_box B p) <-> L p) ->
  truth (pa_con B) <-> logic_consistent L.
Proof.
  intros A L0 L Hclass B truth Hneg Hbox.
  unfold pa_con. rewrite Hneg, Hbox.
  symmetry. exact (pa_logic_consistent_iff_unprovable_bottom Hclass).
Qed.

(** * Standard-natural consistency of checked first-order proof codes *)

(** A theory is externally consistent when the checked raw proof predicate
    rejects the canonical quote of the closed false sentence. *)
Definition boot_consistent {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) : Prop :=
  ~ @boot_provable L EL T ET
      (boot_sentence_code EL
        (@Semiformula_falsum L Empty_set 0)).

(** Consistency with a raw code means unprovability of its executable
    syntactic negation.  The negation transformer is total, so the definition
    is meaningful for every natural code; semantic claims below are confined
    to quotes of well-typed formulas. *)
Definition boot_consistent_with {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (phi : nat) : Prop :=
  ~ @boot_provable L EL T ET
      (boot_formula_neg_code EL 0 phi).

Definition boot_sentence_consistent_with {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T)
    (sigma : sentence L) : Prop :=
  @boot_consistent_with L EL T ET
    (boot_sentence_code EL sigma).

(** Executable negation agrees exactly with negation of a typed proposition
    quote. *)
Lemma boot_consistent_with_quote : forall L EL T ET
    (p : proposition L),
  @boot_consistent_with L EL T ET
      (boot_typed_formula_quote EL p) <->
  ~ @boot_provable L EL T ET
      (boot_typed_formula_quote EL
        (boot_typed_formula_neg p)).
Proof.
  intros L EL T ET p. unfold boot_consistent_with.
  now rewrite boot_typed_formula_quote_neg.
Qed.

(** The closed-sentence specialization is proved directly from the neutral
    quotation APIs, avoiding a dependency on the later Rosser layer merely
    for its factored sentence-negation lemma. *)
Lemma boot_sentence_consistent_with_quote : forall L EL T ET
    (sigma : sentence L),
  @boot_sentence_consistent_with L EL T ET sigma <->
  ~ @boot_sentence_provable L EL T ET
      (semiformula_neg sigma).
Proof.
  intros L EL T ET sigma.
  assert (Hneg :
    boot_sentence_code EL (semiformula_neg sigma) =
    boot_formula_neg_code EL 0 (boot_sentence_code EL sigma)).
  { unfold boot_sentence_code.
    rewrite first_order_sentence_embed_neg.
    apply boot_typed_formula_quote_neg. }
  unfold boot_sentence_consistent_with, boot_consistent_with,
    boot_sentence_provable.
  now rewrite Hneg.
Qed.

(** Every accepted standard proof code reconstructs a genuine derivation and
    every genuine derivation serializes back.  Consequently consistency with
    a quoted sentence is exactly external unprovability of its negation. *)
Theorem boot_sentence_consistent_with_iff_theory : forall L T EL ET
    (sigma : sentence L),
  @boot_sentence_consistent_with L EL T ET sigma <->
  ~ first_order_theory_provable T (semiformula_neg sigma).
Proof.
  intros L T EL ET sigma.
  rewrite boot_sentence_consistent_with_quote.
  now rewrite boot_sentence_provable_iff_theory.
Qed.

(** The source's standard-model consistency theorem, strengthened to every
    executably encoded first-order theory and with no arithmetic base-theory
    hypothesis. *)
Theorem boot_consistent_iff_first_order_consistent : forall L T EL ET,
  @boot_consistent L EL T ET <->
  generic_consistent (first_order_theory_entailment L) T.
Proof.
  intros L T EL ET. unfold boot_consistent.
  change
    (~ @boot_sentence_provable L EL T ET
        (@Semiformula_falsum L Empty_set 0) <->
      generic_consistent (first_order_theory_entailment L) T).
  rewrite boot_sentence_provable_iff_theory.
  symmetry.
  apply (@generic_consistent_iff_unprovable_bottom
    (theory L) (sentence L) (first_order_theory_entailment L)
    (@Semiformula_falsum L Empty_set 0)).
  exact (@generic_deductive_explosion_of_classical
    (theory L) (sentence L) (first_order_theory_entailment L)
    (semiformula_connectives L Empty_set 0)
    (@first_order_theory_classical L)).
Qed.

(** In classical first-order logic, consistency with [sigma] is equivalently
    consistency of adjoining [sigma] as one new axiom.  The generic theorem
    is instantiated at [~ sigma]; its adjoined axiom is therefore [~~ sigma],
    which normalizes by the checked NNF involution law. *)
Theorem boot_sentence_consistent_with_iff_adjoin_consistent :
    forall L T EL ET (sigma : sentence L),
  @boot_sentence_consistent_with L EL T ET sigma <->
  generic_consistent (first_order_theory_entailment L)
    (generic_adjunctive_adjoin
      (generic_predicate_adjunctive_set (sentence L)) sigma T).
Proof.
  intros L T EL ET sigma.
  rewrite boot_sentence_consistent_with_iff_theory.
  pose (A := generic_predicate_adjunctive_set (sentence L)).
  pose proof (@generic_classical_unprovable_iff_consistent_adjoin
    (theory L) (sentence L) (first_order_theory_entailment L)
    (semiformula_connectives L Empty_set 0) A
    (first_order_theory_axiomatized L)
    (first_order_theory_deduction L) T (semiformula_neg sigma)
    (first_order_theory_classical T)
    (generic_intuitionistic_of_classical
      (first_order_theory_classical
        (generic_adjunctive_adjoin A
          (semiformula_neg (semiformula_neg sigma)) T)))) as H.
  change
    (generic_unprovable (first_order_theory_entailment L) T
        (semiformula_neg sigma) <->
      generic_consistent (first_order_theory_entailment L)
        (generic_adjunctive_adjoin A
          (semiformula_neg (semiformula_neg sigma)) T)) in H.
  rewrite semiformula_neg_involutive in H.
  unfold A in H.
  exact H.
Qed.

(** Consistency is invariant under pointwise equivalence of first-order
    axiom predicates.  Mutual proof weakening proves both directions without
    predicate extensionality. *)
Local Lemma first_order_consistent_iff_pointwise : forall L
    (T U : theory L),
  (forall sigma, T sigma <-> U sigma) ->
  (generic_consistent (first_order_theory_entailment L) T <->
   generic_consistent (first_order_theory_entailment L) U).
Proof.
  intros L T U Hequiv. split.
  - intro HT.
    eapply (@generic_consistent_of_le
      (theory L) (theory L) (sentence L)
      (first_order_theory_entailment L)
      (first_order_theory_entailment L) T U).
    + exact HT.
    + apply first_order_theory_weaker_of_subset.
      intros sigma HU. exact (proj2 (Hequiv sigma) HU).
  - intro HU.
    eapply (@generic_consistent_of_le
      (theory L) (theory L) (sentence L)
      (first_order_theory_entailment L)
      (first_order_theory_entailment L) U T).
    + exact HU.
    + apply first_order_theory_weaker_of_subset.
      intros sigma HT. exact (proj1 (Hequiv sigma) HT).
Qed.

(** The executable theory constructors realize the same one-sentence
    extension.  Their disjunction order differs from canonical adjoin, so the
    preceding pointwise transport avoids any use of predicate extensionality. *)
Theorem boot_sentence_consistent_with_iff_union_singleton_consistent :
    forall L T EL ET (sigma : sentence L),
  @boot_sentence_consistent_with L EL T ET sigma <->
  generic_consistent (first_order_theory_entailment L)
    (boot_theory_union T (boot_singleton_theory sigma)).
Proof.
  intros L T EL ET sigma.
  rewrite boot_sentence_consistent_with_iff_adjoin_consistent.
  apply first_order_consistent_iff_pointwise.
  intro tau.
  change ((tau = sigma \/ T tau) <-> (T tau \/ tau = sigma)).
  tauto.
Qed.

(** Fully executable form: consistency with [sigma] in [T] is exactly raw
    consistency of the checked union encoding for [T + sigma]. *)
Corollary
    boot_sentence_consistent_with_iff_boot_consistent_union_singleton :
    forall L T EL ET (sigma : sentence L),
  @boot_sentence_consistent_with L EL T ET sigma <->
  @boot_consistent L EL
    (boot_theory_union T (boot_singleton_theory sigma))
    (@boot_theory_union_encoding L EL T
      (boot_singleton_theory sigma) ET
      (boot_singleton_theory_encoding EL sigma)).
Proof.
  intros L T EL ET sigma.
  rewrite boot_sentence_consistent_with_iff_union_singleton_consistent.
  symmetry.
  apply boot_consistent_iff_first_order_consistent.
Qed.
