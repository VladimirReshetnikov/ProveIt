(**
  Executably recognizable theories for bootstrapped proof codes.

  Foundation packages a Delta-one formula whose standard interpretation is
  membership in a theory.  For the standard-natural port, the essential
  computational content is an explicit Boolean classifier on Gödel codes,
  together with its exact specification.  Keeping that data visible avoids
  importing a nonstandard arithmetic model into every consumer and gives the
  proof recognizer below a directly executable axiom test.
*)

From Stdlib Require Import Arith.PeanoNat Bool Lists.List.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import Coding.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition boot_theory_code_member {L} (EL : language_encodable L)
    (T : theory L) (code : nat) : Prop :=
  exists sigma : sentence L,
    T sigma /\ boot_closed_formula_quote EL sigma = code.

Definition boot_theory_formula_code_member {L}
    (EL : language_encodable L) (T : theory L) (code : nat) : Prop :=
  exists sigma : sentence L,
    T sigma /\
    boot_typed_formula_quote EL (first_order_sentence_embed sigma) = code.

Lemma boot_theory_formula_code_member_iff : forall (L : language) EL T code,
  @boot_theory_formula_code_member L EL T code <->
  boot_theory_code_member EL T code.
Proof.
  intros L EL T code; split.
  - intros [sigma [HT Hcode]]. exists sigma. split; [assumption|].
    rewrite <- Hcode. unfold boot_typed_formula_quote,
      boot_closed_formula_quote, first_order_sentence_embed.
    symmetry. apply semiformula_code_emb.
  - intros [sigma [HT Hcode]]. exists sigma. split; [assumption|].
    rewrite <- Hcode. unfold boot_typed_formula_quote,
      boot_closed_formula_quote, first_order_sentence_embed.
    apply semiformula_code_emb.
Qed.

Record boot_theory_encoding {L} (EL : language_encodable L)
    (T : theory L) : Type := {
  boot_theory_classifier : nat -> bool;
  boot_theory_classifier_spec : forall code,
    boot_theory_classifier code = true <->
    boot_theory_code_member EL T code
}.

Arguments boot_theory_classifier {L EL T} _ _.

Lemma boot_theory_classifier_formula_spec : forall (L : language)
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) code,
  boot_theory_classifier ET code = true <->
  boot_theory_formula_code_member EL T code.
Proof.
  intros. rewrite boot_theory_classifier_spec.
  symmetry. apply boot_theory_formula_code_member_iff.
Qed.

Lemma boot_theory_classifier_quote_iff : forall (L : language)
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (sigma : sentence L),
  boot_theory_classifier ET (boot_closed_formula_quote EL sigma) = true <->
  T sigma.
Proof.
  intros L EL T ET sigma. rewrite boot_theory_classifier_spec.
  split.
  - intros [tau [HTau Hcode]].
    assert (Heq : tau = sigma).
    { apply (@semiformula_code_injective L Empty_set 0 EL
        empty_encoding). exact Hcode. }
    now subst tau.
  - intro HT. exists sigma. now split.
Qed.

(** * Closure constructions *)

Definition boot_empty_theory {L} : theory L := fun _ => False.

Definition boot_empty_theory_encoding {L} (EL : language_encodable L) :
    boot_theory_encoding EL boot_empty_theory.
Proof.
  refine {| boot_theory_classifier := fun _ => false |}.
  intro code; split; [discriminate|].
  intros [sigma [H _]]. contradiction.
Defined.

Definition boot_theory_union {L} (T U : theory L) : theory L :=
  fun sigma => T sigma \/ U sigma.

Definition boot_theory_union_encoding {L} (EL : language_encodable L)
    (T U : theory L) (ET : boot_theory_encoding EL T)
    (EU : boot_theory_encoding EL U) :
    boot_theory_encoding EL (boot_theory_union T U).
Proof.
  refine {| boot_theory_classifier := fun code =>
      orb (boot_theory_classifier ET code)
        (boot_theory_classifier EU code) |}.
  intro code. rewrite Bool.orb_true_iff,
    (boot_theory_classifier_spec ET), (boot_theory_classifier_spec EU).
  split.
  - intros [[sigma [HT Hcode]] | [sigma [HU Hcode]]].
    + exists sigma. split; [now left | assumption].
    + exists sigma. split; [now right | assumption].
  - intros [sigma [[HT | HU] Hcode]].
    + left. exists sigma. now split.
    + right. exists sigma. now split.
Defined.

Definition boot_singleton_theory {L} (sigma : sentence L) : theory L :=
  fun tau => tau = sigma.

Definition boot_singleton_theory_encoding {L}
    (EL : language_encodable L) (sigma : sentence L) :
    boot_theory_encoding EL (boot_singleton_theory sigma).
Proof.
  refine {| boot_theory_classifier := fun code =>
      Nat.eqb code (boot_closed_formula_quote EL sigma) |}.
  intro code. rewrite Nat.eqb_eq. split.
  - intro Hcode. exists sigma. split; [reflexivity|now symmetry].
  - intros [tau [-> Hcode]]. now symmetry.
Defined.

Definition boot_list_theory {L} (axioms : list (sentence L)) : theory L :=
  fun sigma => In sigma axioms.

Fixpoint boot_list_theory_classifier {L} (EL : language_encodable L)
    (axioms : list (sentence L)) (code : nat) : bool :=
  match axioms with
  | [] => false
  | sigma :: rest =>
      orb (Nat.eqb code (boot_closed_formula_quote EL sigma))
        (boot_list_theory_classifier EL rest code)
  end.

Theorem boot_list_theory_classifier_spec : forall (L : language)
    (EL : language_encodable L) (axioms : list (sentence L)) code,
  @boot_list_theory_classifier L EL axioms code = true <->
  boot_theory_code_member EL (boot_list_theory axioms) code.
Proof.
  intros L EL axioms; induction axioms as [|sigma rest IH]; intro code.
  - split; [discriminate|]. intros [tau [H _]]. inversion H.
  - simpl. rewrite Bool.orb_true_iff, Nat.eqb_eq, IH.
    split.
    + intros [Hcode | [tau [HT Hcode]]].
      * exists sigma. split; [now left|now symmetry].
      * exists tau. split; [simpl; right; exact HT|assumption].
    + intros [tau [[-> | HT] Hcode]].
      * left. now symmetry.
      * right. exists tau. now split.
Qed.

Definition boot_list_theory_encoding {L} (EL : language_encodable L)
    (axioms : list (sentence L)) :
    boot_theory_encoding EL (boot_list_theory axioms) :=
  {| boot_theory_classifier := boot_list_theory_classifier EL axioms;
     boot_theory_classifier_spec :=
       boot_list_theory_classifier_spec EL axioms |}.

(** Transport requires only pointwise theory equivalence, not equality of
    predicates or propositional extensionality. *)
Definition boot_theory_encoding_equiv {L} (EL : language_encodable L)
    (T U : theory L) (ET : boot_theory_encoding EL T)
    (H : forall sigma, T sigma <-> U sigma) : boot_theory_encoding EL U.
Proof.
  refine {| boot_theory_classifier := boot_theory_classifier ET |}.
  intro code. rewrite boot_theory_classifier_spec.
  split.
  - intros [sigma [HT Hcode]]. exists sigma. split.
    + now apply H.
    + assumption.
  - intros [sigma [HU Hcode]]. exists sigma. split.
    + now apply H.
    + assumption.
Defined.
