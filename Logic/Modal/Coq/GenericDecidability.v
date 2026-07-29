(**
  Generic decidability of entailment theories.

  This module ports all four active declarations from the pinned Foundation
  module [Logic/Decidability.lean].  Foundation phrases decidability through
  a coded computable predicate and therefore assumes a [Primcodable] formula
  type.  Coq can expose the executable decision procedure directly, avoiding
  a representation-specific coding layer while retaining computational data.

  Only negation is needed to state incompleteness.  Essential undecidability
  therefore accepts that single operation instead of a full connective
  package.
*)

From FoundationModal Require Import GenericEntailment.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source declaration 1/4: [Entailment.Decidable]. *)
Record generic_decidable_theory {S F : Type}
    (E : generic_entailment S F) (s : S) : Type := {
  generic_theory_decide :
    forall p : F,
      {generic_entailment_theory E s p} +
      {~ generic_entailment_theory E s p}
}.

Arguments generic_theory_decide {S F E s} _ _.

(** Source declaration 2/4: [Entailment.Undecidable]. *)
Definition generic_undecidable_theory {S F : Type}
    (E : generic_entailment S F) (s : S) : Prop :=
  generic_decidable_theory E s -> False.

(** Source declaration 3/4: [Entailment.EssentiallyUndecidable].  The source
    connective package is reduced to the negation operation used by
    [generic_incomplete]. *)
Record generic_essentially_undecidable {S F : Type}
    (E : generic_entailment S F) (neg : F -> F) (s : S) : Prop := {
  generic_essentially_undecidable_extension :
    forall t : S,
      generic_weaker_than E E s t ->
      generic_incomplete E neg t ->
      generic_undecidable_theory E t
}.

Arguments generic_essentially_undecidable_extension
  {S F E neg s} _ _ _ _.

(** Source declaration 4/4: [decidable_of_incomplete].  The Foundation name
    is historical: its premise is inconsistency, not incompleteness.  A
    universal theory is decided by the constant positive procedure. *)
Definition generic_decidable_of_incomplete {S F : Type}
    (E : generic_entailment S F) (s : S)
    (Hinc : generic_inconsistent E s) :
    generic_decidable_theory E s.
Proof.
  constructor. intro p. left. exact (Hinc p).
Defined.

(** A propositionally accurate alias for the source-named declaration. *)
Definition generic_decidable_of_inconsistent :=
  @generic_decidable_of_incomplete.
