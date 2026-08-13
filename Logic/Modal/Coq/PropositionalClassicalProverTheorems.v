(** The theorem interface used by Foundation's classical proof-search tactic.

    This module ports exactly the mathematical declarations in
    [Foundation/Meta/ClProver.lean]'s [ClProver.Theorems] namespace.  The
    quotation, elaboration, and tactic implementation that follows that
    namespace is Lean-specific and intentionally has no counterpart here.

    Every wrapper keeps the source's explicit formula and context arguments,
    but delegates to the generic two-sided API.  Source-style propositional
    list membership is converted constructively to inhabited positional
    membership, eliminating the tactic implementation's [DecidableEq]
    requirement without choice. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericSemantics GenericAdjunctiveSet GenericEntailment GenericLogicSymbol
  GenericCalculus
  PropositionalEntailmentAxioms
  PropositionalEntailmentMinimal PropositionalEntailmentInt
  PropositionalEntailmentClassical PropositionalTwoSided.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** A propositional membership proof supplies an inhabited positional
    witness.  The result lives in [Prop], so equality elimination remains
    constructive and never selects a raw proof from arbitrary inhabitation. *)
Lemma generic_classical_prover_raw_member_inhabited :
  forall (F : Type) (p : F) (gamma : list F),
    generic_list_member p gamma ->
    inhabited (generic_raw_list_member p gamma).
Proof.
  intros F p gamma; induction gamma as [|q gamma IH]; simpl.
  - contradiction.
  - intros [e | hp].
    + subst q. constructor. exact (GRLM_here gamma).
    + destruct (IH hp) as [h]. constructor. exact (GRLM_there q h).
Qed.

(** Source declaration [ClProver.Theorems.to_provable]. *)
Lemma generic_classical_prover_to_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s -> forall p,
      generic_two_sided_derivable E s C [] [p] ->
      generic_provable E s p.
Proof.
  intros S F E C s H p d.
  exact (generic_two_sided_to_provable
    (generic_intuitionistic_of_classical H) d).
Qed.

(** Source declaration [ClProver.Theorems.rotate_right]. *)
Lemma generic_classical_prover_rotate_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p : F),
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C gamma (p :: delta).
Proof.
  intros S F E C s H gamma delta p d.
  exact (generic_two_sided_rotate_right
    (generic_minimal_of_classical H) d).
Qed.

(** Source declaration [ClProver.Theorems.rotate_left]. *)
Lemma generic_classical_prover_rotate_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p : F),
      generic_two_sided_derivable E s C (gamma ++ [p]) delta ->
      generic_two_sided_derivable E s C (p :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p d.
  exact (generic_two_sided_rotate_left d).
Qed.

(** Source declaration [ClProver.Theorems.add_hyp]. *)
Lemma generic_classical_prover_add_hyp :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s -> forall (t : S),
      generic_weaker_than E E t s ->
      forall (gamma delta : list F) (p : F),
        generic_provable E t p ->
        generic_two_sided_derivable E s C (p :: gamma) delta ->
        generic_two_sided_derivable E s C gamma delta.
Proof.
  intros S F E C s H t Hweak gamma delta p Hp d.
  exact (generic_two_sided_add_hyp
    (generic_minimal_of_classical H) Hweak Hp d).
Qed.

(** Source declaration [ClProver.Theorems.right_closed]. *)
Lemma generic_classical_prover_right_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p : F),
      generic_list_member p gamma ->
      generic_two_sided_derivable E s C gamma (p :: delta).
Proof.
  intros S F E C s H gamma delta p hp.
  destruct (generic_classical_prover_raw_member_inhabited hp) as [hraw].
  exact (generic_two_sided_right_closed
    (generic_minimal_of_classical H) delta hraw).
Qed.

(** Source declaration [ClProver.Theorems.left_closed]. *)
Lemma generic_classical_prover_left_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p : F),
      generic_list_member p delta ->
      generic_two_sided_derivable E s C (p :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p hp.
  destruct (generic_classical_prover_raw_member_inhabited hp) as [hraw].
  exact (generic_two_sided_left_closed
    (generic_minimal_of_classical H) gamma hraw).
Qed.

(** Source declaration [ClProver.Theorems.verum_right]. *)
Lemma generic_classical_prover_verum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall gamma delta,
      generic_two_sided_derivable E s C gamma
        (generic_top C :: delta).
Proof.
  intros S F E C s H gamma delta.
  exact (generic_two_sided_verum_right
    (generic_minimal_of_classical H) gamma delta).
Qed.

(** Source declaration [ClProver.Theorems.falsum_left]. *)
Lemma generic_classical_prover_falsum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall gamma delta,
      generic_two_sided_derivable E s C
        (generic_bottom C :: gamma) delta.
Proof.
  intros S F E C s H gamma delta.
  exact (generic_two_sided_falsum_left
    (generic_intuitionistic_of_classical H) gamma delta).
Qed.

(** Source declaration [ClProver.Theorems.falsum_right]. *)
Lemma generic_classical_prover_falsum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall gamma delta,
      generic_two_sided_derivable E s C gamma delta ->
      generic_two_sided_derivable E s C gamma
        (generic_bottom C :: delta).
Proof.
  intros S F E C s H gamma delta d.
  exact (generic_two_sided_falsum_right
    (generic_minimal_of_classical H) d).
Qed.

(** Source declaration [ClProver.Theorems.verum_left]. *)
Lemma generic_classical_prover_verum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall gamma delta,
      generic_two_sided_derivable E s C gamma delta ->
      generic_two_sided_derivable E s C
        (generic_top C :: gamma) delta.
Proof.
  intros S F E C s H gamma delta d.
  exact (generic_two_sided_verum_left d).
Qed.

(** Source declaration [ClProver.Theorems.and_right]. *)
Lemma generic_classical_prover_and_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C gamma (delta ++ [q]) ->
      generic_two_sided_derivable E s C gamma
        (generic_and C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q dp dq.
  exact (generic_two_sided_and_right
    (generic_minimal_of_classical H) dp dq).
Qed.

(** Source declaration [ClProver.Theorems.or_left]. *)
Lemma generic_classical_prover_or_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C (gamma ++ [p]) delta ->
      generic_two_sided_derivable E s C (gamma ++ [q]) delta ->
      generic_two_sided_derivable E s C
        (generic_or C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q dp dq.
  exact (generic_two_sided_or_left
    (generic_minimal_of_classical H) dp dq).
Qed.

(** Source declaration [ClProver.Theorems.or_right]. *)
Lemma generic_classical_prover_or_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C gamma (delta ++ [p; q]) ->
      generic_two_sided_derivable E s C gamma
        (generic_or C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q d.
  exact (generic_two_sided_or_right
    (generic_minimal_of_classical H) d).
Qed.

(** Source declaration [ClProver.Theorems.and_left]. *)
Lemma generic_classical_prover_and_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C (gamma ++ [p; q]) delta ->
      generic_two_sided_derivable E s C
        (generic_and C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q d.
  exact (generic_two_sided_and_left
    (generic_minimal_of_classical H) d).
Qed.

(** Source declaration [ClProver.Theorems.neg_right]. *)
Lemma generic_classical_prover_neg_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p : F),
      generic_two_sided_derivable E s C (gamma ++ [p]) delta ->
      generic_two_sided_derivable E s C gamma
        (generic_neg C p :: delta).
Proof.
  intros S F E C s H gamma delta p d.
  exact (generic_two_sided_neg_right_cl H d).
Qed.

(** Source declaration [ClProver.Theorems.neg_left]. *)
Lemma generic_classical_prover_neg_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p : F),
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C
        (generic_neg C p :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p d.
  exact (generic_two_sided_neg_left
    (generic_minimal_of_classical H) d).
Qed.

(** Source declaration [ClProver.Theorems.imply_right]. *)
Lemma generic_classical_prover_imply_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C
        (gamma ++ [p]) (delta ++ [q]) ->
      generic_two_sided_derivable E s C gamma
        (generic_imp C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q d.
  exact (generic_two_sided_imply_right_cl H d).
Qed.

(** Source declaration [ClProver.Theorems.imply_left]. *)
Lemma generic_classical_prover_imply_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C (gamma ++ [q]) delta ->
      generic_two_sided_derivable E s C
        (generic_imp C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q dp dq.
  exact (generic_two_sided_imply_left
    (generic_minimal_of_classical H) dp dq).
Qed.

(** Source declaration [ClProver.Theorems.iff_right]. *)
Lemma generic_classical_prover_iff_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C
        (gamma ++ [p]) (delta ++ [q]) ->
      generic_two_sided_derivable E s C
        (gamma ++ [q]) (delta ++ [p]) ->
      generic_two_sided_derivable E s C gamma
        (generic_formula_iff C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q dpq dqp.
  exact (generic_two_sided_iff_right_cl H dpq dqp).
Qed.

(** Source declaration [ClProver.Theorems.iff_left]. *)
Lemma generic_classical_prover_iff_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s ->
    forall (gamma delta : list F) (p q : F),
      generic_two_sided_derivable E s C gamma (delta ++ [p; q]) ->
      generic_two_sided_derivable E s C (gamma ++ [p; q]) delta ->
      generic_two_sided_derivable E s C
        (generic_formula_iff C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q dr dl.
  exact (generic_two_sided_iff_left
    (generic_minimal_of_classical H) dr dl).
Qed.
