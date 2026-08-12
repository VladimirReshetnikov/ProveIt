(** Generic two-sided sequents over finite proof-relevant contexts.

    This module ports the structural kernel of
    [Foundation/Meta/TwoSided.lean].  A sequent [Gamma ==> Delta] is a
    finite-context derivation of Foundation's ordinary, bottom-terminated
    disjunction of [Delta].  In particular, a singleton succedent denotes
    [p \/ bottom], not the singleton-normalized fold [generic_list_disj2].

    Positional membership makes every raw construction duplicate-safe and
    removes the source's formula-[DecidableEq] premise.  Raw proofs remain in
    [Type]; the corresponding theoremhood interface is their [inhabited]
    wrapper. *)

From Stdlib Require Import Lists.List Program.Equality.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol GenericCalculus
  PropositionalEntailmentAxioms
  PropositionalEntailmentMinimal
  PropositionalEntailmentInt
  PropositionalEntailmentClassical.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Proof-relevant list inclusions and rotations *)

Definition generic_raw_list_subset {F : Type}
    (gamma delta : list F) : Type :=
  forall p, generic_raw_list_member p gamma ->
    generic_raw_list_member p delta.

Arguments generic_raw_list_subset {F} _ _.

Definition generic_raw_list_subset_refl {F : Type} (gamma : list F) :
    generic_raw_list_subset gamma gamma :=
  fun _ hp => hp.

Arguments generic_raw_list_subset_refl {F} gamma.

Definition generic_raw_list_subset_cons_weaken {F : Type}
    (p : F) (gamma : list F) :
    generic_raw_list_subset gamma (p :: gamma) :=
  fun _ hq => GRLM_there p hq.

Arguments generic_raw_list_subset_cons_weaken {F} p gamma.

(** Move the final occurrence to the front.  The singleton branch transports
    its payload through positional evidence rather than deciding equality. *)
Definition generic_raw_list_member_append_singleton_to_cons {F : Type}
    {p q : F} {gamma : list F}
    (h : generic_raw_list_member q (gamma ++ [p])) :
    generic_raw_list_member q (p :: gamma).
Proof.
  destruct (@generic_raw_list_member_app_split F q gamma [p] h)
    as [hgamma | hp].
  - exact (GRLM_there p hgamma).
  - exact (@generic_raw_list_member_singleton_payload F
      (fun r => generic_raw_list_member r (p :: gamma))
      p q (GRLM_here gamma) hp).
Defined.

(** Move the first occurrence to the end. *)
Definition generic_raw_list_member_cons_to_append_singleton {F : Type}
    {p q : F} {gamma : list F}
    (h : generic_raw_list_member q (p :: gamma)) :
    generic_raw_list_member q (gamma ++ [p]).
Proof.
  dependent destruction h.
  - exact (generic_raw_list_member_app_right gamma (GRLM_here [])).
  - exact (generic_raw_list_member_app_left [p] h).
Defined.

Definition generic_raw_list_subset_append_singleton_to_cons {F : Type}
    (p : F) (gamma : list F) :
    generic_raw_list_subset (gamma ++ [p]) (p :: gamma) :=
  fun _ hq => generic_raw_list_member_append_singleton_to_cons hq.

Arguments generic_raw_list_subset_append_singleton_to_cons {F} p gamma.

Definition generic_raw_list_subset_cons_to_append_singleton {F : Type}
    (p : F) (gamma : list F) :
    generic_raw_list_subset (p :: gamma) (gamma ++ [p]) :=
  fun _ hq => generic_raw_list_member_cons_to_append_singleton hq.

Arguments generic_raw_list_subset_cons_to_append_singleton {F} p gamma.

(** Rotate an appended pair to two leading occurrences. *)
Definition generic_raw_list_member_append_pair_to_cons_pair {F : Type}
    {p q r : F} {gamma : list F}
    (h : generic_raw_list_member r (gamma ++ [p; q])) :
    generic_raw_list_member r (p :: q :: gamma).
Proof.
  destruct (@generic_raw_list_member_app_split F r gamma [p; q] h)
    as [hgamma | hpq].
  - exact (GRLM_there p (GRLM_there q hgamma)).
  - dependent destruction hpq.
    + exact (GRLM_here (q :: gamma)).
    + dependent destruction hpq.
      * exact (GRLM_there p (GRLM_here gamma)).
      * inversion hpq.
Defined.

Definition generic_raw_list_subset_append_pair_to_cons_pair {F : Type}
    (p q : F) (gamma : list F) :
    generic_raw_list_subset (gamma ++ [p; q]) (p :: q :: gamma) :=
  fun _ h => generic_raw_list_member_append_pair_to_cons_pair h.

Arguments generic_raw_list_subset_append_pair_to_cons_pair {F} p q gamma.

(** * Capability inheritance by a finite context *)

(** Minimal and intuitionistic inheritance already live in their respective
    entailment modules.  Classical inheritance is recorded here once for the
    connective rules that extend this structural kernel. *)
Definition generic_classical_list_derivation {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (gamma : list F) :
    generic_classical_entailment
      (generic_list_derivation_entailment E s C) C gamma.
Proof.
  constructor.
  - refine {| generic_modus_ponens_raw := _ |}.
    intros p q dpq dp. exact (GLD_mdp dpq dp).
  - intro p. exact (GLD_theorem (generic_classical_neg_equiv H p)).
  - exact (GLD_theorem (generic_classical_verum H)).
  - intros p q. exact (GLD_theorem (generic_classical_K H p q)).
  - intros p q r. exact (GLD_theorem (generic_classical_S H p q r)).
  - intros p q. exact (GLD_theorem (generic_classical_and1 H p q)).
  - intros p q. exact (GLD_theorem (generic_classical_and2 H p q)).
  - intros p q. exact (GLD_theorem (generic_classical_and3 H p q)).
  - intros p q. exact (GLD_theorem (generic_classical_or1 H p q)).
  - intros p q. exact (GLD_theorem (generic_classical_or2 H p q)).
  - intros p q r. exact (GLD_theorem (generic_classical_or3 H p q r)).
  - intro p. exact (GLD_theorem (generic_classical_dne H p)).
Defined.

(** * Two-sided derivability *)

Definition generic_two_sided_derivation {S F : Type}
    (E : generic_entailment S F) (s : S) (C : generic_connectives F)
    (gamma delta : list F) : Type :=
  generic_list_derivation E s C gamma (generic_list_disj C delta).

Definition generic_two_sided_derivable {S F : Type}
    (E : generic_entailment S F) (s : S) (C : generic_connectives F)
    (gamma delta : list F) : Prop :=
  inhabited (generic_two_sided_derivation E s C gamma delta).

(** Bottom embeds in every ordinary, bottom-terminated disjunction fold. *)
Fixpoint generic_minimal_bottom_to_list_disj_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (delta : list F) :
    generic_proof E s
      (generic_imp C (generic_bottom C) (generic_list_disj C delta)) :=
  match delta with
  | [] => generic_minimal_identity_raw H (generic_bottom C)
  | p :: tail =>
      generic_minimal_imp_trans_raw H (generic_bottom C)
        (generic_list_disj C tail) (generic_list_disj C (p :: tail))
        (generic_minimal_bottom_to_list_disj_raw H tail)
        (generic_minimal_or2 H p (generic_list_disj C tail))
  end.

(** A proof-relevant inclusion of succedents induces implication between
    their ordinary disjunction folds.  The empty-source branch is the bottom
    embedding above, so minimal entailment suffices; no EFQ is used. *)
Definition generic_list_disj_subset_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {delta1 delta2 : list F}
    (incl : generic_raw_list_subset delta1 delta2) :
    generic_proof E s
      (generic_imp C (generic_list_disj C delta1)
        (generic_list_disj C delta2)).
Proof.
  induction delta1 as [|p tail IH].
  - exact (generic_minimal_bottom_to_list_disj_raw H delta2).
  - apply (generic_minimal_or_elim_raw H p (generic_list_disj C tail)
      (generic_list_disj C delta2)).
    + exact (generic_minimal_list_disj_intro_raw H
        (incl p (GRLM_here tail))).
    + apply IH. intros q hq. exact (incl q (GRLM_there p hq)).
Defined.

Lemma generic_list_disj_subset_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s ->
    forall delta1 delta2,
      generic_raw_list_subset delta1 delta2 ->
      generic_provable E s
        (generic_imp C (generic_list_disj C delta1)
          (generic_list_disj C delta2)).
Proof.
  intros S F E C s H delta1 delta2 incl. constructor.
  exact (generic_list_disj_subset_raw H incl).
Qed.

(** Source declaration [TwoSided.weakening]. *)
Definition generic_two_sided_weakening_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma1 gamma2 delta1 delta2 : list F}
    (incl_gamma : generic_raw_list_subset gamma1 gamma2)
    (incl_delta : generic_raw_list_subset delta1 delta2)
    (d : generic_two_sided_derivation E s C gamma1 delta1) :
    generic_two_sided_derivation E s C gamma2 delta2 :=
  GLD_mdp
    (GLD_theorem (generic_list_disj_subset_raw H incl_delta))
    (generic_list_derivation_weaken_raw incl_gamma d).

Lemma generic_two_sided_weakening :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s ->
    forall gamma1 gamma2 delta1 delta2,
      generic_raw_list_subset gamma1 gamma2 ->
      generic_raw_list_subset delta1 delta2 ->
      generic_two_sided_derivable E s C gamma1 delta1 ->
      generic_two_sided_derivable E s C gamma2 delta2.
Proof.
  intros S F E C s H gamma1 gamma2 delta1 delta2
    incl_gamma incl_delta [d].
  constructor. exact (generic_two_sided_weakening_raw
    H incl_gamma incl_delta d).
Qed.

(** Source declaration [TwoSided.remove_left].  Antecedent weakening is
    structural and needs no logical capability. *)
Definition generic_two_sided_remove_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} (p : F)
    (d : generic_two_sided_derivation E s C gamma delta) :
    generic_two_sided_derivation E s C (p :: gamma) delta :=
  generic_list_derivation_weaken_raw
    (generic_raw_list_subset_cons_weaken p gamma) d.

Lemma generic_two_sided_remove_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta p,
    generic_two_sided_derivable E s C gamma delta ->
    generic_two_sided_derivable E s C (p :: gamma) delta.
Proof.
  intros S F E C s gamma delta p [d]. constructor.
  exact (generic_two_sided_remove_left_raw p d).
Qed.

(** Source declaration [TwoSided.remove_right]. *)
Definition generic_two_sided_remove_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} (p : F)
    (d : generic_two_sided_derivation E s C gamma delta) :
    generic_two_sided_derivation E s C gamma (p :: delta) :=
  generic_two_sided_weakening_raw H
    (generic_raw_list_subset_refl gamma)
    (generic_raw_list_subset_cons_weaken p delta) d.

Lemma generic_two_sided_remove_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s ->
    forall gamma delta p,
      generic_two_sided_derivable E s C gamma delta ->
      generic_two_sided_derivable E s C gamma (p :: delta).
Proof.
  intros S F E C s H gamma delta p [d]. constructor.
  exact (generic_two_sided_remove_right_raw H p d).
Qed.

(** Source declaration [TwoSided.rotate_right]. *)
Definition generic_two_sided_rotate_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C gamma (delta ++ [p])) :
    generic_two_sided_derivation E s C gamma (p :: delta) :=
  generic_two_sided_weakening_raw H
    (generic_raw_list_subset_refl gamma)
    (generic_raw_list_subset_append_singleton_to_cons p delta) d.

Lemma generic_two_sided_rotate_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s ->
    forall gamma delta p,
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C gamma (p :: delta).
Proof.
  intros S F E C s H gamma delta p [d]. constructor.
  exact (generic_two_sided_rotate_right_raw H d).
Qed.

(** Source declaration [TwoSided.rotate_left]. *)
Definition generic_two_sided_rotate_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C (gamma ++ [p]) delta) :
    generic_two_sided_derivation E s C (p :: gamma) delta :=
  generic_list_derivation_weaken_raw
    (generic_raw_list_subset_append_singleton_to_cons p gamma) d.

Lemma generic_two_sided_rotate_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta p,
    generic_two_sided_derivable E s C (gamma ++ [p]) delta ->
    generic_two_sided_derivable E s C (p :: gamma) delta.
Proof.
  intros S F E C s gamma delta p [d]. constructor.
  exact (generic_two_sided_rotate_left_raw d).
Qed.

(** Source declaration [TwoSided.rotate_right_inv]. *)
Definition generic_two_sided_rotate_right_inv_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C gamma (p :: delta)) :
    generic_two_sided_derivation E s C gamma (delta ++ [p]) :=
  generic_two_sided_weakening_raw H
    (generic_raw_list_subset_refl gamma)
    (generic_raw_list_subset_cons_to_append_singleton p delta) d.

Lemma generic_two_sided_rotate_right_inv :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s ->
    forall gamma delta p,
      generic_two_sided_derivable E s C gamma (p :: delta) ->
      generic_two_sided_derivable E s C gamma (delta ++ [p]).
Proof.
  intros S F E C s H gamma delta p [d]. constructor.
  exact (generic_two_sided_rotate_right_inv_raw H d).
Qed.

(** Source declaration [TwoSided.rotate_left_inv]. *)
Definition generic_two_sided_rotate_left_inv_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C (p :: gamma) delta) :
    generic_two_sided_derivation E s C (gamma ++ [p]) delta :=
  generic_list_derivation_weaken_raw
    (generic_raw_list_subset_cons_to_append_singleton p gamma) d.

Lemma generic_two_sided_rotate_left_inv :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta p,
    generic_two_sided_derivable E s C (p :: gamma) delta ->
    generic_two_sided_derivable E s C (gamma ++ [p]) delta.
Proof.
  intros S F E C s gamma delta p [d]. constructor.
  exact (generic_two_sided_rotate_left_inv_raw d).
Qed.

(** * Projection and hypothesis discharge *)

(** Source declaration [TwoSided.to_provable].  Ordinary singleton
    disjunction is [p \/ bottom], so projection genuinely uses EFQ. *)
Definition generic_two_sided_to_proof_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p : F)
    (d : generic_two_sided_derivation E s C [] [p]) :
    generic_proof E s p :=
  let Hm := generic_intuitionistic_minimal H in
  generic_minimal_mdp_raw Hm (generic_list_disj C [p]) p
    (generic_intuitionistic_list_disj_elim_raw H [p] p
      (fun q hq =>
        @generic_raw_list_member_singleton_payload F
          (fun r => generic_proof E s (generic_imp C r p))
          p q (generic_minimal_identity_raw Hm p) hq))
    (generic_empty_derivation_raw (generic_minimal_mdp Hm) d).

Lemma generic_two_sided_to_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall p,
      generic_two_sided_derivable E s C [] [p] ->
      generic_provable E s p.
Proof.
  intros S F E C s H p [d]. constructor.
  exact (generic_two_sided_to_proof_raw H d).
Qed.

(** Raw form of source declaration [TwoSided.add_hyp]. *)
Definition generic_two_sided_add_hyp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (dp : generic_proof E s p)
    (d : generic_two_sided_derivation E s C (p :: gamma) delta) :
    generic_two_sided_derivation E s C gamma delta :=
  GLD_mdp (generic_minimal_list_deduction_raw H d) (GLD_theorem dp).

(** The theoremhood wrapper retains Foundation's weaker-system premise and
    generalizes it to unrelated source and target system types.  Both inputs
    and the result are propositions, so no witness-selection axiom is used. *)
Lemma generic_two_sided_add_hyp :
  forall (SS S F : Type)
         (ES : generic_entailment SS F) (E : generic_entailment S F)
         (C : generic_connectives F) (ss : SS) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p,
      generic_weaker_than ES E ss s ->
      generic_provable ES ss p ->
      generic_two_sided_derivable E s C (p :: gamma) delta ->
      generic_two_sided_derivable E s C gamma delta.
Proof.
  intros SS S F ES E C ss s H gamma delta p Hweak Hp [d].
  destruct (generic_weaker_subset Hweak p Hp) as [dp].
  constructor. exact (generic_two_sided_add_hyp_raw H dp d).
Qed.

(** * Closed sequents and structural constants *)

(** Source declaration [TwoSided.right_closed]. *)
Definition generic_two_sided_right_closed_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (hp : generic_raw_list_member p gamma) :
    generic_two_sided_derivation E s C gamma (p :: delta) :=
  GLD_mdp
    (GLD_theorem
      (generic_minimal_list_disj_intro_raw H (GRLM_here delta)))
    (GLD_assumption hp).

Lemma generic_two_sided_right_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p,
      generic_raw_list_member p gamma ->
      generic_two_sided_derivable E s C gamma (p :: delta).
Proof.
  intros S F E C s H gamma delta p hp. constructor.
  exact (generic_two_sided_right_closed_raw H hp).
Qed.

(** Source declaration [TwoSided.left_closed]. *)
Definition generic_two_sided_left_closed_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (hp : generic_raw_list_member p delta) :
    generic_two_sided_derivation E s C (p :: gamma) delta :=
  GLD_mdp
    (GLD_theorem (generic_minimal_list_disj_intro_raw H hp))
    (GLD_assumption (GRLM_here gamma)).

Lemma generic_two_sided_left_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p,
      generic_raw_list_member p delta ->
      generic_two_sided_derivable E s C (p :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p hp. constructor.
  exact (generic_two_sided_left_closed_raw H hp).
Qed.

(** Source declaration [TwoSided.verum_right]. *)
Definition generic_two_sided_verum_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    (gamma delta : list F) :
    generic_two_sided_derivation E s C gamma
      (generic_top C :: delta) :=
  GLD_mdp
    (GLD_theorem
      (generic_minimal_list_disj_intro_raw H (GRLM_here delta)))
    (GLD_theorem (generic_minimal_verum H)).

Lemma generic_two_sided_verum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta,
      generic_two_sided_derivable E s C gamma
        (generic_top C :: delta).
Proof.
  intros S F E C s H gamma delta. constructor.
  exact (generic_two_sided_verum_right_raw H gamma delta).
Qed.

(** Source declaration [TwoSided.falsum_left]. *)
Definition generic_two_sided_falsum_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) :
    generic_two_sided_derivation E s C
      (generic_bottom C :: gamma) delta :=
  GLD_mdp
    (GLD_theorem
      (generic_efq_raw (generic_intuitionistic_has_efq H)
        (generic_list_disj C delta)))
    (GLD_assumption (GRLM_here gamma)).

Lemma generic_two_sided_falsum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall gamma delta,
      generic_two_sided_derivable E s C
        (generic_bottom C :: gamma) delta.
Proof.
  intros S F E C s H gamma delta. constructor.
  exact (generic_two_sided_falsum_left_raw H gamma delta).
Qed.

(** Source declaration [TwoSided.falsum_right]. *)
Definition generic_two_sided_falsum_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F}
    (d : generic_two_sided_derivation E s C gamma delta) :
    generic_two_sided_derivation E s C gamma
      (generic_bottom C :: delta) :=
  generic_two_sided_remove_right_raw H (generic_bottom C) d.

Lemma generic_two_sided_falsum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta,
      generic_two_sided_derivable E s C gamma delta ->
      generic_two_sided_derivable E s C gamma
        (generic_bottom C :: delta).
Proof.
  intros S F E C s H gamma delta [d]. constructor.
  exact (generic_two_sided_falsum_right_raw H d).
Qed.

(** Source declaration [TwoSided.verum_left]. *)
Definition generic_two_sided_verum_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F}
    (d : generic_two_sided_derivation E s C gamma delta) :
    generic_two_sided_derivation E s C
      (generic_top C :: gamma) delta :=
  generic_two_sided_remove_left_raw (generic_top C) d.

Lemma generic_two_sided_verum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta,
    generic_two_sided_derivable E s C gamma delta ->
    generic_two_sided_derivable E s C
      (generic_top C :: gamma) delta.
Proof.
  intros S F E C s gamma delta [d]. constructor.
  exact (generic_two_sided_verum_left_raw d).
Qed.

(** * Connective rules *)

(** Map two leading disjunctive branches into a common goal. *)
Definition generic_two_sided_cons2_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    (p q goal : F) (delta : list F)
    (dp : generic_proof E s (generic_imp C p goal))
    (dq : generic_proof E s (generic_imp C q goal))
    (dtail : generic_proof E s
      (generic_imp C (generic_list_disj C delta) goal)) :
    generic_proof E s
      (generic_imp C (generic_list_disj C (p :: q :: delta)) goal) :=
  generic_minimal_or_elim_raw H p
    (generic_list_disj C (q :: delta)) goal dp
    (generic_minimal_or_elim_raw H q
      (generic_list_disj C delta) goal dq dtail).

(** Source declaration [TwoSided.and_right]. *)
Definition generic_two_sided_and_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F}
    (dp : generic_two_sided_derivation E s C gamma (delta ++ [p]))
    (dq : generic_two_sided_derivation E s C gamma (delta ++ [q])) :
    generic_two_sided_derivation E s C gamma
      (generic_and C p q :: delta).
Proof.
  pose (Hgamma := generic_minimal_list_derivation H gamma).
  pose (dpr := generic_two_sided_rotate_right_raw H dp).
  pose (dqr := generic_two_sided_rotate_right_raw H dq).
  set (tail := generic_list_disj C delta).
  set (left := generic_or C p tail).
  set (right := generic_or C q tail).
  set (goal := generic_list_disj C (generic_and C p q :: delta)).
  assert (pbranch : generic_proof E s
      (generic_imp C p (generic_imp C right goal))).
  {
    assert (dright : generic_list_derivation E s C [right; p] right).
    { exact (GLD_assumption (GRLM_here [p])). }
    assert (dp0 : generic_list_derivation E s C [right; p] p).
    { exact (GLD_assumption (GRLM_there right (GRLM_here []))). }
    pose (Hrp := generic_minimal_list_derivation H [right; p]).
    assert (qbranch : generic_list_derivation E s C [right; p]
        (generic_imp C q goal)).
    {
      exact (generic_minimal_imp_trans_raw Hrp q (generic_and C p q) goal
        (generic_minimal_mdp_raw Hrp p
          (generic_imp C q (generic_and C p q))
          (GLD_theorem (generic_minimal_and3 H p q)) dp0)
        (GLD_theorem
          (generic_minimal_list_disj_intro_raw H (GRLM_here delta)))).
    }
    assert (tailbranch : generic_list_derivation E s C [right; p]
        (generic_imp C tail goal)).
    {
      exact (GLD_theorem (generic_list_disj_subset_raw H
        (generic_raw_list_subset_cons_weaken (generic_and C p q) delta))).
    }
    pose (dgoal := generic_minimal_or_cases_raw Hrp q tail goal
      qbranch tailbranch dright).
    exact (generic_empty_derivation_raw (generic_minimal_mdp H)
      (generic_minimal_list_deduction_raw H
        (generic_minimal_list_deduction_raw H dgoal))).
  }
  assert (tailbranch : generic_proof E s
      (generic_imp C tail (generic_imp C right goal))).
  {
    exact (generic_minimal_imp_trans_raw H tail goal
      (generic_imp C right goal)
      (generic_list_disj_subset_raw H
        (generic_raw_list_subset_cons_weaken (generic_and C p q) delta))
      (generic_minimal_K H goal right)).
  }
  assert (first : generic_list_derivation E s C gamma
      (generic_imp C left (generic_imp C right goal))).
  {
    exact (generic_minimal_or_elim_raw Hgamma p
      tail (generic_imp C right goal)
      (GLD_theorem pbranch) (GLD_theorem tailbranch)).
  }
  exact (GLD_mdp (GLD_mdp first dpr) dqr).
Defined.

Lemma generic_two_sided_and_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C gamma (delta ++ [q]) ->
      generic_two_sided_derivable E s C gamma
        (generic_and C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q [dp] [dq]. constructor.
  exact (generic_two_sided_and_right_raw H dp dq).
Qed.

(** Source declaration [TwoSided.or_left]. *)
Definition generic_two_sided_or_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F}
    (dp : generic_two_sided_derivation E s C (gamma ++ [p]) delta)
    (dq : generic_two_sided_derivation E s C (gamma ++ [q]) delta) :
    generic_two_sided_derivation E s C (generic_or C p q :: gamma) delta.
Proof.
  pose (dp' := generic_two_sided_rotate_left_raw dp).
  pose (dq' := generic_two_sided_rotate_left_raw dq).
  pose (dpp := generic_minimal_list_deduction_raw H dp').
  pose (dqq := generic_minimal_list_deduction_raw H dq').
  exact (generic_list_deduction_inverse_raw
    (generic_minimal_or_elim_raw (generic_minimal_list_derivation H gamma)
      p q (generic_list_disj C delta) dpp dqq)).
Defined.

Lemma generic_two_sided_or_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C (gamma ++ [p]) delta ->
      generic_two_sided_derivable E s C (gamma ++ [q]) delta ->
      generic_two_sided_derivable E s C
        (generic_or C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q [dp] [dq]. constructor.
  exact (generic_two_sided_or_left_raw H dp dq).
Qed.

(** Source declaration [TwoSided.or_right]. *)
Definition generic_two_sided_or_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F}
    (d : generic_two_sided_derivation E s C gamma
      (delta ++ [p; q])) :
    generic_two_sided_derivation E s C gamma
      (generic_or C p q :: delta).
Proof.
  pose (d' := generic_two_sided_weakening_raw H
    (generic_raw_list_subset_refl gamma)
    (generic_raw_list_subset_append_pair_to_cons_pair p q delta) d).
  exact (GLD_mdp
    (GLD_theorem (generic_minimal_or_assoc_left_raw H p q
      (generic_list_disj C delta))) d').
Defined.

Lemma generic_two_sided_or_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C gamma (delta ++ [p; q]) ->
      generic_two_sided_derivable E s C gamma
        (generic_or C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q [d]. constructor.
  exact (generic_two_sided_or_right_raw H d).
Qed.

(** Source declaration [TwoSided.and_left]. *)
Definition generic_two_sided_and_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F}
    (d : generic_two_sided_derivation E s C
      (gamma ++ [p; q]) delta) :
    generic_two_sided_derivation E s C
      (generic_and C p q :: gamma) delta.
Proof.
  pose (d' := generic_list_derivation_weaken_raw
    (generic_raw_list_subset_append_pair_to_cons_pair p q gamma) d).
  pose (dqpd := generic_minimal_list_deduction_raw H
    (generic_minimal_list_deduction_raw H d')).
  pose (Hgamma := generic_minimal_list_derivation H gamma).
  pose (dpqd := generic_minimal_imp_swap_raw Hgamma dqpd).
  exact (generic_list_deduction_inverse_raw
    (generic_minimal_uncurry_raw Hgamma p q
      (generic_list_disj C delta) dpqd)).
Defined.

Lemma generic_two_sided_and_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C (gamma ++ [p; q]) delta ->
      generic_two_sided_derivable E s C
        (generic_and C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q [d]. constructor.
  exact (generic_two_sided_and_left_raw H d).
Qed.

(** Source declaration [TwoSided.neg_right_int].  Although Foundation places
    the rule in its intuitionistic namespace, no EFQ is used: the empty
    succedent is exactly bottom, so minimal entailment suffices. *)
Definition generic_two_sided_neg_right_int_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C (gamma ++ [p]) []) :
    generic_two_sided_derivation E s C gamma
      (generic_neg C p :: delta).
Proof.
  pose (d' := generic_two_sided_rotate_left_raw d).
  pose (Hgamma := generic_minimal_list_derivation H gamma).
  pose (dpb := generic_minimal_list_deduction_raw H d').
  pose (dneg := generic_minimal_neg_of_imp_bottom_raw Hgamma p dpb).
  exact (GLD_mdp
    (GLD_theorem (generic_minimal_list_disj_intro_raw H
      (GRLM_here delta))) dneg).
Defined.

Lemma generic_two_sided_neg_right_int :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p,
      generic_two_sided_derivable E s C (gamma ++ [p]) [] ->
      generic_two_sided_derivable E s C gamma
        (generic_neg C p :: delta).
Proof.
  intros S F E C s H gamma delta p [d]. constructor.
  exact (generic_two_sided_neg_right_int_raw H d).
Qed.

(** Source declaration [TwoSided.neg_right_cl]. *)
Definition generic_two_sided_neg_right_cl_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s)
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C (gamma ++ [p]) delta) :
    generic_two_sided_derivation E s C gamma
      (generic_neg C p :: delta).
Proof.
  pose (d' := generic_two_sided_rotate_left_raw d).
  pose (Hgamma := generic_classical_list_derivation H gamma).
  pose (dpd := generic_minimal_list_deduction_raw
    (generic_minimal_of_classical H) d').
  exact (generic_classical_imp_to_neg_or_raw Hgamma p
    (generic_list_disj C delta) dpd).
Defined.

Lemma generic_two_sided_neg_right_cl :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s -> forall gamma delta p,
      generic_two_sided_derivable E s C (gamma ++ [p]) delta ->
      generic_two_sided_derivable E s C gamma
        (generic_neg C p :: delta).
Proof.
  intros S F E C s H gamma delta p [d]. constructor.
  exact (generic_two_sided_neg_right_cl_raw H d).
Qed.

(** Source declaration [TwoSided.neg_left_int], strengthened from
    intuitionistic to minimal entailment. *)
Definition generic_two_sided_neg_left_int_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C
      (gamma ++ [generic_neg C p]) (delta ++ [p])) :
    generic_two_sided_derivation E s C
      (generic_neg C p :: gamma) delta.
Proof.
  pose (d' := generic_two_sided_weakening_raw H
    (generic_raw_list_subset_append_singleton_to_cons
      (generic_neg C p) gamma)
    (generic_raw_list_subset_append_singleton_to_cons p delta) d).
  pose (context := generic_neg C p :: gamma).
  pose (Hcontext := generic_minimal_list_derivation H context).
  assert (dneg : generic_list_derivation E s C context (generic_neg C p)).
  { exact (GLD_assumption (GRLM_here gamma)). }
  assert (pbranch : generic_list_derivation E s C context
      (generic_imp C p (generic_list_disj C delta))).
  {
    exact (generic_minimal_imp_trans_raw Hcontext p (generic_bottom C)
      (generic_list_disj C delta)
      (generic_minimal_imp_bottom_of_neg_raw Hcontext p dneg)
      (GLD_theorem (generic_minimal_bottom_to_list_disj_raw H delta))).
  }
  assert (tailbranch : generic_list_derivation E s C context
      (generic_imp C (generic_list_disj C delta)
        (generic_list_disj C delta))).
  { exact (GLD_theorem
      (generic_minimal_identity_raw H (generic_list_disj C delta))). }
  exact (generic_minimal_or_cases_raw Hcontext p
    (generic_list_disj C delta) (generic_list_disj C delta)
    pbranch tailbranch d').
Defined.

Lemma generic_two_sided_neg_left_int :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p,
      generic_two_sided_derivable E s C
        (gamma ++ [generic_neg C p]) (delta ++ [p]) ->
      generic_two_sided_derivable E s C
        (generic_neg C p :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p [d]. constructor.
  exact (generic_two_sided_neg_left_int_raw H d).
Qed.

(** Source declaration [TwoSided.neg_left]. *)
Definition generic_two_sided_neg_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (d : generic_two_sided_derivation E s C gamma (delta ++ [p])) :
    generic_two_sided_derivation E s C
      (generic_neg C p :: gamma) delta :=
  generic_two_sided_neg_left_int_raw H
    (generic_list_derivation_weaken_raw
      (fun r hr => generic_raw_list_member_app_left [generic_neg C p] hr) d).

Lemma generic_two_sided_neg_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p,
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C
        (generic_neg C p :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p [d]. constructor.
  exact (generic_two_sided_neg_left_raw H d).
Qed.

(** Source declaration [TwoSided.imply_left_int], strengthened from
    intuitionistic to minimal entailment. *)
Definition generic_two_sided_imply_left_int_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F}
    (dp : generic_two_sided_derivation E s C
      (gamma ++ [generic_imp C p q]) (delta ++ [p]))
    (dq : generic_two_sided_derivation E s C
      (gamma ++ [q]) delta) :
    generic_two_sided_derivation E s C
      (generic_imp C p q :: gamma) delta.
Proof.
  set (a := generic_imp C p q).
  pose (dp' := generic_two_sided_weakening_raw H
    (generic_raw_list_subset_append_singleton_to_cons a gamma)
    (generic_raw_list_subset_append_singleton_to_cons p delta) dp).
  pose (dq' := generic_two_sided_rotate_left_raw dq).
  pose (dqd := generic_minimal_list_deduction_raw H dq').
  pose (context := a :: gamma).
  pose (Hcontext := generic_minimal_list_derivation H context).
  assert (da : generic_list_derivation E s C context a).
  { exact (GLD_assumption (GRLM_here gamma)). }
  assert (dqd' : generic_list_derivation E s C context
      (generic_imp C q (generic_list_disj C delta))).
  { exact (generic_list_derivation_weaken_raw
      (generic_raw_list_subset_cons_weaken a gamma) dqd). }
  assert (pbranch : generic_list_derivation E s C context
      (generic_imp C p (generic_list_disj C delta))).
  {
    exact (generic_minimal_under_apply_raw Hcontext p q
      (generic_list_disj C delta)
      (generic_minimal_dhyp_raw Hcontext
        (generic_imp C q (generic_list_disj C delta)) p dqd') da).
  }
  assert (tailbranch : generic_list_derivation E s C context
      (generic_imp C (generic_list_disj C delta)
        (generic_list_disj C delta))).
  { exact (GLD_theorem
      (generic_minimal_identity_raw H (generic_list_disj C delta))). }
  exact (generic_minimal_or_cases_raw Hcontext p
    (generic_list_disj C delta) (generic_list_disj C delta)
    pbranch tailbranch dp').
Defined.

Lemma generic_two_sided_imply_left_int :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C
        (gamma ++ [generic_imp C p q]) (delta ++ [p]) ->
      generic_two_sided_derivable E s C (gamma ++ [q]) delta ->
      generic_two_sided_derivable E s C
        (generic_imp C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q [dp] [dq]. constructor.
  exact (generic_two_sided_imply_left_int_raw H dp dq).
Qed.

(** Source declaration [TwoSided.imply_left]. *)
Definition generic_two_sided_imply_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F}
    (dp : generic_two_sided_derivation E s C gamma (delta ++ [p]))
    (dq : generic_two_sided_derivation E s C (gamma ++ [q]) delta) :
    generic_two_sided_derivation E s C
      (generic_imp C p q :: gamma) delta :=
  generic_two_sided_imply_left_int_raw H
    (generic_list_derivation_weaken_raw
      (fun r hr => generic_raw_list_member_app_left
        [generic_imp C p q] hr) dp) dq.

Lemma generic_two_sided_imply_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C gamma (delta ++ [p]) ->
      generic_two_sided_derivable E s C (gamma ++ [q]) delta ->
      generic_two_sided_derivable E s C
        (generic_imp C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q [dp] [dq]. constructor.
  exact (generic_two_sided_imply_left_raw H dp dq).
Qed.

(** Source declaration [TwoSided.imply_right_int].  Singleton projection
    needs EFQ because the source fold is [q \/ bottom]. *)
Definition generic_two_sided_imply_right_int_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    {gamma delta : list F} {p q : F}
    (d : generic_two_sided_derivation E s C (gamma ++ [p]) [q]) :
    generic_two_sided_derivation E s C gamma
      (generic_imp C p q :: delta).
Proof.
  pose (Hm := generic_intuitionistic_minimal H).
  pose (Hgamma := generic_minimal_list_derivation Hm gamma).
  pose (d' := generic_two_sided_rotate_left_raw d).
  assert (single : generic_proof E s
      (generic_imp C (generic_list_disj C [q]) q)).
  {
    exact (generic_intuitionistic_list_disj_elim_raw H [q] q
      (fun r hr =>
        @generic_raw_list_member_singleton_payload F
          (fun x => generic_proof E s (generic_imp C x q))
          q r (generic_minimal_identity_raw Hm q) hr)).
  }
  pose (dq := GLD_mdp (GLD_theorem single) d').
  pose (dpq := generic_minimal_list_deduction_raw Hm dq).
  exact (GLD_mdp
    (GLD_theorem (generic_minimal_list_disj_intro_raw Hm
      (GRLM_here delta))) dpq).
Defined.

Lemma generic_two_sided_imply_right_int :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C (gamma ++ [p]) [q] ->
      generic_two_sided_derivable E s C gamma
        (generic_imp C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q [d]. constructor.
  exact (generic_two_sided_imply_right_int_raw H d).
Qed.

(** Source declaration [TwoSided.imply_right_cl].  The proof factors the
    classical implication [p -> (q \/ D)] into [~p \/ (q \/ D)] and maps
    both branches into [(p -> q) \/ D]. *)
Definition generic_two_sided_imply_right_cl_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s)
    {gamma delta : list F} {p q : F}
    (d : generic_two_sided_derivation E s C
      (gamma ++ [p]) (delta ++ [q])) :
    generic_two_sided_derivation E s C gamma
      (generic_imp C p q :: delta).
Proof.
  pose (Hm := generic_minimal_of_classical H).
  pose (Hi := generic_intuitionistic_of_classical H).
  pose (Hgamma := generic_classical_list_derivation H gamma).
  pose (Hm_gamma := generic_minimal_of_classical Hgamma).
  pose (d' := generic_two_sided_weakening_raw Hm
    (generic_raw_list_subset_append_singleton_to_cons p gamma)
    (generic_raw_list_subset_append_singleton_to_cons q delta) d).
  pose (dpqd := generic_minimal_list_deduction_raw Hm d').
  pose (cases := generic_classical_imp_to_neg_or_raw Hgamma p
    (generic_list_disj C (q :: delta)) dpqd).
  set (goal := generic_list_disj C (generic_imp C p q :: delta)).
  assert (negbranch : generic_list_derivation E s C gamma
      (generic_imp C (generic_neg C p) goal)).
  {
    exact (generic_minimal_imp_trans_raw Hm_gamma (generic_neg C p)
      (generic_imp C p q) goal
      (GLD_theorem (generic_intuitionistic_neg_imp_explosion_raw Hi p q))
      (GLD_theorem (generic_minimal_list_disj_intro_raw Hm
        (GRLM_here delta)))).
  }
  assert (qbranch : generic_list_derivation E s C gamma
      (generic_imp C q goal)).
  {
    exact (generic_minimal_imp_trans_raw Hm_gamma q
      (generic_imp C p q) goal
      (GLD_theorem (generic_minimal_K Hm q p))
      (GLD_theorem (generic_minimal_list_disj_intro_raw Hm
        (GRLM_here delta)))).
  }
  assert (tailbranch : generic_list_derivation E s C gamma
      (generic_imp C (generic_list_disj C delta) goal)).
  {
    exact (GLD_theorem (generic_list_disj_subset_raw Hm
      (generic_raw_list_subset_cons_weaken (generic_imp C p q) delta))).
  }
  assert (positive : generic_list_derivation E s C gamma
      (generic_imp C (generic_list_disj C (q :: delta)) goal)).
  {
    exact (generic_minimal_or_elim_raw Hm_gamma q
      (generic_list_disj C delta) goal qbranch tailbranch).
  }
  exact (generic_minimal_or_cases_raw Hm_gamma (generic_neg C p)
    (generic_list_disj C (q :: delta)) goal negbranch positive cases).
Defined.

Lemma generic_two_sided_imply_right_cl :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C
        (gamma ++ [p]) (delta ++ [q]) ->
      generic_two_sided_derivable E s C gamma
        (generic_imp C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q [d]. constructor.
  exact (generic_two_sided_imply_right_cl_raw H d).
Qed.

(** Source declaration [TwoSided.iff_right_cl]. *)
Definition generic_two_sided_iff_right_cl_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s)
    {gamma delta : list F} {p q : F}
    (dpq : generic_two_sided_derivation E s C
      (gamma ++ [p]) (delta ++ [q]))
    (dqp : generic_two_sided_derivation E s C
      (gamma ++ [q]) (delta ++ [p])) :
    generic_two_sided_derivation E s C gamma
      (generic_formula_iff C p q :: delta) :=
  generic_two_sided_and_right_raw (generic_minimal_of_classical H)
    (generic_two_sided_rotate_right_inv_raw
      (generic_minimal_of_classical H)
      (generic_two_sided_imply_right_cl_raw H dpq))
    (generic_two_sided_rotate_right_inv_raw
      (generic_minimal_of_classical H)
      (generic_two_sided_imply_right_cl_raw H dqp)).

Lemma generic_two_sided_iff_right_cl :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_classical_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C
        (gamma ++ [p]) (delta ++ [q]) ->
      generic_two_sided_derivable E s C
        (gamma ++ [q]) (delta ++ [p]) ->
      generic_two_sided_derivable E s C gamma
        (generic_formula_iff C p q :: delta).
Proof.
  intros S F E C s H gamma delta p q [dpq] [dqp]. constructor.
  exact (generic_two_sided_iff_right_cl_raw H dpq dqp).
Qed.

(** Source declaration [TwoSided.iff_left].  This direct proof is shorter
    than replaying the source's nested implication-left derivations. *)
Definition generic_two_sided_iff_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F}
    (dr : generic_two_sided_derivation E s C gamma
      (delta ++ [p; q]))
    (dl : generic_two_sided_derivation E s C
      (gamma ++ [p; q]) delta) :
    generic_two_sided_derivation E s C
      (generic_formula_iff C p q :: gamma) delta.
Proof.
  set (a := generic_formula_iff C p q).
  pose (context := a :: gamma).
  pose (Hcontext := generic_minimal_list_derivation H context).
  pose (dr' := generic_two_sided_weakening_raw H
    (generic_raw_list_subset_cons_weaken a gamma)
    (generic_raw_list_subset_append_pair_to_cons_pair p q delta) dr).
  pose (dl' := generic_list_derivation_weaken_raw
    (generic_raw_list_subset_append_pair_to_cons_pair p q gamma) dl).
  pose (dqpd := generic_minimal_list_deduction_raw H
    (generic_minimal_list_deduction_raw H dl')).
  pose (dpqd := generic_minimal_imp_swap_raw
    (generic_minimal_list_derivation H gamma) dqpd).
  assert (dl_context : generic_list_derivation E s C context
      (generic_imp C p (generic_imp C q
        (generic_list_disj C delta)))).
  {
    exact (generic_list_derivation_weaken_raw
      (generic_raw_list_subset_cons_weaken a gamma) dpqd).
  }
  assert (da : generic_list_derivation E s C context a).
  { exact (GLD_assumption (GRLM_here gamma)). }
  assert (dpq : generic_list_derivation E s C context
      (generic_imp C p q)).
  { exact (GLD_mdp
      (GLD_theorem (generic_minimal_and1 H
        (generic_imp C p q) (generic_imp C q p))) da). }
  assert (dqp : generic_list_derivation E s C context
      (generic_imp C q p)).
  { exact (GLD_mdp
      (GLD_theorem (generic_minimal_and2 H
        (generic_imp C p q) (generic_imp C q p))) da). }
  assert (pbranch : generic_list_derivation E s C context
      (generic_imp C p (generic_list_disj C delta))).
  {
    assert (dp0 : generic_list_derivation E s C (p :: context) p).
    { exact (GLD_assumption (GRLM_here context)). }
    pose (dpq' := generic_list_derivation_weaken_raw
      (generic_raw_list_subset_cons_weaken p context) dpq).
    pose (dq0 := GLD_mdp dpq' dp0).
    pose (dl0 := generic_list_derivation_weaken_raw
      (generic_raw_list_subset_cons_weaken p context) dl_context).
    exact (generic_minimal_list_deduction_raw H
      (GLD_mdp (GLD_mdp dl0 dp0) dq0)).
  }
  assert (qbranch : generic_list_derivation E s C context
      (generic_imp C q (generic_list_disj C delta))).
  {
    assert (dq0 : generic_list_derivation E s C (q :: context) q).
    { exact (GLD_assumption (GRLM_here context)). }
    pose (dqp' := generic_list_derivation_weaken_raw
      (generic_raw_list_subset_cons_weaken q context) dqp).
    pose (dp0 := GLD_mdp dqp' dq0).
    pose (dl0 := generic_list_derivation_weaken_raw
      (generic_raw_list_subset_cons_weaken q context) dl_context).
    exact (generic_minimal_list_deduction_raw H
      (GLD_mdp (GLD_mdp dl0 dp0) dq0)).
  }
  assert (tailbranch : generic_list_derivation E s C context
      (generic_imp C (generic_list_disj C delta)
        (generic_list_disj C delta))).
  { exact (GLD_theorem
      (generic_minimal_identity_raw H (generic_list_disj C delta))). }
  exact (generic_minimal_or_cases_raw Hcontext p
    (generic_list_disj C (q :: delta)) (generic_list_disj C delta)
    pbranch
    (generic_minimal_or_elim_raw Hcontext q
      (generic_list_disj C delta) (generic_list_disj C delta)
      qbranch tailbranch)
    dr').
Defined.

Lemma generic_two_sided_iff_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q,
      generic_two_sided_derivable E s C gamma (delta ++ [p; q]) ->
      generic_two_sided_derivable E s C (gamma ++ [p; q]) delta ->
      generic_two_sided_derivable E s C
        (generic_formula_iff C p q :: gamma) delta.
Proof.
  intros S F E C s H gamma delta p q [dr] [dl]. constructor.
  exact (generic_two_sided_iff_left_raw H dr dl).
Qed.
