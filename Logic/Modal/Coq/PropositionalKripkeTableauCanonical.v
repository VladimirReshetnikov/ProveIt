(** Saturated-tableau canonical Kripke models.

    The repository's primary intuitionistic completeness proof uses a smaller
    one-sided prime-theory construction.  Foundation's Kreisel--Putnam
    canonicality argument, however, needs both positive and negative sides.
    This module factors the reusable two-sided canonical model and its truth
    lemma once, using the completed consistent-tableau API. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  PropositionalFormula PropositionalEntailmentAxioms
  PropositionalEntailmentMinimal PropositionalEntailmentInt
  PropositionalHilbert
  PropositionalConsistentTableau PropositionalKripke.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition psct_canonical_frame {Atom : Type} (H : ph_hilbert Atom) :
    pkripke_frame :=
  {| pkripke_world := psctableau H;
     pkripke_access := fun W U =>
       forall p, psct_positive W p -> psct_positive U p;
     pkripke_access_refl := fun W p Hp => Hp;
     pkripke_access_trans := fun W U V HWU HUV p Hp => HUV p (HWU p Hp) |}.

Definition psct_canonical_valuation {Atom : Type} (H : ph_hilbert Atom) :
    pkripke_valuation Atom (psct_canonical_frame H).
Proof.
  refine (@Build_pkripke_valuation Atom (psct_canonical_frame H)
    (fun a W => psct_positive W (PAtom a)) _).
  intros a W U HWU Ha. exact (HWU (PAtom a) Ha).
Defined.

Definition psct_canonical_model {Atom : Type} (H : ph_hilbert Atom) :
    pkripke_model Atom :=
  {| pkripke_model_frame := psct_canonical_frame H;
     pkripke_model_valuation := psct_canonical_valuation H |}.

(** If [p -> q] is on the negative side, adjoining [p] positively and [q]
    negatively remains consistent.  The finite-context calculation is the
    sole proof-theoretic ingredient needed by the implication truth case. *)
Lemma psct_imp_counterseed_consistent :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (efq : forall r, ph_hilbert_proof H (ph_axiom_efq r))
      (W : psctableau H) p q,
    psct_negative W (PImp p q) ->
    pctableau_consistent H
      ((fun r => r = p \/ psct_positive W r), fun r => r = q).
Proof.
  intros Atom H efq W p q Himp gamma delta Hgamma Hdelta [d].
  pose (split := @pct_split_insert (pformula Atom) p
    (psct_positive W) gamma Hgamma).
  set (rest := pct_insert_remainder split).
  apply (psct_consistent W rest [PImp p q]).
  - unfold rest. apply pct_insert_remainder_covered.
  - apply pct_list_covered_cons. split; [exact Himp |].
    apply pct_list_covered_nil.
  - constructor. change (ph_hilbert_proof H
      (PImp (pct_conj rest) (PImp p q))).
    pose (Hm := ph_hilbert_generic_minimal H).
    pose (dinsert := pct_and_to_cons_conj H p rest).
    pose (dsubset := generic_minimal_list_conj2_subset_raw Hm gamma
      (p :: rest) (fun r hr => pct_insert_original_included split hr)).
    pose (dunique := @generic_intuitionistic_list_disj2_unique_raw
      (ph_hilbert Atom) (pformula Atom)
      (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
      (@ph_hilbert_generic_intuitionistic Atom H efq) q delta
      (fun r hr => Hdelta r hr)).
    pose (dand := ph_hilbert_imp_trans dinsert
      (ph_hilbert_imp_trans dsubset
        (ph_hilbert_imp_trans d dunique))).
    exact (@generic_minimal_imp_swap_raw
      (ph_hilbert Atom) (pformula Atom)
      (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
      Hm p (pct_conj rest) q
      (@generic_minimal_curry_raw
        (ph_hilbert Atom) (pformula Atom)
        (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
        Hm p (pct_conj rest) q dand)).
Qed.

Theorem psct_imp_counterextension :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall r, ph_hilbert_proof H (ph_axiom_efq r))
      (W : psctableau H) p q,
    psct_negative W (PImp p q) ->
    exists U : psctableau H,
      (forall r, psct_positive W r -> psct_positive U r) /\
      psct_positive U p /\ psct_negative U q.
Proof.
  intros Atom K H efq W p q Himp.
  destruct (@psct_lindenbaum Atom K H efq
    ((fun r => r = p \/ psct_positive W r), fun r => r = q)
    (@psct_imp_counterseed_consistent Atom H efq W p q Himp))
    as [U Hsub].
  exists U. repeat split.
  - intros r Hr. apply (proj1 Hsub r). now right.
  - apply (proj1 Hsub p). now left.
  - apply (proj2 Hsub q). reflexivity.
Qed.

Theorem psct_canonical_truth :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall r, ph_hilbert_proof H (ph_axiom_efq r))
      (W : psctableau H) p,
    (pkripke_forces (psct_canonical_model H) W p <->
     psct_positive W p).
Proof.
  intros Atom K H efq W p. revert W.
  induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro W.
  - reflexivity.
  - cbn. split; [contradiction | apply psct_bottom_not_positive].
  - cbn. rewrite IHp, IHq. symmetry. apply psct_and_positive_iff.
  - cbn. rewrite IHp, IHq. symmetry. apply psct_or_positive_iff.
  - cbn. split.
    + intro Hforce.
      apply (proj1 (psct_not_negative_iff_positive W (PImp p q))).
      intro Hnegative.
      destruct (@psct_imp_counterextension Atom K H efq W p q Hnegative)
        as [U [HWU [HUp HUq]]].
      pose proof (Hforce U HWU (proj2 (IHp U) HUp)) as Hqforce.
      exact (@psct_not_both Atom H U q
        (conj (proj1 (IHq U) Hqforce) HUq)).
    + intros Himp U HWU HUp.
      apply (proj2 (IHq U)).
      apply (@psct_mdp_positive Atom H U p q (HWU (PImp p q) Himp)).
      now apply (proj1 (IHp U)).
Qed.

Theorem psct_canonical_model_valid_iff_provable :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall r, ph_hilbert_proof H (ph_axiom_efq r)) p,
    (pkripke_model_valid (psct_canonical_model H) p <->
     ph_hilbert_provable H p).
Proof.
  intros Atom K H efq p. split.
  - intro Hvalid. apply (proj2 (@psct_provable_iff Atom K H efq p)).
    intro W. apply (proj1 (@psct_canonical_truth Atom K H efq W p)).
    exact (Hvalid W).
  - intro Hproof. intro W.
    apply (proj2 (@psct_canonical_truth Atom K H efq W p)).
    exact (@psct_theorem_positive Atom H W p Hproof).
Qed.

Definition psct_canonical_for_class {Atom : Type} (H : ph_hilbert Atom)
    (C : pkripke_frame -> Prop) : Prop :=
  C (psct_canonical_frame H).

Theorem ph_hilbert_pkripke_complete_of_psct_canonical :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall r, ph_hilbert_proof H (ph_axiom_efq r)) C,
    psct_canonical_for_class H C -> pkripke_complete H C.
Proof.
  intros Atom K H efq C Hcanonical p Hvalid.
  apply (proj1 (@psct_canonical_model_valid_iff_provable Atom K H efq p)).
  intro W. exact (Hvalid (psct_canonical_frame H) Hcanonical
    (psct_canonical_valuation H) W).
Qed.
