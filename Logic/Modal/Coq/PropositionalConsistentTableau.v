(** Consistent saturated tableaux for propositional Hilbert systems.

    This ports Foundation/Propositional/ConsistentTableau.lean.  Finite sets
    are replaced throughout by positional, duplicate-tolerant lists.  This
    removes every source [DecidableEq] premise, while a typed insert-splitting
    record keeps raw proof construction free of proof extraction.

    The enumeration-independent consistency algebra is factored from the
    Lindenbaum chain.  A single two-sided cut lemma supplies the only
    nontrivial step: every consistent pair can put the next formula on one of
    its two sides. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Program.Equality.
From Stdlib Require Import Logic.ClassicalDescription.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericCalculus GenericLogicSymbol
  PropositionalEntailmentAxioms
  PropositionalEntailmentMinimal PropositionalEntailmentInt
  PropositionalEntailmentClassical
  PropositionalFormula PropositionalHilbert.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Duplicate-tolerant finite contexts *)

Definition pct_conj {Atom : Type} (gamma : list (pformula Atom)) :
    pformula Atom :=
  generic_list_conj2 (pformula_connectives Atom) gamma.

Definition pct_disj {Atom : Type} (delta : list (pformula Atom)) :
    pformula Atom :=
  generic_list_disj2 (pformula_connectives Atom) delta.

Definition pct_list_covered {F : Type}
    (T : F -> Prop) (gamma : list F) : Prop :=
  forall p, generic_raw_list_member p gamma -> T p.

Fixpoint pct_raw_member_in {F : Type} {p : F} {gamma : list F}
    (h : generic_raw_list_member p gamma) : In p gamma :=
  match h with
  | GRLM_here _ => or_introl eq_refl
  | GRLM_there _ h' => or_intror (pct_raw_member_in h')
  end.

Lemma pct_list_covered_nil :
  forall (F : Type) (T : F -> Prop), pct_list_covered T [].
Proof. intros F T p h; inversion h. Qed.

Lemma pct_list_covered_cons :
  forall (F : Type) (T : F -> Prop) p gamma,
    pct_list_covered T (p :: gamma) <->
    T p /\ pct_list_covered T gamma.
Proof.
  intros F T p gamma; split.
  - intro H. split.
    + exact (H p (GRLM_here gamma)).
    + intros q hq. exact (H q (GRLM_there p hq)).
  - intros [Hp Hgamma] q hq. dependent destruction hq.
    + exact Hp.
    + now apply Hgamma.
Qed.

Lemma pct_list_covered_app :
  forall (F : Type) (T : F -> Prop) gamma delta,
    pct_list_covered T (gamma ++ delta) <->
    pct_list_covered T gamma /\ pct_list_covered T delta.
Proof.
  intros F T gamma delta; split.
  - intro H. split.
    + intros p hp. apply H. now apply generic_raw_list_member_app_left.
    + intros p hp. apply H. now apply generic_raw_list_member_app_right.
  - intros [Hg Hd] p hp.
    destruct (generic_raw_list_member_app_split hp) as [hl | hr].
    + now apply Hg.
    + now apply Hd.
Qed.

Lemma pct_raw_member_singleton_eq :
  forall (F : Type) (p q : F),
    generic_raw_list_member q [p] -> q = p.
Proof.
  intros F p q h. pose proof (pct_raw_member_in h) as Hin.
  simpl in Hin. destruct Hin as [H | H]; [exact (eq_sym H) | contradiction].
Qed.

(** A constructive split of a finite list covered by [q = p \/ T q].
    Returning data in [Type] lets the inclusion field retain positional raw
    membership evidence without any choice principle. *)
Record pct_insert_split {F : Type} (p : F) (T : F -> Prop)
    (gamma : list F) : Type := {
  pct_insert_remainder : list F;
  pct_insert_remainder_covered :
    pct_list_covered T pct_insert_remainder;
  pct_insert_original_included : forall q,
    generic_raw_list_member q gamma ->
    generic_raw_list_member q (p :: pct_insert_remainder)
}.

Arguments pct_insert_remainder {F p T gamma} _.
Arguments pct_insert_remainder_covered {F p T gamma} _.
Arguments pct_insert_original_included {F p T gamma} _ {q} _.

Fixpoint pct_split_insert {F : Type} (p : F) (T : F -> Prop)
    (gamma : list F)
    (Hcover : pct_list_covered (fun q => q = p \/ T q) gamma) :
    pct_insert_split p T gamma.
Proof.
  destruct gamma as [|q gamma].
  - refine {| pct_insert_remainder := [] |}.
    + apply pct_list_covered_nil.
    + intros r hr. inversion hr.
  - destruct (excluded_middle_informative (q = p)) as [-> | Hneq].
    + pose (tail := @pct_split_insert F p T gamma
        (fun r hr => Hcover r (GRLM_there p hr))).
      refine {| pct_insert_remainder := pct_insert_remainder tail |}.
      * apply pct_insert_remainder_covered.
      * intros r hr. dependent destruction hr.
        -- apply GRLM_here.
        -- apply pct_insert_original_included. assumption.
    + assert (Hq : T q).
      { destruct (Hcover q (GRLM_here gamma)) as [Heq | Hq].
        - contradiction.
        - exact Hq. }
      pose (tail := @pct_split_insert F p T gamma
        (fun r hr => Hcover r (GRLM_there q hr))).
      refine {| pct_insert_remainder := q :: pct_insert_remainder tail |}.
      * apply (proj2 (pct_list_covered_cons T q _)). split.
        -- exact Hq.
        -- apply pct_insert_remainder_covered.
      * intros r hr. dependent destruction hr.
        -- exact (GRLM_there p (GRLM_here (pct_insert_remainder tail))).
        -- apply (@generic_raw_list_member_skip_insert F q r
             [p] (pct_insert_remainder tail)).
           apply pct_insert_original_included. assumption.
Defined.

(** * Hilbert consistency of a two-sided tableau *)

Definition pctableau (Atom : Type) : Type :=
  (pformula Atom -> Prop) * (pformula Atom -> Prop).

Definition pctableau_positive {Atom : Type} (t : pctableau Atom) := fst t.
Definition pctableau_negative {Atom : Type} (t : pctableau Atom) := snd t.

Definition pctableau_subset {Atom : Type}
    (t u : pctableau Atom) : Prop :=
  (forall p, pctableau_positive t p -> pctableau_positive u p) /\
  (forall p, pctableau_negative t p -> pctableau_negative u p).

Definition pctableau_insert_positive {Atom : Type}
    (p : pformula Atom) (t : pctableau Atom) : pctableau Atom :=
  (fun q => q = p \/ pctableau_positive t q, pctableau_negative t).

Definition pctableau_insert_negative {Atom : Type}
    (p : pformula Atom) (t : pctableau Atom) : pctableau Atom :=
  (pctableau_positive t, fun q => q = p \/ pctableau_negative t q).

Definition pctableau_consistent {Atom : Type}
    (H : ph_hilbert Atom) (t : pctableau Atom) : Prop :=
  forall gamma delta,
    pct_list_covered (pctableau_positive t) gamma ->
    pct_list_covered (pctableau_negative t) delta ->
    ~ ph_hilbert_provable H (PImp (pct_conj gamma) (pct_disj delta)).

Definition pctableau_inconsistent {Atom : Type}
    (H : ph_hilbert Atom) (t : pctableau Atom) : Prop :=
  ~ pctableau_consistent H t.

Definition pctableau_saturated {Atom : Type} (t : pctableau Atom) : Prop :=
  forall p, pctableau_positive t p \/ pctableau_negative t p.

Lemma pctableau_subset_refl :
  forall (Atom : Type) (t : pctableau Atom), pctableau_subset t t.
Proof. intros; split; auto. Qed.

Lemma pctableau_subset_trans :
  forall (Atom : Type) (t u v : pctableau Atom),
    pctableau_subset t u -> pctableau_subset u v -> pctableau_subset t v.
Proof. intros Atom t u v [Htu1 Htu2] [Huv1 Huv2]; split; eauto. Qed.

Lemma pctableau_insert_positive_includes :
  forall (Atom : Type) (p : pformula Atom) t,
    pctableau_subset t (pctableau_insert_positive p t).
Proof. intros; split; cbn; auto. Qed.

Lemma pctableau_insert_negative_includes :
  forall (Atom : Type) (p : pformula Atom) t,
    pctableau_subset t (pctableau_insert_negative p t).
Proof. intros; split; cbn; auto. Qed.

Lemma pctableau_not_both :
  forall (Atom : Type) (H : ph_hilbert Atom) t,
    pctableau_consistent H t -> forall p,
    ~ (pctableau_positive t p /\ pctableau_negative t p).
Proof.
  intros Atom H t Hcon p [Hp Hn].
  apply (Hcon [p] [p]).
  - apply (proj2 (pct_list_covered_cons _ _ _)); split; [exact Hp |].
    apply pct_list_covered_nil.
  - apply (proj2 (pct_list_covered_cons _ _ _)); split; [exact Hn |].
    apply pct_list_covered_nil.
  - constructor. exact (ph_hilbert_identity H p).
Qed.

Lemma pctableau_negative_of_not_positive :
  forall (Atom : Type) (t : pctableau Atom),
    pctableau_saturated t -> forall p,
    ~ pctableau_positive t p -> pctableau_negative t p.
Proof. intros Atom t Hsat p Hnot; destruct (Hsat p); tauto. Qed.

Lemma pctableau_positive_of_not_negative :
  forall (Atom : Type) (t : pctableau Atom),
    pctableau_saturated t -> forall p,
    ~ pctableau_negative t p -> pctableau_positive t p.
Proof. intros Atom t Hsat p Hnot; destruct (Hsat p); tauto. Qed.

Lemma pctableau_not_positive_iff_negative :
  forall (Atom : Type) (H : ph_hilbert Atom) t,
    pctableau_consistent H t -> pctableau_saturated t -> forall p,
    (~ pctableau_positive t p <-> pctableau_negative t p).
Proof.
  intros Atom H t Hcon Hsat p; split.
  - now apply pctableau_negative_of_not_positive.
  - intros Hn Hp. exact (pctableau_not_both Hcon (conj Hp Hn)).
Qed.

Lemma pctableau_not_negative_iff_positive :
  forall (Atom : Type) (H : ph_hilbert Atom) t,
    pctableau_consistent H t -> pctableau_saturated t -> forall p,
    (~ pctableau_negative t p <-> pctableau_positive t p).
Proof.
  intros Atom H t Hcon Hsat p; split.
  - now apply pctableau_positive_of_not_negative.
  - intros Hp Hn. exact (pctableau_not_both Hcon (conj Hp Hn)).
Qed.

Lemma pctableau_saturated_duality :
  forall (Atom : Type) (H : ph_hilbert Atom) t u,
    pctableau_consistent H t -> pctableau_consistent H u ->
    pctableau_saturated t -> pctableau_saturated u ->
    ((forall p, pctableau_positive t p <-> pctableau_positive u p) <->
     (forall p, pctableau_negative t p <-> pctableau_negative u p)).
Proof.
  intros Atom H t u Hct Hcu Hst Hsu; split; intros Heq p.
  - rewrite <- (pctableau_not_positive_iff_negative Hct Hst p).
    rewrite <- (pctableau_not_positive_iff_negative Hcu Hsu p).
    now rewrite Heq.
  - rewrite <- (pctableau_not_negative_iff_positive Hct Hst p).
    rewrite <- (pctableau_not_negative_iff_positive Hcu Hsu p).
    now rewrite Heq.
Qed.

Lemma pctableau_not_negative_of_provable_context :
  forall (Atom : Type) (H : ph_hilbert Atom) t gamma p,
    pctableau_consistent H t ->
    pct_list_covered (pctableau_positive t) gamma ->
    ph_hilbert_provable H (PImp (pct_conj gamma) p) ->
    ~ pctableau_negative t p.
Proof.
  intros Atom H t gamma p Hcon Hgamma Hprov Hp.
  apply (Hcon gamma [p] Hgamma).
  - apply (proj2 (pct_list_covered_cons _ _ _)); split; [exact Hp |].
    apply pct_list_covered_nil.
  - exact Hprov.
Qed.

(** * Insert characterizations and the shared cut step *)

Definition pct_and_to_cons_conj {Atom : Type} (H : ph_hilbert Atom)
    (p : pformula Atom) (gamma : list (pformula Atom)) :
    ph_hilbert_proof H
      (PImp (PAnd p (pct_conj gamma)) (pct_conj (p :: gamma))) :=
  generic_minimal_and_to_list_conj2_append_raw
    (ph_hilbert_generic_minimal H) [p] gamma.

Definition pct_cons_conj_to_and {Atom : Type} (H : ph_hilbert Atom)
    (p : pformula Atom) (gamma : list (pformula Atom)) :
    ph_hilbert_proof H
      (PImp (pct_conj (p :: gamma)) (PAnd p (pct_conj gamma))) :=
  generic_minimal_list_conj2_append_to_and_raw
    (ph_hilbert_generic_minimal H) [p] gamma.

Definition pct_cons_disj_to_or {Atom : Type} (H : ph_hilbert Atom)
    (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q))
    (p : pformula Atom) (delta : list (pformula Atom)) :
    ph_hilbert_proof H
      (PImp (pct_disj (p :: delta)) (POr p (pct_disj delta))) :=
  generic_intuitionistic_list_disj2_append_to_or_raw
    (@ph_hilbert_generic_intuitionistic Atom H efq) [p] delta.

Definition pct_or_to_cons_disj {Atom : Type} (H : ph_hilbert Atom)
    (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q))
    (p : pformula Atom) (delta : list (pformula Atom)) :
    ph_hilbert_proof H
      (PImp (POr p (pct_disj delta)) (pct_disj (p :: delta))) :=
  generic_intuitionistic_or_to_list_disj2_append_raw
    (@ph_hilbert_generic_intuitionistic Atom H efq) [p] delta.

Lemma pctableau_consistent_insert_positive_iff :
  forall (Atom : Type) (H : ph_hilbert Atom) t p,
    pctableau_consistent H (pctableau_insert_positive p t) <->
    forall gamma delta,
      pct_list_covered (pctableau_positive t) gamma ->
      pct_list_covered (pctableau_negative t) delta ->
      ~ ph_hilbert_provable H
          (PImp (PAnd p (pct_conj gamma)) (pct_disj delta)).
Proof.
  intros Atom H t p; split.
  - intros Hcon gamma delta Hg Hd [d].
    apply (Hcon (p :: gamma) delta).
    + apply (proj2 (pct_list_covered_cons
        (fun q => q = p \/ pctableau_positive t q) p gamma)).
      split.
      * left. reflexivity.
      * intros q hq. right. now apply Hg.
    + exact Hd.
    + constructor. exact (ph_hilbert_imp_trans
        (pct_cons_conj_to_and H p gamma) d).
  - intros Hchar gamma delta Hg Hd [d].
    pose (split := @pct_split_insert (pformula Atom) p
      (pctableau_positive t) gamma Hg).
    apply (Hchar (pct_insert_remainder split) delta).
    + apply pct_insert_remainder_covered.
    + exact Hd.
    + constructor.
      exact (ph_hilbert_imp_trans
        (ph_hilbert_imp_trans
          (pct_and_to_cons_conj H p (pct_insert_remainder split))
          (generic_minimal_list_conj2_subset_raw
            (ph_hilbert_generic_minimal H) gamma
            (p :: pct_insert_remainder split)
            (fun q hq => pct_insert_original_included split hq))) d).
Qed.

Lemma pctableau_consistent_insert_negative_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) t p,
    pctableau_consistent H (pctableau_insert_negative p t) <->
    forall gamma delta,
      pct_list_covered (pctableau_positive t) gamma ->
      pct_list_covered (pctableau_negative t) delta ->
      ~ ph_hilbert_provable H
          (PImp (pct_conj gamma) (POr p (pct_disj delta))).
Proof.
  intros Atom H efq t p; split.
  - intros Hcon gamma delta Hg Hd [d].
    apply (Hcon gamma (p :: delta)).
    + exact Hg.
    + apply (proj2 (pct_list_covered_cons
        (fun q => q = p \/ pctableau_negative t q) p delta)).
      split.
      * left. reflexivity.
      * intros q hq. right. now apply Hd.
    + constructor. apply (ph_hilbert_imp_trans d).
      apply pct_or_to_cons_disj. exact efq.
  - intros Hchar gamma delta Hg Hd [d].
    pose (split := @pct_split_insert (pformula Atom) p
      (pctableau_negative t) delta Hd).
    apply (Hchar gamma (pct_insert_remainder split)).
    + exact Hg.
    + apply pct_insert_remainder_covered.
    + constructor.
      exact (ph_hilbert_imp_trans d
        (ph_hilbert_imp_trans
          (generic_intuitionistic_list_disj2_subset_raw
            (@ph_hilbert_generic_intuitionistic Atom H efq)
            delta (p :: pct_insert_remainder split)
            (fun q hq => pct_insert_original_included split hq))
          (@pct_cons_disj_to_or Atom H efq p
            (pct_insert_remainder split)))).
Qed.

Lemma pctableau_inconsistent_insert_positive_iff :
  forall (Atom : Type) (H : ph_hilbert Atom) t p,
    pctableau_inconsistent H (pctableau_insert_positive p t) <->
    exists gamma delta,
      pct_list_covered (pctableau_positive t) gamma /\
      pct_list_covered (pctableau_negative t) delta /\
      ph_hilbert_provable H
        (PImp (PAnd p (pct_conj gamma)) (pct_disj delta)).
Proof.
  intros Atom H t p; split.
  - intro Hnot. apply NNPP. intro Hnone. apply Hnot.
    apply (proj2 (pctableau_consistent_insert_positive_iff H t p)).
    intros gamma delta Hg Hd Hprov. apply Hnone.
    exists gamma, delta. auto.
  - intros [gamma [delta [Hg [Hd Hprov]]]] Hcon.
    apply (proj1 (pctableau_consistent_insert_positive_iff H t p) Hcon
      gamma delta Hg Hd Hprov).
Qed.

Lemma pctableau_inconsistent_insert_negative_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) t p,
    pctableau_inconsistent H (pctableau_insert_negative p t) <->
    exists gamma delta,
      pct_list_covered (pctableau_positive t) gamma /\
      pct_list_covered (pctableau_negative t) delta /\
      ph_hilbert_provable H
        (PImp (pct_conj gamma) (POr p (pct_disj delta))).
Proof.
  intros Atom H efq t p; split.
  - intro Hnot. apply NNPP. intro Hnone. apply Hnot.
    apply (proj2 (@pctableau_consistent_insert_negative_iff Atom H efq t p)).
    intros gamma delta Hg Hd Hprov. apply Hnone.
    exists gamma, delta. auto.
  - intros [gamma [delta [Hg [Hd Hprov]]]] Hcon.
    apply (proj1 (@pctableau_consistent_insert_negative_iff Atom H efq t p) Hcon
      gamma delta Hg Hd Hprov).
Qed.

Theorem pctableau_consistent_either :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) t,
    pctableau_consistent H t -> forall p,
    pctableau_consistent H (pctableau_insert_positive p t) \/
    pctableau_consistent H (pctableau_insert_negative p t).
Proof.
  intros Atom H efq t Hcon p.
  apply NNPP. intro Hneither. apply not_or_and in Hneither.
  destruct Hneither as [Hpos Hneg].
  apply pctableau_inconsistent_insert_positive_iff in Hpos.
  apply (@pctableau_inconsistent_insert_negative_iff Atom H efq t p) in Hneg.
  destruct Hpos as [g1 [d1 [Hg1 [Hd1 [b1]]]]].
  destruct Hneg as [g2 [d2 [Hg2 [Hd2 [b2]]]]].
  apply (Hcon (g1 ++ g2) (d1 ++ d2)).
  - apply (proj2 (pct_list_covered_app _ _ _)); auto.
  - apply (proj2 (pct_list_covered_app _ _ _)); auto.
  - constructor.
    pose (b1' := ph_hilbert_imp_trans
      (generic_minimal_and_swap_axiom_raw
        (ph_hilbert_generic_minimal H) (pct_conj g1) p) b1).
    pose (cut := @ph_hilbert_and_or_cut Atom H
      (pct_conj g1) (pct_conj g2) p
      (pct_disj d1) (pct_disj d2) b1' b2).
    exact (ph_hilbert_imp_trans
      (generic_minimal_list_conj2_append_to_and_raw
        (ph_hilbert_generic_minimal H) g1 g2)
      (ph_hilbert_imp_trans cut
        (generic_intuitionistic_or_to_list_disj2_append_raw
          (@ph_hilbert_generic_intuitionistic Atom H efq) d1 d2))).
Qed.

(** * A factored enumerated Lindenbaum chain *)

Definition pctableau_next {Atom : Type} (H : ph_hilbert Atom)
    (p : pformula Atom) (t : pctableau Atom) : pctableau Atom :=
  if excluded_middle_informative
      (pctableau_consistent H (pctableau_insert_positive p t))
  then pctableau_insert_positive p t
  else pctableau_insert_negative p t.

Fixpoint pctableau_chain {Atom : Type} (K : pformula_atom_codec Atom)
    (H : ph_hilbert Atom) (t : pctableau Atom) (n : nat) : pctableau Atom :=
  match n with
  | 0 => t
  | S k => pctableau_next H (pformula_enum K k)
             (pctableau_chain K H t k)
  end.

Definition pctableau_limit {Atom : Type} (K : pformula_atom_codec Atom)
    (H : ph_hilbert Atom) (t : pctableau Atom) : pctableau Atom :=
  (fun p => exists n, pctableau_positive (pctableau_chain K H t n) p,
   fun p => exists n, pctableau_negative (pctableau_chain K H t n) p).

Lemma pctableau_next_includes :
  forall (Atom : Type) (H : ph_hilbert Atom) p t,
    pctableau_subset t (pctableau_next H p t).
Proof.
  intros Atom H p t. unfold pctableau_next.
  destruct (excluded_middle_informative _).
  - apply pctableau_insert_positive_includes.
  - apply pctableau_insert_negative_includes.
Qed.

Lemma pctableau_next_consistent :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) p t,
    pctableau_consistent H t ->
    pctableau_consistent H (pctableau_next H p t).
Proof.
  intros Atom H efq p t Hcon. unfold pctableau_next.
  destruct (excluded_middle_informative _) as [Hleft | Hleft].
  - exact Hleft.
  - destruct (pctableau_consistent_either efq Hcon p) as [Hpos | Hneg].
    + contradiction.
    + exact Hneg.
Qed.

Lemma pctableau_chain_included_succ :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom) t n,
    pctableau_subset (pctableau_chain K H t n)
      (pctableau_chain K H t (S n)).
Proof. intros; simpl; apply pctableau_next_includes. Qed.

Lemma pctableau_chain_included_le :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom) t m n,
    m <= n -> pctableau_subset (pctableau_chain K H t m)
      (pctableau_chain K H t n).
Proof.
  intros Atom K H t m n Hmn. induction Hmn.
  - apply pctableau_subset_refl.
  - eapply pctableau_subset_trans; [exact IHHmn |].
    apply pctableau_chain_included_succ.
Qed.

Lemma pctableau_chain_consistent :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) t,
    pctableau_consistent H t -> forall n,
    pctableau_consistent H (pctableau_chain K H t n).
Proof.
  intros Atom K H efq t Hcon n. induction n; simpl.
  - exact Hcon.
  - now apply pctableau_next_consistent.
Qed.

Lemma pctableau_chain_decides_enumerated :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom) t n,
    pctableau_positive (pctableau_chain K H t (S n))
      (pformula_enum K n) \/
    pctableau_negative (pctableau_chain K H t (S n))
      (pformula_enum K n).
Proof.
  intros Atom K H t n. simpl. unfold pctableau_next.
  destruct (excluded_middle_informative _); cbn; auto.
Qed.

Lemma pctableau_limit_includes :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom) t,
    pctableau_subset t (pctableau_limit K H t).
Proof. intros; split; intros p Hp; exists 0; exact Hp. Qed.

Lemma pctableau_limit_saturated :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom) t,
    pctableau_saturated (pctableau_limit K H t).
Proof.
  intros Atom K H t p.
  destruct (pformula_enum_surjective K p) as [n Henum].
  destruct (pctableau_chain_decides_enumerated K H t n) as [Hp | Hp].
  - left. exists (S n). now rewrite <- Henum.
  - right. exists (S n). now rewrite <- Henum.
Qed.

Lemma pctableau_limit_list_stage_positive :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom) t gamma,
    pct_list_covered (pctableau_positive (pctableau_limit K H t)) gamma ->
    exists n,
      pct_list_covered (pctableau_positive (pctableau_chain K H t n)) gamma.
Proof.
  intros Atom K H t gamma. induction gamma as [|p gamma IH]; intro Hcover.
  - exists 0. apply pct_list_covered_nil.
  - apply pct_list_covered_cons in Hcover as [Hp Hgamma].
    destruct Hp as [m Hm]. destruct (IH Hgamma) as [n Hn].
    exists (Nat.max m n). apply pct_list_covered_cons. split.
    + apply (proj1 (@pctableau_chain_included_le Atom K H t m (Nat.max m n)
        (Nat.le_max_l _ _))). exact Hm.
    + intros q hq. apply (proj1 (@pctableau_chain_included_le Atom K H t n
        (Nat.max m n) (Nat.le_max_r _ _))). now apply Hn.
Qed.

Lemma pctableau_limit_list_stage_negative :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom) t delta,
    pct_list_covered (pctableau_negative (pctableau_limit K H t)) delta ->
    exists n,
      pct_list_covered (pctableau_negative (pctableau_chain K H t n)) delta.
Proof.
  intros Atom K H t delta. induction delta as [|p delta IH]; intro Hcover.
  - exists 0. apply pct_list_covered_nil.
  - apply pct_list_covered_cons in Hcover as [Hp Hdelta].
    destruct Hp as [m Hm]. destruct (IH Hdelta) as [n Hn].
    exists (Nat.max m n). apply pct_list_covered_cons. split.
    + apply (proj2 (@pctableau_chain_included_le Atom K H t m (Nat.max m n)
        (Nat.le_max_l _ _))). exact Hm.
    + intros q hq. apply (proj2 (@pctableau_chain_included_le Atom K H t n
        (Nat.max m n) (Nat.le_max_r _ _))). now apply Hn.
Qed.

Lemma pctableau_limit_consistent :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) t,
    pctableau_consistent H t ->
    pctableau_consistent H (pctableau_limit K H t).
Proof.
  intros Atom K H efq t Hcon gamma delta Hg Hd Hprov.
  destruct (@pctableau_limit_list_stage_positive Atom K H t gamma Hg)
    as [m Hgm].
  destruct (@pctableau_limit_list_stage_negative Atom K H t delta Hd)
    as [n Hdn].
  apply (@pctableau_chain_consistent Atom K H efq t Hcon
    (Nat.max m n) gamma delta).
  - intros p hp. apply (proj1 (@pctableau_chain_included_le Atom K H t m
      (Nat.max m n) (Nat.le_max_l _ _))). now apply Hgm.
  - intros p hp. apply (proj2 (@pctableau_chain_included_le Atom K H t n
      (Nat.max m n) (Nat.le_max_r _ _))). now apply Hdn.
  - exact Hprov.
Qed.

Theorem pctableau_lindenbaum :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) t,
    pctableau_consistent H t ->
    exists u, pctableau_subset t u /\
      pctableau_consistent H u /\ pctableau_saturated u.
Proof.
  intros Atom K H efq t Hcon.
  exists (pctableau_limit K H t). split.
  - exact (@pctableau_limit_includes Atom K H t).
  - split.
    + exact (@pctableau_limit_consistent Atom K H efq t Hcon).
    + exact (@pctableau_limit_saturated Atom K H t).
Qed.

(** * Saturated consistent tableaux *)

Record psctableau {Atom : Type} (H : ph_hilbert Atom) : Type := {
  psct_pair : pctableau Atom;
  psct_consistent : pctableau_consistent H psct_pair;
  psct_saturated : pctableau_saturated psct_pair
}.

Arguments psct_pair {Atom H} _.
Arguments psct_consistent {Atom H} _.
Arguments psct_saturated {Atom H} _.

Definition psct_positive {Atom : Type} {H : ph_hilbert Atom}
    (W : psctableau H) : pformula Atom -> Prop :=
  pctableau_positive (psct_pair W).

Definition psct_negative {Atom : Type} {H : ph_hilbert Atom}
    (W : psctableau H) : pformula Atom -> Prop :=
  pctableau_negative (psct_pair W).

Theorem psct_lindenbaum :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) t,
    pctableau_consistent H t ->
    exists W : psctableau H, pctableau_subset t (psct_pair W).
Proof.
  intros Atom K H efq t Hcon.
  destruct (@pctableau_lindenbaum Atom K H efq t Hcon)
    as [u [Hsub [Hu Hsat]]].
  exists {| psct_pair := u; psct_consistent := Hu;
            psct_saturated := Hsat |}.
  exact Hsub.
Qed.

Lemma psct_not_both :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p,
    ~ (psct_positive W p /\ psct_negative W p).
Proof. intros; now apply (pctableau_not_both (psct_consistent W)). Qed.

Lemma psct_not_positive_iff_negative :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p,
    (~ psct_positive W p <-> psct_negative W p).
Proof.
  intros Atom H W p.
  apply (@pctableau_not_positive_iff_negative Atom H (psct_pair W)).
  - apply psct_consistent.
  - apply psct_saturated.
Qed.

Lemma psct_not_negative_iff_positive :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p,
    (~ psct_negative W p <-> psct_positive W p).
Proof.
  intros Atom H W p.
  apply (@pctableau_not_negative_iff_positive Atom H (psct_pair W)).
  - apply psct_consistent.
  - apply psct_saturated.
Qed.

Lemma psct_equiv_of_positive :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W U : psctableau H),
    (forall p, psct_positive W p <-> psct_positive U p) ->
    forall p, psct_negative W p <-> psct_negative U p.
Proof.
  intros Atom H W U Heq.
  apply (proj1 (pctableau_saturated_duality
    (psct_consistent W) (psct_consistent U)
    (psct_saturated W) (psct_saturated U))). exact Heq.
Qed.

Lemma psct_equiv_of_negative :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W U : psctableau H),
    (forall p, psct_negative W p <-> psct_negative U p) ->
    forall p, psct_positive W p <-> psct_positive U p.
Proof.
  intros Atom H W U Heq.
  apply (proj2 (pctableau_saturated_duality
    (psct_consistent W) (psct_consistent U)
    (psct_saturated W) (psct_saturated U))). exact Heq.
Qed.

Lemma psct_not_negative_of_provable_context :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) gamma p,
    pct_list_covered (psct_positive W) gamma ->
    ph_hilbert_provable H (PImp (pct_conj gamma) p) ->
    ~ psct_negative W p.
Proof.
  intros Atom H W gamma p Hgamma Hproof.
  exact (@pctableau_not_negative_of_provable_context Atom H
    (psct_pair W) gamma p (psct_consistent W) Hgamma Hproof).
Qed.

Lemma pctableau_false_covered_nil :
  forall (F : Type) (gamma : list F),
    pct_list_covered (fun _ => False) gamma -> gamma = [].
Proof.
  intros F gamma H. destruct gamma as [|p gamma]; [reflexivity |].
  exfalso. exact (H p (GRLM_here gamma)).
Qed.

Definition ph_hilbert_bottom_consistent {Atom : Type}
    (H : ph_hilbert Atom) : Prop :=
  ~ ph_hilbert_provable H PFalsum.

Lemma pctableau_empty_consistent :
  forall (Atom : Type) (H : ph_hilbert Atom),
    ph_hilbert_bottom_consistent H ->
    pctableau_consistent H ((fun _ => False), (fun _ => False)).
Proof.
  intros Atom H Hbottom gamma delta Hg Hd [d].
  apply pctableau_false_covered_nil in Hg.
  apply pctableau_false_covered_nil in Hd. subst gamma delta.
  apply Hbottom. constructor. exact (PHPModusPonens d PHPVerum).
Qed.

Theorem psctableau_inhabited :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)),
    ph_hilbert_bottom_consistent H -> inhabited (psctableau H).
Proof.
  intros Atom K H efq Hbottom.
  destruct (@psct_lindenbaum Atom K H efq
    ((fun _ => False), (fun _ => False))
    (@pctableau_empty_consistent Atom H Hbottom)) as [W _].
  now constructor.
Qed.

(** * Closure under the Hilbert connectives *)

Lemma psct_theorem_positive_raw :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p,
    ph_hilbert_proof H p -> psct_positive W p.
Proof.
  intros Atom H W p d.
  apply (proj1 (psct_not_negative_iff_positive W p)). intro Hneg.
  apply (psct_consistent W [] [p]).
  - apply pct_list_covered_nil.
  - apply pct_list_covered_cons. split; [exact Hneg |].
    apply pct_list_covered_nil.
  - constructor. exact (@ph_hilbert_dhyp Atom H p ptop d).
Qed.

Lemma psct_theorem_positive :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p,
    ph_hilbert_provable H p -> psct_positive W p.
Proof. intros Atom H W p [d]; now apply psct_theorem_positive_raw. Qed.

Lemma psct_mdp_theorem_positive :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p q,
    ph_hilbert_proof H (PImp p q) ->
    psct_positive W p -> psct_positive W q.
Proof.
  intros Atom H W p q d Hp.
  apply (proj1 (psct_not_negative_iff_positive W q)). intro Hq.
  apply (psct_consistent W [p] [q]).
  - apply pct_list_covered_cons. split; [exact Hp |].
    apply pct_list_covered_nil.
  - apply pct_list_covered_cons. split; [exact Hq |].
    apply pct_list_covered_nil.
  - constructor. exact d.
Qed.

Lemma psct_mdp_theorem_negative :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p q,
    ph_hilbert_proof H (PImp p q) ->
    psct_negative W q -> psct_negative W p.
Proof.
  intros Atom H W p q d Hq.
  apply (proj1 (psct_not_positive_iff_negative W p)). intro Hp.
  pose proof (@psct_mdp_theorem_positive Atom H W p q d Hp) as Hqp.
  exact (@psct_not_both Atom H W q (conj Hqp Hq)).
Qed.

Lemma psct_top_positive :
  forall (Atom : Type) (H : ph_hilbert Atom) (W : psctableau H),
    psct_positive W ptop.
Proof. intros; apply psct_theorem_positive_raw; exact PHPVerum. Qed.

Lemma psct_bottom_not_positive :
  forall (Atom : Type) (H : ph_hilbert Atom) (W : psctableau H),
    ~ psct_positive W PFalsum.
Proof.
  intros Atom H W Hbot.
  apply (psct_consistent W [PFalsum] []).
  - apply pct_list_covered_cons. split; [exact Hbot |].
    apply pct_list_covered_nil.
  - apply pct_list_covered_nil.
  - constructor. exact (ph_hilbert_identity H PFalsum).
Qed.

Lemma psct_bottom_negative :
  forall (Atom : Type) (H : ph_hilbert Atom) (W : psctableau H),
    psct_negative W PFalsum.
Proof.
  intros. apply (proj1 (psct_not_positive_iff_negative W PFalsum)).
  apply psct_bottom_not_positive.
Qed.

Lemma psct_mdp_positive :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p q,
    psct_positive W (PImp p q) ->
    psct_positive W p -> psct_positive W q.
Proof.
  intros Atom H W p q Himp Hp.
  apply (proj1 (psct_not_negative_iff_positive W q)). intro Hq.
  apply (psct_consistent W [p; PImp p q] [q]).
  - apply pct_list_covered_cons. split; [exact Hp |].
    apply pct_list_covered_cons. split; [exact Himp |].
    apply pct_list_covered_nil.
  - apply pct_list_covered_cons. split; [exact Hq |].
    apply pct_list_covered_nil.
  - constructor.
    apply (@ph_hilbert_conj2_to_disj2_of_mdp_members Atom H
      [p; PImp p q] [q] p q).
    + apply GRLM_here.
    + apply GRLM_there. apply GRLM_here.
    + apply GRLM_here.
Qed.

Lemma psct_and_positive_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p q,
    (psct_positive W (PAnd p q) <->
     psct_positive W p /\ psct_positive W q).
Proof.
  intros Atom H W p q; split.
  - intro Hand. split.
    + exact (@psct_mdp_theorem_positive Atom H W (PAnd p q) p
        (PHPAndElimL p q) Hand).
    + exact (@psct_mdp_theorem_positive Atom H W (PAnd p q) q
        (PHPAndElimR p q) Hand).
  - intros [Hp Hq].
    apply (proj1 (psct_not_negative_iff_positive W (PAnd p q))).
    intro Handneg.
    apply (psct_consistent W [p; q] [PAnd p q]).
    + apply pct_list_covered_cons. split; [exact Hp |].
      apply pct_list_covered_cons. split; [exact Hq |].
      apply pct_list_covered_nil.
    + apply pct_list_covered_cons. split; [exact Handneg |].
      apply pct_list_covered_nil.
    + constructor.
      apply (@ph_hilbert_conj2_to_disj2_of_and_member Atom H
        [p; q] [PAnd p q] p q).
      * apply GRLM_here.
      * apply GRLM_there. apply GRLM_here.
      * apply GRLM_here.
Qed.

Lemma psct_or_positive_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p q,
    (psct_positive W (POr p q) <->
     psct_positive W p \/ psct_positive W q).
Proof.
  intros Atom H W p q; split.
  - intro Hor.
    destruct (psct_saturated W p) as [Hp | Hpneg]; [now left |].
    destruct (psct_saturated W q) as [Hq | Hqneg]; [now right |].
    exfalso.
    apply (psct_consistent W [POr p q] [p; q]).
    + apply pct_list_covered_cons. split; [exact Hor |].
      apply pct_list_covered_nil.
    + apply pct_list_covered_cons. split; [exact Hpneg |].
      apply pct_list_covered_cons. split; [exact Hqneg |].
      apply pct_list_covered_nil.
    + constructor.
      apply (@ph_hilbert_conj2_to_disj2_of_or_member Atom H
        [POr p q] [p; q] p q).
      * apply GRLM_here.
      * apply GRLM_here.
      * apply GRLM_there. apply GRLM_here.
  - intros [Hp | Hq].
    + exact (@psct_mdp_theorem_positive Atom H W p (POr p q)
        (PHPOrIntroL p q) Hp).
    + exact (@psct_mdp_theorem_positive Atom H W q (POr p q)
        (PHPOrIntroR p q) Hq).
Qed.

Lemma psct_or_negative_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p q,
    (psct_negative W (POr p q) <->
     psct_negative W p /\ psct_negative W q).
Proof.
  intros Atom H W p q. split.
  - intro Hor. split.
    + apply (proj1 (psct_not_positive_iff_negative W p)). intro Hp.
      pose proof (proj2 (psct_or_positive_iff W p q) (or_introl Hp)) as Hpos.
      exact (@psct_not_both Atom H W (POr p q) (conj Hpos Hor)).
    + apply (proj1 (psct_not_positive_iff_negative W q)). intro Hq.
      pose proof (proj2 (psct_or_positive_iff W p q) (or_intror Hq)) as Hpos.
      exact (@psct_not_both Atom H W (POr p q) (conj Hpos Hor)).
  - intros [Hp Hq].
    apply (proj1 (psct_not_positive_iff_negative W (POr p q))). intro Hor.
    destruct (proj1 (psct_or_positive_iff W p q) Hor) as [Hpos | Hpos].
    + exact (@psct_not_both Atom H W p (conj Hpos Hp)).
    + exact (@psct_not_both Atom H W q (conj Hpos Hq)).
Qed.

Lemma psct_imp_positive_cases :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p q,
    psct_positive W (PImp p q) ->
    psct_negative W p \/ psct_positive W q.
Proof.
  intros Atom H W p q Himp.
  destruct (psct_saturated W p) as [Hp | Hp]; [right | now left].
  exact (@psct_mdp_positive Atom H W p q Himp Hp).
Qed.

Lemma psct_neg_positive_implies_negative :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p,
    psct_positive W (pneg p) -> psct_negative W p.
Proof.
  intros Atom H W p Hneg.
  destruct (@psct_imp_positive_cases Atom H W p PFalsum Hneg)
    as [Hp | Hbottom].
  - exact Hp.
  - exfalso. exact (@psct_bottom_not_positive Atom H W Hbottom).
Qed.

Lemma psct_positive_implies_neg_negative :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) p,
    psct_positive W p -> psct_negative W (pneg p).
Proof.
  intros Atom H W p Hp.
  apply (proj1 (psct_not_positive_iff_negative W (pneg p))). intro Hneg.
  pose proof (@psct_mdp_positive Atom H W p PFalsum Hneg Hp) as Hbottom.
  exact (@psct_bottom_not_positive Atom H W Hbottom).
Qed.

Lemma psct_conj_positive_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) gamma,
    (psct_positive W (pct_conj gamma) <->
     pct_list_covered (psct_positive W) gamma).
Proof.
  intros Atom H W gamma. induction gamma as [|p gamma IH].
  - split; intro Hx.
    + apply pct_list_covered_nil.
    + apply psct_top_positive.
  - destruct gamma as [|q gamma].
    + split; intro Hx.
      * apply pct_list_covered_cons. split; [exact Hx |].
        apply pct_list_covered_nil.
      * now apply pct_list_covered_cons in Hx as [Hp _].
    + change (psct_positive W (PAnd p (pct_conj (q :: gamma))) <->
        pct_list_covered (psct_positive W) (p :: q :: gamma)).
      split.
      * intro Hpq. apply psct_and_positive_iff in Hpq as [Hp Htail].
        apply pct_list_covered_cons. split; [exact Hp |].
        now apply IH.
      * intro Hcovered. apply pct_list_covered_cons in Hcovered as [Hp Htail].
        apply psct_and_positive_iff. split; [exact Hp |].
        now apply IH.
Qed.

Lemma psct_disj_negative_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (W : psctableau H) delta,
    (psct_negative W (pct_disj delta) <->
     pct_list_covered (psct_negative W) delta).
Proof.
  intros Atom H W delta. induction delta as [|p delta IH].
  - split; intro Hx.
    + apply pct_list_covered_nil.
    + apply psct_bottom_negative.
  - destruct delta as [|q delta].
    + split; intro Hx.
      * apply pct_list_covered_cons. split; [exact Hx |].
        apply pct_list_covered_nil.
      * now apply pct_list_covered_cons in Hx as [Hp _].
    + change (psct_negative W (POr p (pct_disj (q :: delta))) <->
        pct_list_covered (psct_negative W) (p :: q :: delta)).
      split.
      * intro Hpq. apply psct_or_negative_iff in Hpq as [Hp Htail].
        apply pct_list_covered_cons. split; [exact Hp |].
        now apply IH.
      * intro Hcovered. apply pct_list_covered_cons in Hcovered as [Hp Htail].
        apply psct_or_negative_iff. split; [exact Hp |].
        now apply IH.
Qed.

(** * Contextual completeness *)

Definition pct_context_provable {Atom : Type} (H : ph_hilbert Atom)
    (T : pformula Atom -> Prop) (p : pformula Atom) : Prop :=
  inhabited (ph_hilbert_type_context_proof H
    (generic_proof_relevant_context T) p).

Fixpoint pct_list_derivation_bind_raw {Atom : Type}
    (H : ph_hilbert Atom) {gamma : list (pformula Atom)}
    {T : pformula Atom -> Type}
    (replace : forall q, generic_raw_list_member q gamma ->
      ph_hilbert_type_context_proof H T q)
    {p} (d : ph_hilbert_context_proof H gamma p) :
    ph_hilbert_type_context_proof H T p.
Proof.
  destruct d as [p hp | p b | p q dpq dp].
  - exact (replace p hp).
  - exact (GTCD_theorem b).
  - exact (GTCD_mdp
      (@pct_list_derivation_bind_raw Atom H gamma T replace (PImp p q) dpq)
      (@pct_list_derivation_bind_raw Atom H gamma T replace p dp)).
Defined.

Fixpoint psct_context_positive_raw {Atom : Type} {H : ph_hilbert Atom}
    (W : psctableau H) (T : pformula Atom -> Prop)
    (incl : forall q, T q -> psct_positive W q) {p}
    (d : ph_hilbert_type_context_proof H
      (generic_proof_relevant_context T) p) : psct_positive W p.
Proof.
  destruct d as [p hp | p b | p q dpq dp].
  - exact (incl p (proj2_sig hp)).
  - exact (@psct_theorem_positive_raw Atom H W p b).
  - exact (@psct_mdp_positive Atom H W p q
      (@psct_context_positive_raw Atom H W T incl (PImp p q) dpq)
      (@psct_context_positive_raw Atom H W T incl p dp)).
Defined.

Definition pctableau_context_counterexample {Atom : Type}
    (T : pformula Atom -> Prop) (p : pformula Atom) : pctableau Atom :=
  (T, fun q => q = p).

Lemma pctableau_context_counterexample_consistent :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) T p,
    ~ pct_context_provable H T p ->
    pctableau_consistent H (pctableau_context_counterexample T p).
Proof.
  intros Atom H efq T p Hnot gamma delta Hgamma Hdelta [d].
  apply Hnot. constructor.
  apply (@pct_list_derivation_bind_raw Atom H gamma
    (generic_proof_relevant_context T)).
  - intros q hq. apply GTCD_assumption. exists tt. exact (Hgamma q hq).
  - apply (@ph_hilbert_context_of_conj2 Atom H gamma p).
    exact (ph_hilbert_imp_trans d
      (@generic_intuitionistic_list_disj2_unique_raw
        (ph_hilbert Atom) (pformula Atom)
        (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
        (@ph_hilbert_generic_intuitionistic Atom H efq) p delta
        (fun q hq => Hdelta q hq))).
Qed.

Theorem psct_context_provable_iff :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) T p,
    (pct_context_provable H T p <->
     forall W : psctableau H,
       (forall q, T q -> psct_positive W q) -> psct_positive W p).
Proof.
  intros Atom K H efq T p. split.
  - intros [d] W Hincl.
    exact (@psct_context_positive_raw Atom H W T Hincl p d).
  - intro Hall. apply NNPP. intro Hnot.
    destruct (@psct_lindenbaum Atom K H efq
      (pctableau_context_counterexample T p)
      (@pctableau_context_counterexample_consistent Atom H efq T p Hnot))
      as [W Hsub].
    pose proof (Hall W (fun q hq => (proj1 Hsub) q hq)) as Hp.
    pose proof ((proj2 Hsub) p eq_refl) as Hpn.
    exact (@psct_not_both Atom H W p (conj Hp Hpn)).
Qed.

Definition pct_empty_context_to_proof {Atom : Type} (H : ph_hilbert Atom)
    {p : pformula Atom}
    (d : ph_hilbert_type_context_proof H
      (generic_proof_relevant_context (fun _ => False)) p) :
    ph_hilbert_proof H p :=
  generic_empty_type_context_derivation_raw (ph_hilbert_modus_ponens H)
    (generic_type_context_derivation_weaken_raw
      (fun q h => False_rect (generic_empty_type_context q) (proj2_sig h)) d).

Theorem psct_provable_iff :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall q, ph_hilbert_proof H (ph_axiom_efq q)) p,
    (ph_hilbert_provable H p <->
     forall W : psctableau H, psct_positive W p).
Proof.
  intros Atom K H efq p. split.
  - intros Hp W. exact (@psct_theorem_positive Atom H W p Hp).
  - intro Hall.
    assert (Hctx : pct_context_provable H (fun _ => False) p).
    { apply (proj2 (@psct_context_provable_iff Atom K H efq
        (fun _ => False) p)).
      intros W _. exact (Hall W). }
    destruct Hctx as [d]. constructor.
    exact (@pct_empty_context_to_proof Atom H p d).
Qed.

(** * Exact classical implication laws

    Foundation obtains these through the global completeness equivalence.
    The local proof below only needs excluded middle as a Hilbert theorem, so
    it drops the source's atom encoding and decidable-equality hypotheses. *)

Lemma psct_classical_imp_positive_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (HC : generic_classical_entailment
        (ph_hilbert_entailment Atom) (pformula_connectives Atom) H)
      (W : psctableau H) p q,
    (psct_positive W (PImp p q) <->
     psct_negative W p \/ psct_positive W q).
Proof.
  intros Atom H HC W p q. split.
  - apply psct_imp_positive_cases.
  - intros [Hpneg | Hq].
    + pose proof (@psct_theorem_positive_raw Atom H W
        (POr p (pneg p)) (generic_classical_lem_raw HC p)) as Hlem.
      destruct (proj1 (@psct_or_positive_iff Atom H W p (pneg p)) Hlem)
        as [Hp | Hnp].
      * exfalso. exact (@psct_not_both Atom H W p (conj Hp Hpneg)).
      * exact (@psct_mdp_theorem_positive Atom H W (pneg p) (PImp p q)
          (generic_intuitionistic_neg_imp_explosion_raw
            (generic_intuitionistic_of_classical HC) p q) Hnp).
    + exact (@psct_mdp_theorem_positive Atom H W q (PImp p q)
        (PHPImplyK q p) Hq).
Qed.

Lemma psct_classical_imp_negative_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (HC : generic_classical_entailment
        (ph_hilbert_entailment Atom) (pformula_connectives Atom) H)
      (W : psctableau H) p q,
    (psct_negative W (PImp p q) <->
     psct_positive W p /\ psct_negative W q).
Proof.
  intros Atom H HC W p q. split.
  - intro Himp. split.
    + apply (proj1 (psct_not_negative_iff_positive W p)). intro Hpneg.
      apply (@psct_not_both Atom H W (PImp p q)). split; [|exact Himp].
      apply (proj2 (@psct_classical_imp_positive_iff Atom H HC W p q)).
      now left.
    + apply (proj1 (psct_not_positive_iff_negative W q)). intro Hq.
      apply (@psct_not_both Atom H W (PImp p q)). split; [|exact Himp].
      apply (proj2 (@psct_classical_imp_positive_iff Atom H HC W p q)).
      now right.
  - intros [Hp Hq].
    apply (proj1 (psct_not_positive_iff_negative W (PImp p q))).
    intro Himp.
    destruct (proj1 (@psct_classical_imp_positive_iff Atom H HC W p q)
      Himp) as [Hpneg | Hqpos].
    + exact (@psct_not_both Atom H W p (conj Hp Hpneg)).
    + exact (@psct_not_both Atom H W q (conj Hqpos Hq)).
Qed.

Lemma psct_classical_neg_positive_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (HC : generic_classical_entailment
        (ph_hilbert_entailment Atom) (pformula_connectives Atom) H)
      (W : psctableau H) p,
    (psct_positive W (pneg p) <-> psct_negative W p).
Proof.
  intros Atom H HC W p.
  rewrite (@psct_classical_imp_positive_iff Atom H HC W p PFalsum).
  split; [intros [Hp | Hbot] | intro Hp; now left].
  - exact Hp.
  - exfalso. exact (@psct_bottom_not_positive Atom H W Hbot).
Qed.

Lemma psct_classical_neg_negative_iff :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (HC : generic_classical_entailment
        (ph_hilbert_entailment Atom) (pformula_connectives Atom) H)
      (W : psctableau H) p,
    (psct_negative W (pneg p) <-> psct_positive W p).
Proof.
  intros Atom H HC W p.
  rewrite (@psct_classical_imp_negative_iff Atom H HC W p PFalsum).
  split.
  - now intros [Hp _].
  - intro Hp. split; [exact Hp | apply psct_bottom_negative].
Qed.
