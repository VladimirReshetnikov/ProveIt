(** Two-sided maximal tableaux over arbitrary modal atom types.

    A two-sided classical tableau is most economically represented by one
    maximal theory: the positive side contains its members and the negative
    side contains formulas whose negations are members.  This presentation
    makes disjointness and saturation structural, drops Foundation's
    [DecidableEq]/[Encodable] hypotheses, and reuses the atom-polymorphic
    Zorn construction instead of maintaining a second enumeration chain. *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality Logic.ProofIrrelevance.
From FoundationModal Require Import
  Syntax LogicInfrastructure MaximalTheoryLaws.
From Foundation.Modal Require Import MaximalConsistentSet MaximalCanonical.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record abstract_tableau (AtomType : Type) : Type := {
  at_positive : formula AtomType -> Prop;
  at_negative : formula AtomType -> Prop
}.

Arguments abstract_tableau (AtomType) : clear implicits.
Arguments at_positive {AtomType} _ _.
Arguments at_negative {AtomType} _ _.

Definition abstract_tableau_subset {AtomType}
    (t u : abstract_tableau AtomType) : Prop :=
  (forall p, at_positive t p -> at_positive u p) /\
  (forall p, at_negative t p -> at_negative u p).

(** Refuted formulas become negated assumptions in the one-sided seed. *)
Definition abstract_tableau_seed {AtomType}
    (t : abstract_tableau AtomType) : abstract_formula_theory AtomType :=
  fun p => at_positive t p \/
    exists q, at_negative t q /\ p = Neg q.

Definition abstract_tableau_consistent {AtomType}
    (L : modal_logic_set AtomType) (t : abstract_tableau AtomType) : Prop :=
  abstract_context_consistent L (abstract_tableau_seed t).

Definition abstract_tableau_inconsistent {AtomType}
    (L : modal_logic_set AtomType) (t : abstract_tableau AtomType) : Prop :=
  ~ abstract_tableau_consistent L t.

Definition abstract_tableau_insert_positive {AtomType}
    (p : formula AtomType) (t : abstract_tableau AtomType) :
    abstract_tableau AtomType :=
  {| at_positive := fun q => q = p \/ at_positive t q;
     at_negative := at_negative t |}.

Definition abstract_tableau_insert_negative {AtomType}
    (p : formula AtomType) (t : abstract_tableau AtomType) :
    abstract_tableau AtomType :=
  {| at_positive := at_positive t;
     at_negative := fun q => q = p \/ at_negative t q |}.

Definition abstract_empty_tableau {AtomType} : abstract_tableau AtomType :=
  {| at_positive := fun _ => False;
     at_negative := fun _ => False |}.

Definition abstract_singleton_negative_tableau {AtomType}
    (p : formula AtomType) : abstract_tableau AtomType :=
  {| at_positive := fun _ => False;
     at_negative := fun q => q = p |}.

Definition abstract_maximal_tableau (AtomType : Type)
    (L : modal_logic_set AtomType) : Type :=
  abstract_normal_mct AtomType L.

Arguments abstract_maximal_tableau (AtomType) L : clear implicits.

Definition amt_positive {AtomType L}
    (M : abstract_maximal_tableau AtomType L) (p : formula AtomType) : Prop :=
  anmct_mem M p.

Definition amt_negative {AtomType L}
    (M : abstract_maximal_tableau AtomType L) (p : formula AtomType) : Prop :=
  anmct_mem M (Neg p).

Definition amt_as_tableau {AtomType L}
    (M : abstract_maximal_tableau AtomType L) : abstract_tableau AtomType :=
  {| at_positive := amt_positive M;
     at_negative := amt_negative M |}.

Lemma abstract_context_derives_empty_iff_classical :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    abstract_context_derives L (fun _ => False) p <-> L p.
Proof.
  intros AtomType L Hclass p; split.
  - intro Hp. induction Hp.
    + contradiction.
    + assumption.
    + eapply (logic_modus_ponens Hclass); eauto.
  - now apply ACD_theorem.
Qed.

Lemma abstract_singleton_negative_seed :
  forall (AtomType : Type) (p : formula AtomType),
    abstract_tableau_seed (abstract_singleton_negative_tableau p) =
    abstract_theory_insert (fun _ => False) (Neg p).
Proof.
  intros AtomType p. apply functional_extensionality; intro q.
  apply propositional_extensionality. unfold abstract_tableau_seed,
    abstract_singleton_negative_tableau, abstract_theory_insert; cbn.
  split.
  - intros [H | [r [-> ->]]]; [contradiction | now left].
  - intros [-> | H]; [right; exists p; auto | contradiction].
Qed.

Lemma abstract_tableau_insert_positive_seed :
  forall (AtomType : Type) (t : abstract_tableau AtomType) p,
    abstract_tableau_seed (abstract_tableau_insert_positive p t) =
    abstract_theory_insert (abstract_tableau_seed t) p.
Proof.
  intros AtomType t p. apply functional_extensionality; intro q.
  apply propositional_extensionality. unfold abstract_tableau_seed,
    abstract_tableau_insert_positive, abstract_theory_insert; cbn.
  firstorder.
Qed.

Lemma abstract_tableau_insert_negative_seed :
  forall (AtomType : Type) (t : abstract_tableau AtomType) p,
    abstract_tableau_seed (abstract_tableau_insert_negative p t) =
    abstract_theory_insert (abstract_tableau_seed t) (Neg p).
Proof.
  intros AtomType t p. apply functional_extensionality; intro q.
  apply propositional_extensionality. unfold abstract_tableau_seed,
    abstract_tableau_insert_negative, abstract_theory_insert; cbn.
  split.
  - intros [Hq | [r [[-> | Hr] ->]]].
    + right. now left.
    + now left.
    + right. right. exists r. now split.
  - intros [-> | [Hq | [r [Hr ->]]]].
    + right. exists p. split; [now left | reflexivity].
    + now left.
    + right. exists r. split; [now right | reflexivity].
Qed.

Theorem abstract_tableau_insert_positive_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall t p,
    abstract_tableau_consistent L
      (abstract_tableau_insert_positive p t) <->
    ~ abstract_context_derives L (abstract_tableau_seed t) (Neg p).
Proof.
  intros AtomType L Hclass t p. unfold abstract_tableau_consistent.
  rewrite abstract_tableau_insert_positive_seed.
  apply abstract_insert_consistent_iff, Hclass.
Qed.

Theorem abstract_tableau_insert_negative_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall t p,
    abstract_tableau_consistent L
      (abstract_tableau_insert_negative p t) <->
    ~ abstract_context_derives L (abstract_tableau_seed t) p.
Proof.
  intros AtomType L Hclass t p. unfold abstract_tableau_consistent.
  rewrite abstract_tableau_insert_negative_seed.
  apply abstract_insert_neg_consistent_iff, Hclass.
Qed.

Theorem abstract_tableau_either_expand_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall t,
    abstract_tableau_consistent L t -> forall p,
    abstract_tableau_consistent L
      (abstract_tableau_insert_positive p t) \/
    abstract_tableau_consistent L
      (abstract_tableau_insert_negative p t).
Proof.
  intros AtomType L Hclass t Hconsistent p.
  unfold abstract_tableau_consistent in *.
  rewrite abstract_tableau_insert_positive_seed,
    abstract_tableau_insert_negative_seed.
  now apply abstract_either_insert_consistent.
Qed.

Lemma abstract_singleton_negative_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    abstract_tableau_consistent L
      (abstract_singleton_negative_tableau p) <-> ~ L p.
Proof.
  intros AtomType L Hclass p. unfold abstract_tableau_consistent.
  rewrite abstract_singleton_negative_seed.
  rewrite abstract_insert_neg_consistent_iff by exact Hclass.
  now rewrite abstract_context_derives_empty_iff_classical by exact Hclass.
Qed.

Lemma abstract_empty_tableau_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L ->
    abstract_tableau_consistent L abstract_empty_tableau <-> ~ L Bottom.
Proof.
  intros AtomType L Hclass. unfold abstract_tableau_consistent,
    abstract_empty_tableau, abstract_tableau_seed,
    abstract_context_consistent; cbn.
  assert (Hseed : (fun p : formula AtomType =>
      False \/ exists q, False /\ p = Neg q) = (fun _ => False)).
  { apply functional_extensionality; intro p.
    apply propositional_extensionality; firstorder. }
  rewrite Hseed. apply not_iff_compat.
  apply abstract_context_derives_empty_iff_classical, Hclass.
Qed.

Theorem abstract_tableau_lindenbaum :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall t,
    abstract_tableau_consistent L t ->
    exists M : abstract_maximal_tableau AtomType L,
      abstract_tableau_subset t (amt_as_tableau M).
Proof.
  intros AtomType L Hnormal t Hconsistent.
  destruct (abstract_normal_lindenbaum_extension Hnormal Hconsistent)
    as [M Hinclude]. exists M. split.
  - intros p Hp. apply Hinclude. now left.
  - intros p Hp. apply Hinclude. right. exists p. now split.
Qed.

Lemma amt_neither :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p,
    ~ (amt_positive M p /\ amt_negative M p).
Proof.
  intros AtomType L M p [Hp Hn].
  exact (@gmct_not_both AtomType (anmct_generic M) p Hp Hn).
Qed.

Lemma amt_saturated :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p,
    amt_positive M p \/ amt_negative M p.
Proof.
  intros AtomType L M p. exact (gmct_complete (anmct_generic M) p).
Qed.

Lemma amt_not_positive_iff_negative :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p,
    ~ amt_positive M p <-> amt_negative M p.
Proof.
  intros AtomType L M p. symmetry.
  exact (gmct_neg_iff (anmct_generic M) p).
Qed.

Lemma amt_not_negative_iff_positive :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p,
    ~ amt_negative M p <-> amt_positive M p.
Proof.
  intros AtomType L M p; split.
  - intro Hnotneg. destruct (amt_saturated M p) as [Hp | Hneg].
    + exact Hp.
    + contradiction.
  - intros Hp Hneg. exact (@amt_neither AtomType L M p (conj Hp Hneg)).
Qed.

Lemma anmct_extensional :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M N : abstract_normal_mct AtomType L),
    (forall p, anmct_mem M p <-> anmct_mem N p) -> M = N.
Proof.
  intros AtomType L [GM HMc HMd] [GN HNc HNd] Heq; cbn in *.
  destruct GM as [memM HclassM HbotM HcompleteM].
  destruct GN as [memN HclassN HbotN HcompleteN]. cbn in Heq.
  assert (Hmem : memM = memN).
  { apply functional_extensionality; intro p.
    apply propositional_extensionality. apply Heq. }
  subst memN.
  assert (HclassM = HclassN) by apply proof_irrelevance. subst HclassN.
  assert (HbotM = HbotN) by apply proof_irrelevance. subst HbotN.
  assert (HcompleteM = HcompleteN) by apply proof_irrelevance.
  subst HcompleteN. cbn in *.
  assert (HMc = HNc) by apply proof_irrelevance. subst HNc.
  assert (HMd = HNd) by apply proof_irrelevance. subst HNd.
  reflexivity.
Qed.

Theorem amt_positive_extensional :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M N : abstract_maximal_tableau AtomType L),
    (forall p, amt_positive M p <-> amt_positive N p) -> M = N.
Proof. intros; now apply anmct_extensional. Qed.

Theorem amt_negative_extensional :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M N : abstract_maximal_tableau AtomType L),
    (forall p, amt_negative M p <-> amt_negative N p) -> M = N.
Proof.
  intros AtomType L M N Hnegative. apply amt_positive_extensional.
  intro p. rewrite <- !amt_not_negative_iff_positive.
  now rewrite Hnegative.
Qed.

Theorem amt_inclusion_extensional :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M N : abstract_maximal_tableau AtomType L),
    (forall p, amt_positive M p -> amt_positive N p) -> M = N.
Proof.
  intros AtomType L M N Hinc. apply amt_positive_extensional.
  exact (@gmct_inclusion_extensional AtomType (anmct_generic M)
    (anmct_generic N) Hinc).
Qed.

Theorem amt_context_derivable_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall Gamma p,
    abstract_context_derives L Gamma p <->
    forall M : abstract_maximal_tableau AtomType L,
      abstract_theory_included Gamma (amt_positive M) ->
      amt_positive M p.
Proof.
  intros AtomType L Hnormal Gamma p; split.
  - intros Hp M Hinclude.
    apply (proj1 (anmct_derivable_iff M p)).
    eapply abstract_context_derives_weaken; [exact Hinclude | exact Hp].
  - intro Hall. apply NNPP. intro Hnot.
    pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
    pose proof (proj2 (abstract_insert_neg_consistent_iff
      Hclass Gamma p) Hnot) as Hconsistent.
    destruct (abstract_normal_lindenbaum_extension Hnormal Hconsistent)
      as [M Hinclude].
    apply (@gmct_not_both AtomType (anmct_generic M) p).
    + apply Hall. intros q Hq. apply Hinclude. now right.
    + apply Hinclude. now left.
Qed.

Corollary amt_theorem_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall p,
    L p <-> forall M : abstract_maximal_tableau AtomType L,
      amt_positive M p.
Proof.
  intros AtomType L Hnormal p.
  rewrite <- abstract_context_derives_empty_iff_classical
    by exact (quasi_classical (normal_quasi Hnormal)).
  rewrite amt_context_derivable_iff by exact Hnormal. split.
  - intros H M. apply H. firstorder.
  - intros H M _. apply H.
Qed.

(** * Positive and negative connective laws *)

Lemma amt_positive_bottom_absent :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L),
    ~ amt_positive M Bottom.
Proof. intros; apply gmct_bottom_absent. Qed.

Lemma amt_negative_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L),
    amt_negative M Bottom.
Proof. intros; unfold amt_negative; apply gmct_top_mem. Qed.

Lemma amt_positive_top :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L),
    amt_positive M Top.
Proof. intros; apply gmct_top_mem. Qed.

Lemma amt_negative_top_absent :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L),
    ~ amt_negative M Top.
Proof.
  intros AtomType L M. apply (proj2 (amt_not_negative_iff_positive M Top)).
  apply amt_positive_top.
Qed.

Lemma amt_positive_neg_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p,
    amt_positive M (Neg p) <-> amt_negative M p.
Proof. reflexivity. Qed.

Lemma amt_negative_neg_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p,
    amt_negative M (Neg p) <-> amt_positive M p.
Proof.
  intros AtomType L M p. unfold amt_negative, amt_positive.
  apply gmct_negneg_iff.
Qed.

Lemma amt_positive_imp_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_positive M (Imp p q) <->
    amt_negative M p \/ amt_positive M q.
Proof.
  intros AtomType L M p q; split.
  - intro Himp. destruct (amt_saturated M p) as [Hp | Hnegp].
    + right. exact (proj1 (gmct_imp_iff (anmct_generic M) p q) Himp Hp).
    + now left.
  - intros [Hnegp | Hq].
    + apply (proj2 (gmct_imp_iff (anmct_generic M) p q)).
      intro Hp. exfalso. exact (@amt_neither AtomType L M p
        (conj Hp Hnegp)).
    + apply (proj2 (gmct_imp_iff (anmct_generic M) p q)).
      intros _. exact Hq.
Qed.

Lemma amt_positive_imp_function_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_positive M (Imp p q) <->
    (amt_positive M p -> amt_positive M q).
Proof. intros; apply gmct_imp_iff. Qed.

Lemma amt_negative_imp_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_negative M (Imp p q) <->
    amt_positive M p /\ amt_negative M q.
Proof.
  intros AtomType L M p q; split.
  - intro Hnegimp.
    assert (Hnotimp : ~ amt_positive M (Imp p q)).
    { exact (proj2 (amt_not_positive_iff_negative M (Imp p q)) Hnegimp). }
    split.
    + destruct (amt_saturated M p) as [Hp | Hnegp]; [exact Hp |].
      exfalso. apply Hnotimp, (proj2
        (gmct_imp_iff (anmct_generic M) p q)).
      intro Hp. exfalso. exact (@amt_neither AtomType L M p
        (conj Hp Hnegp)).
    + destruct (amt_saturated M q) as [Hq | Hnegq]; [|exact Hnegq].
      exfalso. apply Hnotimp, (proj2
        (gmct_imp_iff (anmct_generic M) p q)).
      intros _. exact Hq.
  - intros [Hp Hnegq].
    apply (proj1 (amt_not_positive_iff_negative M (Imp p q))).
    intro Himp. apply (@amt_neither AtomType L M q).
    split.
    + exact (proj1 (gmct_imp_iff (anmct_generic M) p q) Himp Hp).
    + exact Hnegq.
Qed.

Lemma amt_positive_and_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_positive M (And p q) <->
    amt_positive M p /\ amt_positive M q.
Proof. intros; apply gmct_and_iff. Qed.

Lemma amt_negative_and_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_negative M (And p q) <->
    amt_negative M p \/ amt_negative M q.
Proof.
  intros AtomType L M p q; split.
  - intro Hnegand. destruct (amt_saturated M p) as [Hp | Hnegp].
    + destruct (amt_saturated M q) as [Hq | Hnegq]; [|now right].
      exfalso. apply (@amt_neither AtomType L M (And p q)).
      split; [apply (proj2 (gmct_and_iff (anmct_generic M) p q)); now split
             | exact Hnegand].
    + now left.
  - intros [Hnegp | Hnegq].
    + apply (proj1 (amt_not_positive_iff_negative M (And p q))).
      intro Hand. apply (@amt_neither AtomType L M p).
      split; [exact (proj1 (proj1
        (gmct_and_iff (anmct_generic M) p q) Hand))
             | exact Hnegp].
    + apply (proj1 (amt_not_positive_iff_negative M (And p q))).
      intro Hand. apply (@amt_neither AtomType L M q).
      split; [exact (proj2 (proj1
        (gmct_and_iff (anmct_generic M) p q) Hand))
             | exact Hnegq].
Qed.

Lemma amt_positive_or_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_positive M (Or p q) <->
    amt_positive M p \/ amt_positive M q.
Proof. intros; apply gmct_or_iff. Qed.

Lemma amt_negative_or_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_negative M (Or p q) <->
    amt_negative M p /\ amt_negative M q.
Proof.
  intros AtomType L M p q; split.
  - intro Hnegor. split.
    + apply (proj1 (amt_not_positive_iff_negative M p)). intro Hp.
      apply (@amt_neither AtomType L M (Or p q)). split.
      * apply (proj2 (gmct_or_iff (anmct_generic M) p q)). now left.
      * exact Hnegor.
    + apply (proj1 (amt_not_positive_iff_negative M q)). intro Hq.
      apply (@amt_neither AtomType L M (Or p q)). split.
      * apply (proj2 (gmct_or_iff (anmct_generic M) p q)). now right.
      * exact Hnegor.
  - intros [Hnegp Hnegq].
    apply (proj1 (amt_not_positive_iff_negative M (Or p q))).
    intro Hor. destruct (proj1 (gmct_or_iff (anmct_generic M) p q) Hor)
      as [Hp | Hq].
    + exact (@amt_neither AtomType L M p (conj Hp Hnegp)).
    + exact (@amt_neither AtomType L M q (conj Hq Hnegq)).
Qed.

Lemma amt_positive_mdp :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_positive M (Imp p q) -> amt_positive M p -> amt_positive M q.
Proof. intros; eapply gmct_mdp; eauto. Qed.

Lemma amt_negative_contravariant_mdp :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) p q,
    amt_positive M (Imp p q) -> amt_negative M q -> amt_negative M p.
Proof.
  intros AtomType L M p q Himp Hnq.
  apply (proj1 (amt_not_positive_iff_negative M p)). intro Hp.
  apply (proj2 (amt_not_positive_iff_negative M q) Hnq).
  exact (amt_positive_mdp Himp Hp).
Qed.

Lemma amt_positive_list_conj_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) Gamma,
    amt_positive M (logic_list_conj2 Gamma) <->
    forall p, In p Gamma -> amt_positive M p.
Proof. intros; apply gmct_list_conj2_members_iff. Qed.

Lemma amt_negative_list_conj_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) Gamma,
    amt_negative M (logic_list_conj2 Gamma) <->
    Exists (amt_negative M) Gamma.
Proof.
  intros AtomType L M Gamma. induction Gamma as [|p Gamma IH].
  - simpl. split.
    + intro H. exfalso.
      exact (@amt_negative_top_absent AtomType L M H).
    + intro H. inversion H.
  - destruct Gamma as [|q Gamma].
    + simpl. split; intro H.
      * now constructor.
      * inversion H; subst; [assumption | inversion H1].
    + simpl in IH |- *. rewrite amt_negative_and_iff, IH.
      split.
      * intros [Hp | Hrest]; [now constructor | now right].
      * intro H. inversion H; subst; [now left | now right].
Qed.

Lemma amt_positive_list_disj_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) Gamma,
    amt_positive M (logic_list_disj2 Gamma) <->
    Exists (amt_positive M) Gamma.
Proof. intros; apply gmct_list_disj2_iff. Qed.

Lemma amt_negative_list_disj_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_maximal_tableau AtomType L) Gamma,
    amt_negative M (logic_list_disj2 Gamma) <->
    forall p, In p Gamma -> amt_negative M p.
Proof.
  intros AtomType L M Gamma.
  unfold amt_negative, anmct_mem. split.
  - intros Hneg p Hp.
    apply (proj2 (gmct_neg_iff (anmct_generic M) p)). intro Hpos.
    apply (proj1 (gmct_neg_iff (anmct_generic M)
      (logic_list_disj2 Gamma)) Hneg).
    apply (proj2 (gmct_list_disj2_iff (anmct_generic M) Gamma)).
    apply Exists_exists. now exists p.
  - intro Hall.
    apply (proj2 (gmct_neg_iff (anmct_generic M)
      (logic_list_disj2 Gamma))). intro Hdisj.
    apply (proj1 (gmct_list_disj2_iff (anmct_generic M) Gamma)) in Hdisj.
    apply Exists_exists in Hdisj as [p [Hp Hpos]].
    exact (proj1 (gmct_neg_iff (anmct_generic M) p)
      (Hall p Hp) Hpos).
Qed.

(** * Modal saturation laws *)

Definition amt_relation_iter {AtomType L} (n : nat)
    (M N : abstract_maximal_tableau AtomType L) : Prop :=
  abstract_canonical_relation_iter n M N.

Definition amt_relation {AtomType L}
    (M N : abstract_maximal_tableau AtomType L) : Prop :=
  abstract_canonical_relation M N.

Lemma amt_positive_box_iter_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_maximal_tableau AtomType L) p,
    amt_positive M (box_iter n p) <->
    forall N, amt_relation_iter n M N -> amt_positive N p.
Proof. intros; apply anmct_box_iter_relation_iff; assumption. Qed.

Lemma amt_negative_box_iter_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_maximal_tableau AtomType L) p,
    amt_negative M (box_iter n p) <->
    exists N, amt_relation_iter n M N /\ amt_negative N p.
Proof.
  intros AtomType L Hnormal n M p; split.
  - apply abstract_canonical_successor_of_neg_box_iter; exact Hnormal.
  - intros [N [Hrel Hnegp]].
    apply (proj1 (amt_not_positive_iff_negative M (box_iter n p))).
    intro Hbox. apply (proj2 (amt_not_positive_iff_negative N p) Hnegp).
    exact (Hrel p Hbox).
Qed.

Lemma amt_positive_dia_iter_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_maximal_tableau AtomType L) p,
    amt_positive M (dia_iter n p) <->
    exists N, amt_relation_iter n M N /\ amt_positive N p.
Proof. intros; apply anmct_dia_iter_relation_iff; assumption. Qed.

Lemma amt_negative_dia_iter_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_maximal_tableau AtomType L) p,
    amt_negative M (dia_iter n p) <->
    forall N, amt_relation_iter n M N -> amt_negative N p.
Proof.
  intros AtomType L Hnormal n M p; split.
  - intros Hnegdia N Hrel.
    apply (proj1 (@abstract_canonical_relation_iter_iff_neg_dia_iter
      AtomType L Hnormal n M N) Hrel p Hnegdia).
  - intro Hall.
    apply (proj1 (amt_not_positive_iff_negative M (dia_iter n p))).
    intro Hdia.
    destruct (proj1 (@anmct_dia_iter_relation_iff
      AtomType L Hnormal n M p) Hdia) as [N [Hrel Hp]].
    exact (proj2 (amt_not_positive_iff_negative N p)
      (Hall N Hrel) Hp).
Qed.

Corollary amt_positive_box_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_maximal_tableau AtomType L) p,
    amt_positive M (Box p) <->
    forall N, amt_relation M N -> amt_positive N p.
Proof.
  intros AtomType L Hnormal M p.
  exact (@amt_positive_box_iter_iff AtomType L Hnormal 1 M p).
Qed.

Corollary amt_negative_box_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_maximal_tableau AtomType L) p,
    amt_negative M (Box p) <->
    exists N, amt_relation M N /\ amt_negative N p.
Proof.
  intros AtomType L Hnormal M p.
  exact (@amt_negative_box_iter_iff AtomType L Hnormal 1 M p).
Qed.

Corollary amt_positive_dia_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_maximal_tableau AtomType L) p,
    amt_positive M (Dia p) <->
    exists N, amt_relation M N /\ amt_positive N p.
Proof.
  intros AtomType L Hnormal M p.
  exact (@amt_positive_dia_iter_iff AtomType L Hnormal 1 M p).
Qed.

Corollary amt_negative_dia_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_maximal_tableau AtomType L) p,
    amt_negative M (Dia p) <->
    forall N, amt_relation M N -> amt_negative N p.
Proof.
  intros AtomType L Hnormal M p.
  exact (@amt_negative_dia_iter_iff AtomType L Hnormal 1 M p).
Qed.

Lemma amt_positive_difference_of_neq :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M N : abstract_maximal_tableau AtomType L),
    M <> N -> exists p, amt_positive M p /\ amt_negative N p.
Proof.
  intros AtomType L M N Hneq.
  apply NNPP. intro Hnone. apply Hneq, amt_positive_extensional.
  intro p; split; intro Hp.
  - destruct (amt_saturated N p) as [HN | HnegN]; [exact HN |].
    exfalso. apply Hnone. exists p. now split.
  - destruct (amt_saturated M p) as [HM | HnegM]; [exact HM |].
    exfalso. apply Hnone. exists (Neg p). split.
    + exact HnegM.
    + apply (proj2 (amt_negative_neg_iff N p)). exact Hp.
Qed.

Lemma amt_negative_difference_of_neq :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M N : abstract_maximal_tableau AtomType L),
    M <> N -> exists p, amt_negative M p /\ amt_positive N p.
Proof.
  intros AtomType L M N Hneq.
  assert (Hnm : N <> M).
  { intro Heq. apply Hneq. now symmetry. }
  destruct (@amt_positive_difference_of_neq AtomType L N M Hnm)
    as [p [Hp Hn]].
  exists p. now split.
Qed.
