(** Atom-polymorphic canonical worlds for abstract normal modal logics.

    The enumerative canonical models in the modal port use [nat] atoms.
    Foundation's maximal-consistency API is polymorphic in the atom type.
    Combining the predicate-theory Lindenbaum theorem with the generic
    maximal-theory laws recovers that generality without an enumeration or
    decidable equality. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  Syntax LogicInfrastructure EntailmentExtensions MaximalTheoryLaws.
From Foundation.Modal Require Import MaximalConsistentSet.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record abstract_normal_mct (AtomType : Type)
    (L : modal_logic_set AtomType) : Type := {
  anmct_generic : generic_maximal_classical_theory AtomType;
  anmct_context_consistent_field :
    abstract_context_consistent L (gmct_mem anmct_generic);
  anmct_derivable_iff_field : forall p,
    abstract_context_derives L (gmct_mem anmct_generic) p <->
    gmct_mem anmct_generic p
}.

Arguments abstract_normal_mct (AtomType) L : clear implicits.
Arguments anmct_generic {AtomType L} _.
Arguments anmct_context_consistent_field {AtomType L} _.
Arguments anmct_derivable_iff_field {AtomType L} _ p.

Definition anmct_mem {AtomType L}
    (M : abstract_normal_mct AtomType L) : abstract_formula_theory AtomType :=
  gmct_mem (anmct_generic M).

Arguments anmct_mem {AtomType L} M p.

Lemma anmct_context_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_normal_mct AtomType L),
    abstract_context_consistent L (anmct_mem M).
Proof. intros AtomType L M; exact (anmct_context_consistent_field M). Qed.

Lemma anmct_derivable_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_normal_mct AtomType L) p,
    abstract_context_derives L (anmct_mem M) p <-> anmct_mem M p.
Proof. intros AtomType L M p; exact (anmct_derivable_iff_field M p). Qed.

Lemma anmct_theorem_mem :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
    (M : abstract_normal_mct AtomType L) p,
    L p -> anmct_mem M p.
Proof.
  intros AtomType L M p Hp. apply (proj1 (anmct_derivable_iff M p)).
  now apply ACD_theorem.
Qed.

Theorem abstract_normal_lindenbaum_extension :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall Gamma,
    abstract_context_consistent L Gamma ->
    exists M : abstract_normal_mct AtomType L,
      abstract_theory_included Gamma (anmct_mem M).
Proof.
  intros AtomType L Hnormal Gamma Hconsistent.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  destruct (abstract_lindenbaum_extension Hclass Gamma Hconsistent)
    as [G [Hinclude [HGconsistent [Hderive _]]]].
  exists {| anmct_generic := G;
            anmct_context_consistent_field := HGconsistent;
            anmct_derivable_iff_field := Hderive |}.
  exact Hinclude.
Qed.

(** Formula preservation along the exact-[n] canonical relation. *)
Definition abstract_canonical_relation_iter {AtomType L} (n : nat)
    (M N : abstract_normal_mct AtomType L) : Prop :=
  forall p, anmct_mem M (box_iter n p) -> anmct_mem N p.

Definition abstract_canonical_relation {AtomType L}
    (M N : abstract_normal_mct AtomType L) : Prop :=
  abstract_canonical_relation_iter 1 M N.

Lemma abstract_context_derives_box_iter_from_preboxed :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n Gamma p,
    abstract_context_derives L (fun q => Gamma (box_iter n q)) p ->
    abstract_context_derives L Gamma (box_iter n p).
Proof.
  intros AtomType L Hnormal n Gamma p Hp.
  pose proof (k_entailment_of_normal_logic Hnormal) as HK.
  induction Hp as [p Hp | p Hp | p q Hpq IHpq Hp IHp].
  - now apply ACD_assumption.
  - apply ACD_theorem. exact (k_multinecessitation HK n Hp).
  - eapply ACD_mp; [|exact IHp]. eapply ACD_mp; [|exact IHpq].
    apply ACD_theorem. exact (k_box_iter_axiom_K HK n p q).
Qed.

(** A negated iterated box has a canonical successor carrying the negated
    body.  This is the central modal use of Lindenbaum. *)
Theorem abstract_canonical_successor_of_neg_box_iter :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (Neg (box_iter n p)) ->
    exists N : abstract_normal_mct AtomType L,
      abstract_canonical_relation_iter n M N /\ anmct_mem N (Neg p).
Proof.
  intros AtomType L Hnormal n M p Hnegbox.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  pose (Gamma := abstract_theory_insert
    (fun q => anmct_mem M (box_iter n q)) (Neg p)).
  assert (Hconsistent : abstract_context_consistent L Gamma).
  { unfold Gamma. apply (proj2
      (abstract_insert_neg_consistent_iff Hclass
        (fun q => anmct_mem M (box_iter n q)) p)).
    intro Hp.
    pose proof (abstract_context_derives_box_iter_from_preboxed
      Hnormal Hp) as Hboxed.
    pose proof (proj1 (anmct_derivable_iff M (box_iter n p)) Hboxed)
      as Hboxedmem.
    exact (@gmct_not_both AtomType (anmct_generic M)
      (box_iter n p) Hboxedmem Hnegbox). }
  destruct (abstract_normal_lindenbaum_extension Hnormal Hconsistent)
    as [N Hinclude].
  exists N. split.
  - intros q Hbox. apply Hinclude. now right.
  - apply Hinclude. now left.
Qed.

Corollary abstract_canonical_successor_of_neg_box :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (Neg (Box p)) ->
    exists N : abstract_normal_mct AtomType L,
      abstract_canonical_relation M N /\ anmct_mem N (Neg p).
Proof.
  intros AtomType L Hnormal M p.
  exact (@abstract_canonical_successor_of_neg_box_iter
    AtomType L Hnormal 1 M p).
Qed.

Theorem anmct_box_iter_relation_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (box_iter n p) <->
    forall N, abstract_canonical_relation_iter n M N -> anmct_mem N p.
Proof.
  intros AtomType L Hnormal n M p; split.
  - intros Hbox N Hrel. exact (Hrel p Hbox).
  - intro Hall.
    destruct (gmct_complete (anmct_generic M) (box_iter n p))
      as [Hbox | Hnegbox]; [exact Hbox |].
    destruct (@abstract_canonical_successor_of_neg_box_iter
      AtomType L Hnormal n M p Hnegbox) as [N [Hrel Hnegp]].
    exfalso. exact (@gmct_not_both AtomType (anmct_generic N) p
      (Hall N Hrel) Hnegp).
Qed.

Corollary anmct_box_relation_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (Box p) <->
    forall N, abstract_canonical_relation M N -> anmct_mem N p.
Proof.
  intros AtomType L Hnormal M p.
  exact (@anmct_box_iter_relation_iff AtomType L Hnormal 1 M p).
Qed.

Lemma anmct_box_iter_negneg_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (box_iter n (Neg (Neg p))) <->
    anmct_mem M (box_iter n p).
Proof.
  intros AtomType L Hnormal n M p.
  rewrite !(@anmct_box_iter_relation_iff AtomType L Hnormal n M).
  split; intros H N Hrel.
  - apply (proj1 (gmct_negneg_iff (anmct_generic N) p)). now apply H.
  - apply (proj2 (gmct_negneg_iff (anmct_generic N) p)). now apply H.
Qed.

Corollary anmct_box_negneg_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (Box (Neg (Neg p))) <-> anmct_mem M (Box p).
Proof.
  intros AtomType L Hnormal M p.
  exact (@anmct_box_iter_negneg_iff AtomType L Hnormal 1 M p).
Qed.

Lemma anmct_box_iter_dual :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (box_iter n p) <->
    anmct_mem M (Neg (dia_iter n (Neg p))).
Proof.
  intros AtomType L Hnormal n M p.
  pose proof (e_entailment_of_k
    (k_entailment_of_normal_logic Hnormal)) as HE.
  split; intro Hmem.
  - eapply gmct_mdp; [|exact Hmem]. apply anmct_theorem_mem.
    exact (boxItrDuality_mp HE n p).
  - eapply gmct_mdp; [|exact Hmem]. apply anmct_theorem_mem.
    exact (boxItrDuality_mpr HE n p).
Qed.

Corollary anmct_box_dual :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (Box p) <-> anmct_mem M (Neg (Dia (Neg p))).
Proof.
  intros AtomType L Hnormal M p.
  exact (@anmct_box_iter_dual AtomType L Hnormal 1 M p).
Qed.

Lemma anmct_dia_iter_dual :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (dia_iter n p) <->
    anmct_mem M (Neg (box_iter n (Neg p))).
Proof.
  intros AtomType L Hnormal n M p.
  pose proof (e_entailment_of_k
    (k_entailment_of_normal_logic Hnormal)) as HE.
  split; intro Hmem.
  - eapply gmct_mdp; [|exact Hmem]. apply anmct_theorem_mem.
    exact (diaItrDuality_mp HE n p).
  - eapply gmct_mdp; [|exact Hmem]. apply anmct_theorem_mem.
    exact (diaItrDuality_mpr HE n p).
Qed.

Corollary anmct_dia_dual :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (Dia p) <-> anmct_mem M (Neg (Box (Neg p))).
Proof.
  intros AtomType L Hnormal M p.
  exact (@anmct_dia_iter_dual AtomType L Hnormal 1 M p).
Qed.

Theorem anmct_dia_iter_relation_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (dia_iter n p) <->
    exists N, abstract_canonical_relation_iter n M N /\ anmct_mem N p.
Proof.
  intros AtomType L Hnormal n M p; split.
  - intro Hdia.
    pose proof (proj1 (@anmct_dia_iter_dual
      AtomType L Hnormal n M p) Hdia)
      as Hnegbox.
    destruct (@abstract_canonical_successor_of_neg_box_iter
      AtomType L Hnormal n M (Neg p) Hnegbox) as [N [Hrel Hnegneg]].
    exists N. split; [exact Hrel |].
    exact (proj1 (gmct_negneg_iff (anmct_generic N) p) Hnegneg).
  - intros [N [Hrel Hp]].
    apply (proj2 (@anmct_dia_iter_dual AtomType L Hnormal n M p)).
    apply (proj2 (gmct_neg_iff (anmct_generic M) (box_iter n (Neg p)))).
    intro Hboxneg.
    exact (@gmct_not_both AtomType (anmct_generic N) p Hp
      (Hrel (Neg p) Hboxneg)).
Qed.

Corollary anmct_dia_relation_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_normal_mct AtomType L) p,
    anmct_mem M (Dia p) <->
    exists N, abstract_canonical_relation M N /\ anmct_mem N p.
Proof.
  intros AtomType L Hnormal M p.
  exact (@anmct_dia_iter_relation_iff AtomType L Hnormal 1 M p).
Qed.

Theorem abstract_canonical_relation_iter_iff_dia_iter :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M N : abstract_normal_mct AtomType L),
    abstract_canonical_relation_iter n M N <->
    forall p, anmct_mem N p -> anmct_mem M (dia_iter n p).
Proof.
  intros AtomType L Hnormal n M N; split.
  - intros Hrel p Hp. apply (proj2
      (@anmct_dia_iter_relation_iff AtomType L Hnormal n M p)).
    exists N. now split.
  - intros Hdia p Hbox.
    destruct (gmct_complete (anmct_generic N) p) as [Hp | Hnegp];
      [exact Hp |].
    exfalso. exact (@gmct_not_both AtomType (anmct_generic M)
      (dia_iter n (Neg p)) (Hdia (Neg p) Hnegp)
      (proj1 (@anmct_box_iter_dual AtomType L Hnormal n M p) Hbox)).
Qed.

Theorem abstract_canonical_relation_iter_iff_neg_box_iter :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M N : abstract_normal_mct AtomType L),
    abstract_canonical_relation_iter n M N <->
    forall p, anmct_mem N (Neg p) ->
      anmct_mem M (Neg (box_iter n p)).
Proof.
  intros AtomType L Hnormal n M N; split.
  - intros Hrel p Hnegp.
    apply (proj2 (gmct_neg_iff (anmct_generic M) (box_iter n p))).
    intro Hbox. exact (@gmct_not_both AtomType (anmct_generic N) p
      (Hrel p Hbox) Hnegp).
  - intros Hneg p Hbox.
    destruct (gmct_complete (anmct_generic N) p) as [Hp | Hnegp];
      [exact Hp |].
    exfalso. exact (@gmct_not_both AtomType (anmct_generic M)
      (box_iter n p) Hbox (Hneg p Hnegp)).
Qed.

Theorem abstract_canonical_relation_iter_iff_neg_dia_iter :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M N : abstract_normal_mct AtomType L),
    abstract_canonical_relation_iter n M N <->
    forall p, anmct_mem M (Neg (dia_iter n p)) -> anmct_mem N (Neg p).
Proof.
  intros AtomType L Hnormal n M N; split.
  - intros Hrel p Hnegdia.
    apply (proj2 (gmct_neg_iff (anmct_generic N) p)). intro Hp.
    apply (@gmct_not_both AtomType (anmct_generic M) (dia_iter n p)).
    + apply (proj2 (@anmct_dia_iter_relation_iff
        AtomType L Hnormal n M p)).
      exists N. now split.
    + exact Hnegdia.
  - intros Hnegdia p Hbox.
    destruct (gmct_complete (anmct_generic N) p) as [Hp | Hnegp];
      [exact Hp |].
    exfalso. apply (@gmct_not_both AtomType (anmct_generic N) (Neg p)
      Hnegp).
    apply Hnegdia.
    exact (proj1 (@anmct_box_iter_dual
      AtomType L Hnormal n M p) Hbox).
Qed.

Corollary abstract_canonical_relation_iff_dia :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M N : abstract_normal_mct AtomType L),
    abstract_canonical_relation M N <->
    forall p, anmct_mem N p -> anmct_mem M (Dia p).
Proof.
  intros AtomType L Hnormal M N.
  exact (@abstract_canonical_relation_iter_iff_dia_iter
    AtomType L Hnormal 1 M N).
Qed.

Corollary abstract_canonical_relation_iff_neg_box :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M N : abstract_normal_mct AtomType L),
    abstract_canonical_relation M N <->
    forall p, anmct_mem N (Neg p) -> anmct_mem M (Neg (Box p)).
Proof.
  intros AtomType L Hnormal M N.
  exact (@abstract_canonical_relation_iter_iff_neg_box_iter
    AtomType L Hnormal 1 M N).
Qed.

Corollary abstract_canonical_relation_iff_neg_dia :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M N : abstract_normal_mct AtomType L),
    abstract_canonical_relation M N <->
    forall p, anmct_mem M (Neg (Dia p)) -> anmct_mem N (Neg p).
Proof.
  intros AtomType L Hnormal M N.
  exact (@abstract_canonical_relation_iter_iff_neg_dia_iter
    AtomType L Hnormal 1 M N).
Qed.

Lemma anmct_box_iter_list_conj_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall n (M : abstract_normal_mct AtomType L) Gamma,
    anmct_mem M (box_iter n (logic_list_conj Gamma)) <->
    forall p, In p Gamma -> anmct_mem M (box_iter n p).
Proof.
  intros AtomType L Hnormal n M Gamma; split.
  - intros Hconj p Hp.
    apply (proj2 (@anmct_box_iter_relation_iff
      AtomType L Hnormal n M p)).
    intros N Hrel.
    apply (proj1 (gmct_list_conj_members_iff (anmct_generic N) Gamma)).
    + apply (proj1
        (@anmct_box_iter_relation_iff
          AtomType L Hnormal n M (logic_list_conj Gamma))
        Hconj N Hrel).
    + exact Hp.
  - intro Hall.
    apply (proj2
      (@anmct_box_iter_relation_iff
        AtomType L Hnormal n M (logic_list_conj Gamma))).
    intros N Hrel.
    apply (proj2 (gmct_list_conj_members_iff (anmct_generic N) Gamma)).
    intros p Hp.
    apply (proj1 (@anmct_box_iter_relation_iff
      AtomType L Hnormal n M p)
      (Hall p Hp) N Hrel).
Qed.

Corollary anmct_box_list_conj_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    normal_logic L -> forall (M : abstract_normal_mct AtomType L) Gamma,
    anmct_mem M (Box (logic_list_conj Gamma)) <->
    forall p, In p Gamma -> anmct_mem M (Box p).
Proof.
  intros AtomType L Hnormal M Gamma.
  exact (@anmct_box_iter_list_conj_iff
    AtomType L Hnormal 1 M Gamma).
Qed.
