(** Iterated canonical-relation laws for maximal normal theories.

    [CanonicalK4n] proves the hard bridge: an exact length-[n] canonical path
    is equivalent to preservation of every [box_iter n] formula.  This module
    derives the source-facing positive, negative, and semantic presentations
    from that one theorem and the factored maximal-theory algebra. *)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Kripke NormalHilbert LogicInfrastructure CanonicalExtensions KripkeSemantics
  MaximalTheoryLaws CanonicalK4n.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The one-sided canonical truth lemma contains the source's two-sided
    statement: membership on the negative side is membership of syntactic
    negation. *)
Lemma normal_canonical_truth_neg_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Neg p) <->
    ~ satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        M p.
Proof.
  intros Ax M p. rewrite normal_mct_neg_iff.
  now rewrite normal_canonical_truth_lemma.
Qed.

Theorem normal_canonical_truth_pair :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    (normal_mct_mem M p <->
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        M p) /\
    (normal_mct_mem M (Neg p) <->
      ~ satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        M p).
Proof.
  intros Ax M p; split.
  - apply normal_canonical_truth_lemma.
  - apply normal_canonical_truth_neg_iff.
Qed.

Theorem normal_canonical_model_valid_iff_provable :
  forall Ax, normal_system_consistent Ax -> forall p,
    model_valid (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) p <-> normal_proves Ax p.
Proof.
  intros Ax Hconsistent p; split.
  - intro Hvalid. apply NNPP. intro Hnot.
    destruct (@normal_canonical_countermodel Ax Hconsistent p Hnot)
      as [M Hcounter]. exact (Hcounter (Hvalid M)).
  - intros Hproof M.
    apply (proj1 (@normal_canonical_truth_lemma Ax p M)).
    apply normal_mct_derivable_mem, ND_theorem. exact Hproof.
Qed.

(** Membership of one iterated box is universal truth at exact-length
    canonical successors. *)
Theorem normal_mct_box_iter_rel_iff :
  forall Ax n (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (box_iter n p) <->
    forall N, rel_iter (@normal_canonical_relation Ax) n M N ->
      normal_mct_mem N p.
Proof.
  intros Ax n M p; split.
  - intros Hbox N Hrel.
    apply (proj2 (@normal_canonical_truth_lemma Ax p N)).
    apply (proj1 (@satisfies_box_iter nat (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) n M p)).
    + now apply (proj1 (@normal_canonical_truth_lemma Ax (box_iter n p) M)).
    + exact Hrel.
  - intro Hall. apply (proj2 (@normal_canonical_truth_lemma Ax
      (box_iter n p) M)).
    apply (proj2 (@satisfies_box_iter nat (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) n M p)).
    intros N Hrel.
    apply (proj1 (@normal_canonical_truth_lemma Ax p N)).
    now apply Hall.
Qed.

Corollary normal_mct_box_rel_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Box p) <->
    forall N, @normal_canonical_relation Ax M N -> normal_mct_mem N p.
Proof.
  intros Ax M p. change
    (normal_mct_mem M (box_iter 1 p) <->
     forall N, @normal_canonical_relation Ax M N -> normal_mct_mem N p).
  rewrite normal_mct_box_iter_rel_iff. split; intros H N Hrel.
  - apply H. now apply (proj2 (rel_iter_one _ _ _)).
  - apply H. now apply (proj1 (rel_iter_one _ _ _)).
Qed.

Lemma normal_mct_box_iter_negneg_iff :
  forall Ax n (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (box_iter n (Neg (Neg p))) <->
    normal_mct_mem M (box_iter n p).
Proof.
  intros Ax n M p.
  rewrite !normal_mct_box_iter_rel_iff.
  split; intros H N Hrel.
  - apply (proj1 (@normal_mct_negneg_iff Ax N p)). now apply H.
  - apply (proj2 (@normal_mct_negneg_iff Ax N p)). now apply H.
Qed.

Corollary normal_mct_box_negneg_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Box (Neg (Neg p))) <-> normal_mct_mem M (Box p).
Proof. intros Ax M p; exact (@normal_mct_box_iter_negneg_iff Ax 1 M p). Qed.

(** Syntactic modal dualities read back exactly at maximal theories. *)
Lemma normal_mct_box_iter_dual :
  forall Ax n (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (box_iter n p) <->
    normal_mct_mem M (Neg (dia_iter n (Neg p))).
Proof.
  intros Ax n M p.
  rewrite !normal_canonical_truth_lemma.
  apply kripke_box_iter_dual.
Qed.

Corollary normal_mct_box_dual :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Box p) <->
    normal_mct_mem M (Neg (Dia (Neg p))).
Proof. intros Ax M p; exact (@normal_mct_box_iter_dual Ax 1 M p). Qed.

Lemma normal_mct_dia_iter_dual :
  forall Ax n (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (dia_iter n p) <->
    normal_mct_mem M (Neg (box_iter n (Neg p))).
Proof.
  intros Ax n M p.
  rewrite !normal_canonical_truth_lemma.
  apply kripke_dia_iter_dual.
Qed.

Corollary normal_mct_dia_dual :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Dia p) <->
    normal_mct_mem M (Neg (Box (Neg p))).
Proof. intros Ax M p; exact (@normal_mct_dia_iter_dual Ax 1 M p). Qed.

(** Diamond membership is an existential exact-length canonical successor. *)
Theorem normal_mct_dia_iter_rel_iff :
  forall Ax n (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (dia_iter n p) <->
    exists N, rel_iter (@normal_canonical_relation Ax) n M N /\
      normal_mct_mem N p.
Proof.
  intros Ax n M p; split.
  - intro Hdia.
    apply (proj1 (@normal_canonical_truth_lemma Ax (dia_iter n p) M)) in Hdia.
    apply (proj1 (@satisfies_dia_iter nat (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) n M p)) in Hdia.
    destruct Hdia as [N [Hrel Hsat]]. exists N. split; [exact Hrel |].
    now apply (proj2 (@normal_canonical_truth_lemma Ax p N)).
  - intros [N [Hrel Hp]].
    apply (proj2 (@normal_canonical_truth_lemma Ax (dia_iter n p) M)).
    apply (proj2 (@satisfies_dia_iter nat (normal_canonical_frame Ax)
      (@normal_canonical_valuation Ax) n M p)).
    exists N. split; [exact Hrel |].
    now apply (proj1 (@normal_canonical_truth_lemma Ax p N)).
Qed.

Corollary normal_mct_dia_rel_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Dia p) <->
    exists N, @normal_canonical_relation Ax M N /\ normal_mct_mem N p.
Proof.
  intros Ax M p. change
    (normal_mct_mem M (dia_iter 1 p) <->
     exists N, @normal_canonical_relation Ax M N /\ normal_mct_mem N p).
  rewrite normal_mct_dia_iter_rel_iff. split.
  - intros [N [Hrel Hp]]. exists N. split; [|exact Hp].
    now apply (proj1 (rel_iter_one _ _ _)).
  - intros [N [Hrel Hp]]. exists N. split; [|exact Hp].
    now apply (proj2 (rel_iter_one _ _ _)).
Qed.

(** Exact-length accessibility in the positive box and diamond
    presentations. *)
Theorem normal_canonical_rel_iter_iff_dia_iter :
  forall Ax n (M N : normal_maximal_consistent_theory Ax),
    rel_iter (@normal_canonical_relation Ax) n M N <->
    forall p, normal_mct_mem N p -> normal_mct_mem M (dia_iter n p).
Proof.
  intros Ax n M N; split.
  - intros Hrel p Hp. apply (proj2 (@normal_mct_dia_iter_rel_iff Ax n M p)).
    exists N. now split.
  - intro Hdia.
    apply (proj2 (@normal_canonical_rel_iter_iff_box_iter Ax n M N)).
    intros p Hbox. destruct (@normal_mct_complete Ax N p) as [Hp | Hneg].
    + exact Hp.
    + exfalso. apply (@normal_mct_not_both Ax M (dia_iter n (Neg p))).
      * exact (Hdia (Neg p) Hneg).
      * apply (proj1 (@normal_mct_box_iter_dual Ax n M p)). exact Hbox.
Qed.

(** The negative box-side presentation corresponding to the second side of
    Foundation's two-sided tableaux. *)
Theorem normal_canonical_rel_iter_iff_neg_box_iter :
  forall Ax n (M N : normal_maximal_consistent_theory Ax),
    rel_iter (@normal_canonical_relation Ax) n M N <->
    forall p, normal_mct_mem N (Neg p) ->
      normal_mct_mem M (Neg (box_iter n p)).
Proof.
  intros Ax n M N; split.
  - intros Hrel p Hnegp.
    apply (proj2 (@normal_mct_neg_iff Ax M (box_iter n p))). intro Hbox.
    apply (@normal_mct_not_both Ax N p).
    + exact (proj1 (@normal_canonical_rel_iter_iff_box_iter Ax n M N)
        Hrel p Hbox).
    + exact Hnegp.
  - intro Hneg.
    apply (proj2 (@normal_canonical_rel_iter_iff_box_iter Ax n M N)).
    intros p Hbox. destruct (@normal_mct_complete Ax N p) as [Hp | Hnegp].
    + exact Hp.
    + exfalso. exact (@normal_mct_not_both Ax M (box_iter n p)
        Hbox (Hneg p Hnegp)).
Qed.

(** The negative diamond-side presentation. *)
Theorem normal_canonical_rel_iter_iff_neg_dia_iter :
  forall Ax n (M N : normal_maximal_consistent_theory Ax),
    rel_iter (@normal_canonical_relation Ax) n M N <->
    forall p, normal_mct_mem M (Neg (dia_iter n p)) ->
      normal_mct_mem N (Neg p).
Proof.
  intros Ax n M N; split.
  - intros Hrel p Hnegdia.
    apply (proj2 (@normal_mct_neg_iff Ax N p)). intro Hp.
    apply (@normal_mct_not_both Ax M (dia_iter n p)).
    + apply (proj2 (@normal_mct_dia_iter_rel_iff Ax n M p)).
      exists N. now split.
    + exact Hnegdia.
  - intro Hnegdia.
    apply (proj2 (@normal_canonical_rel_iter_iff_box_iter Ax n M N)).
    intros p Hbox. destruct (@normal_mct_complete Ax N p) as [Hp | Hnegp].
    + exact Hp.
    + exfalso. apply (@normal_mct_not_both Ax N (Neg p) Hnegp).
      apply Hnegdia.
      apply (proj1 (@normal_mct_box_iter_dual Ax n M p)). exact Hbox.
Qed.

(** One-step aliases matching the source relation API. *)
Corollary normal_canonical_relation_iff_box_mem :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    @normal_canonical_relation Ax M N <->
    forall p, normal_mct_mem M (Box p) -> normal_mct_mem N p.
Proof.
  intros Ax M N.
  rewrite <- (rel_iter_one (@normal_canonical_relation Ax) M N).
  exact (@normal_canonical_rel_iter_iff_box_iter Ax 1 M N).
Qed.

Corollary normal_canonical_relation_iff_neg_box_mem :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    @normal_canonical_relation Ax M N <->
    forall p, normal_mct_mem N (Neg p) ->
      normal_mct_mem M (Neg (Box p)).
Proof.
  intros Ax M N.
  rewrite <- (rel_iter_one (@normal_canonical_relation Ax) M N).
  exact (@normal_canonical_rel_iter_iff_neg_box_iter Ax 1 M N).
Qed.

Corollary normal_canonical_relation_iff_dia_mem :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    @normal_canonical_relation Ax M N <->
    forall p, normal_mct_mem N p -> normal_mct_mem M (Dia p).
Proof.
  intros Ax M N.
  rewrite <- (rel_iter_one (@normal_canonical_relation Ax) M N).
  exact (@normal_canonical_rel_iter_iff_dia_iter Ax 1 M N).
Qed.

Corollary normal_canonical_relation_iff_neg_dia_mem :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    @normal_canonical_relation Ax M N <->
    forall p, normal_mct_mem M (Neg (Dia p)) -> normal_mct_mem N (Neg p).
Proof.
  intros Ax M N.
  rewrite <- (rel_iter_one (@normal_canonical_relation Ax) M N).
  exact (@normal_canonical_rel_iter_iff_neg_dia_iter Ax 1 M N).
Qed.

(** Semantic versions of the same exact relation characterizations. *)
Theorem normal_canonical_rel_iter_iff_box_iter_satisfies :
  forall Ax n (M N : normal_maximal_consistent_theory Ax),
    rel_iter (@normal_canonical_relation Ax) n M N <->
    forall p,
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        M (box_iter n p) ->
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        N p.
Proof.
  intros Ax n M N; rewrite normal_canonical_rel_iter_iff_box_iter.
  split; intros H p Hp.
  - apply (proj1 (@normal_canonical_truth_lemma Ax p N)). apply H.
    now apply (proj2 (@normal_canonical_truth_lemma Ax (box_iter n p) M)).
  - apply (proj2 (@normal_canonical_truth_lemma Ax p N)). apply H.
    now apply (proj1 (@normal_canonical_truth_lemma Ax (box_iter n p) M)).
Qed.

Theorem normal_canonical_rel_iter_iff_dia_iter_satisfies :
  forall Ax n (M N : normal_maximal_consistent_theory Ax),
    rel_iter (@normal_canonical_relation Ax) n M N <->
    forall p,
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        N p ->
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        M (dia_iter n p).
Proof.
  intros Ax n M N; rewrite normal_canonical_rel_iter_iff_dia_iter.
  split; intros H p Hp.
  - apply (proj1 (@normal_canonical_truth_lemma Ax (dia_iter n p) M)).
    apply H. now apply (proj2 (@normal_canonical_truth_lemma Ax p N)).
  - apply (proj2 (@normal_canonical_truth_lemma Ax (dia_iter n p) M)).
    apply H. now apply (proj1 (@normal_canonical_truth_lemma Ax p N)).
Qed.

Corollary normal_canonical_relation_iff_box_satisfies :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    @normal_canonical_relation Ax M N <->
    forall p,
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        M (Box p) ->
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        N p.
Proof.
  intros Ax M N.
  rewrite <- (rel_iter_one (@normal_canonical_relation Ax) M N).
  exact (@normal_canonical_rel_iter_iff_box_iter_satisfies Ax 1 M N).
Qed.

Corollary normal_canonical_relation_iff_dia_satisfies :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    @normal_canonical_relation Ax M N <->
    forall p,
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        N p ->
      satisfies (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
        M (Dia p).
Proof.
  intros Ax M N.
  rewrite <- (rel_iter_one (@normal_canonical_relation Ax) M N).
  exact (@normal_canonical_rel_iter_iff_dia_iter_satisfies Ax 1 M N).
Qed.

(** Iterated boxes distribute over both list-conjunction presentations at a
    maximal theory. *)
Theorem normal_mct_box_iter_list_conj_iff :
  forall Ax n (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (box_iter n (logic_list_conj Gamma)) <->
    forall p, In p Gamma -> normal_mct_mem M (box_iter n p).
Proof.
  intros Ax n M Gamma; split.
  - intros H p Hp.
    apply (proj2 (@normal_mct_box_iter_rel_iff Ax n M p)).
    intros N Hrel.
    apply (proj1 (@normal_mct_list_conj_members_iff Ax N Gamma)).
    + apply (proj1 (@normal_mct_box_iter_rel_iff Ax n M
        (logic_list_conj Gamma)) H N Hrel).
    + exact Hp.
  - intro Hall.
    apply (proj2 (@normal_mct_box_iter_rel_iff Ax n M
      (logic_list_conj Gamma))).
    intros N Hrel.
    apply (proj2 (@normal_mct_list_conj_members_iff Ax N Gamma)).
    intros p Hp.
    apply (proj1 (@normal_mct_box_iter_rel_iff Ax n M p)
      (Hall p Hp) N Hrel).
Qed.

Theorem normal_mct_box_iter_list_conj2_iff :
  forall Ax n (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (box_iter n (logic_list_conj2 Gamma)) <->
    forall p, In p Gamma -> normal_mct_mem M (box_iter n p).
Proof.
  intros Ax n M Gamma; split.
  - intros H p Hp.
    apply (proj2 (@normal_mct_box_iter_rel_iff Ax n M p)).
    intros N Hrel.
    apply (proj1 (@normal_mct_list_conj2_members_iff Ax N Gamma)).
    + apply (proj1 (@normal_mct_box_iter_rel_iff Ax n M
        (logic_list_conj2 Gamma)) H N Hrel).
    + exact Hp.
  - intro Hall.
    apply (proj2 (@normal_mct_box_iter_rel_iff Ax n M
      (logic_list_conj2 Gamma))).
    intros N Hrel.
    apply (proj2 (@normal_mct_list_conj2_members_iff Ax N Gamma)).
    intros p Hp.
    apply (proj1 (@normal_mct_box_iter_rel_iff Ax n M p)
      (Hall p Hp) N Hrel).
Qed.

Corollary normal_mct_box_list_conj_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (Box (logic_list_conj Gamma)) <->
    forall p, In p Gamma -> normal_mct_mem M (Box p).
Proof. intros Ax M Gamma; exact (@normal_mct_box_iter_list_conj_iff Ax 1 M Gamma). Qed.

Corollary normal_mct_box_list_conj2_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (Box (logic_list_conj2 Gamma)) <->
    forall p, In p Gamma -> normal_mct_mem M (Box p).
Proof. intros Ax M Gamma; exact (@normal_mct_box_iter_list_conj2_iff Ax 1 M Gamma). Qed.
