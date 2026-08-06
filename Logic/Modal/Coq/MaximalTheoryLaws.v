(** Atom-polymorphic laws of maximal consistent classical theories.

    Foundation/Modal/MaximalConsistentSet.lean combines a Lindenbaum
    construction with a large propositional convenience API.  The latter
    depends only on four pieces of data: a formula predicate, closure under
    classical tautologies and modus ponens, absence of falsity, and a choice
    between every formula and its negation.  Isolating exactly that interface
    makes all algebraic laws independent of atom enumeration, modal axioms,
    necessitation, and the particular Lindenbaum construction. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  Syntax CanonicalK NormalHilbert LogicInfrastructure CanonicalExtensions.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record generic_maximal_classical_theory (AtomType : Type) : Type := {
  gmct_mem : formula AtomType -> Prop;
  gmct_classical : classical_logic gmct_mem;
  gmct_bottom_absent_field : ~ gmct_mem Bottom;
  gmct_complete : forall p, gmct_mem p \/ gmct_mem (Neg p)
}.

Arguments gmct_mem {AtomType} _ _.
Arguments gmct_classical {AtomType} _.
Arguments gmct_bottom_absent_field {AtomType} _.
Arguments gmct_complete {AtomType} _ _.

Lemma gmct_not_both :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p,
    gmct_mem M p -> gmct_mem M (Neg p) -> False.
Proof.
  intros AtomType M p Hp Hneg.
  apply (gmct_bottom_absent_field M).
  exact (logic_modus_ponens (gmct_classical M) Hneg Hp).
Qed.

Lemma gmct_bottom_absent :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType),
    ~ gmct_mem M Bottom.
Proof. intros AtomType M; exact (gmct_bottom_absent_field M). Qed.

Lemma gmct_neg_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p,
    gmct_mem M (Neg p) <-> ~ gmct_mem M p.
Proof.
  intros AtomType M p; split.
  - intros Hneg Hp. exact (@gmct_not_both AtomType M p Hp Hneg).
  - intro Hnot. destruct (gmct_complete M p) as [Hp | Hneg].
    + contradiction.
    + exact Hneg.
Qed.

Lemma gmct_tautology_mem :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p,
    classical_tautology p -> gmct_mem M p.
Proof.
  intros AtomType M p Htaut.
  exact (logic_classical_tautology (gmct_classical M) Htaut).
Qed.

Lemma gmct_top_mem :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType),
    gmct_mem M Top.
Proof.
  intros AtomType M. apply logic_mem_top. exact (gmct_classical M).
Qed.

Lemma gmct_imp_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p q,
    gmct_mem M (Imp p q) <-> (gmct_mem M p -> gmct_mem M q).
Proof.
  intros AtomType M p q; split.
  - intros Himp Hp.
    exact (logic_modus_ponens (gmct_classical M) Himp Hp).
  - intro Hpq. destruct (gmct_complete M p) as [Hp | Hneg].
    + apply (logic_imply_intro (gmct_classical M) p (Hpq Hp)).
    + eapply (logic_modus_ponens (gmct_classical M)); [|exact Hneg].
      apply (logic_classical_tautology (gmct_classical M)).
      intro rho. unfold Neg. simpl. tauto.
Qed.

Lemma gmct_negneg_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p,
    gmct_mem M (Neg (Neg p)) <-> gmct_mem M p.
Proof.
  intros AtomType M p; split.
  - intro Hnn. destruct (gmct_complete M p) as [Hp | Hneg].
    + exact Hp.
    + exfalso. exact (@gmct_not_both AtomType M (Neg p) Hneg Hnn).
  - intro Hp. destruct (gmct_complete M (Neg p)) as [Hneg | Hnn].
    + exfalso. exact (@gmct_not_both AtomType M p Hp Hneg).
    + exact Hnn.
Qed.

Lemma gmct_and_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p q,
    gmct_mem M (And p q) <-> gmct_mem M p /\ gmct_mem M q.
Proof.
  intros AtomType M p q. unfold And. split.
  - intro Hand. split.
    + destruct (gmct_complete M p) as [Hp | Hnegp]; [exact Hp |].
      exfalso. apply (@gmct_not_both AtomType M (Imp p (Neg q))).
      * apply (proj2 (@gmct_imp_iff AtomType M p (Neg q))).
        intro Hp. exfalso.
        exact (@gmct_not_both AtomType M p Hp Hnegp).
      * exact Hand.
    + destruct (gmct_complete M q) as [Hq | Hnegq]; [exact Hq |].
      exfalso. apply (@gmct_not_both AtomType M (Imp p (Neg q))).
      * apply (proj2 (@gmct_imp_iff AtomType M p (Neg q))).
        intros _. exact Hnegq.
      * exact Hand.
  - intros [Hp Hq]. apply (proj2 (gmct_neg_iff M (Imp p (Neg q)))).
    intro Himp. apply (@gmct_not_both AtomType M q Hq).
    exact (proj1 (@gmct_imp_iff AtomType M p (Neg q)) Himp Hp).
Qed.

Lemma gmct_or_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p q,
    gmct_mem M (Or p q) <-> gmct_mem M p \/ gmct_mem M q.
Proof.
  intros AtomType M p q. unfold Or. split.
  - intro Hor. destruct (gmct_complete M p) as [Hp | Hneg].
    + now left.
    + right. exact (proj1 (@gmct_imp_iff AtomType M (Neg p) q) Hor Hneg).
  - intros [Hp | Hq].
    + apply (proj2 (@gmct_imp_iff AtomType M (Neg p) q)).
      intro Hneg. exfalso. exact (@gmct_not_both AtomType M p Hp Hneg).
    + apply (logic_imply_intro (gmct_classical M) (Neg p) Hq).
Qed.

Lemma gmct_iff_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p q,
    gmct_mem M (Iff p q) <-> (gmct_mem M p <-> gmct_mem M q).
Proof.
  intros AtomType M p q. unfold Iff.
  rewrite gmct_and_iff, !gmct_imp_iff. tauto.
Qed.

(** Every maximal theory is a two-valued classical valuation when boxes are
    regarded as propositional letters. *)
Theorem gmct_classical_truth_lemma :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType)
    (p : formula AtomType),
    gmct_mem M p <-> classical_eval (gmct_mem M) p.
Proof.
  intros AtomType M p. induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - reflexivity.
  - split; [apply gmct_bottom_absent | contradiction].
  - rewrite gmct_imp_iff, IHp, IHq. reflexivity.
  - reflexivity.
Qed.

Lemma gmct_mdp :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p q,
    gmct_mem M (Imp p q) -> gmct_mem M p -> gmct_mem M q.
Proof.
  intros AtomType M p q.
  apply (proj1 (@gmct_imp_iff AtomType M p q)).
Qed.

Lemma gmct_iff_congr :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType) p q,
    gmct_mem M (Iff p q) -> (gmct_mem M p <-> gmct_mem M q).
Proof.
  intros AtomType M p q.
  apply (proj1 (@gmct_iff_iff AtomType M p q)).
Qed.

(** One-way inclusion between maximal theories is already extensional
    equivalence.  This is the representation-independent form of Foundation's
    [intro_equality]. *)
Theorem gmct_inclusion_extensional :
  forall (AtomType : Type)
    (M N : generic_maximal_classical_theory AtomType),
    (forall p, gmct_mem M p -> gmct_mem N p) ->
    forall p, gmct_mem M p <-> gmct_mem N p.
Proof.
  intros AtomType M N Hinc p; split; [apply Hinc |].
  intro HpN. destruct (gmct_complete M p) as [HpM | HnegM].
  - exact HpM.
  - exfalso. exact (@gmct_not_both AtomType N p HpN (Hinc _ HnegM)).
Qed.

Lemma gmct_neg_imp :
  forall (AtomType : Type)
    (M N : generic_maximal_classical_theory AtomType) p q,
    (gmct_mem N q -> gmct_mem M p) ->
    gmct_mem M (Neg p) -> gmct_mem N (Neg q).
Proof.
  intros AtomType M N p q H Hnegp.
  apply (proj2 (gmct_neg_iff N q)). intro Hq.
  exact (@gmct_not_both AtomType M p (H Hq) Hnegp).
Qed.

Lemma gmct_neg_congr :
  forall (AtomType : Type)
    (M N : generic_maximal_classical_theory AtomType) p q,
    (gmct_mem M p <-> gmct_mem N q) ->
    (gmct_mem M (Neg p) <-> gmct_mem N (Neg q)).
Proof.
  intros AtomType M N p q H; split.
  - apply gmct_neg_imp. exact (proj2 H).
  - apply gmct_neg_imp. exact (proj1 H).
Qed.

Lemma gmct_list_conj_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType)
    Gamma,
    gmct_mem M (logic_list_conj Gamma) <->
    Forall (gmct_mem M) Gamma.
Proof.
  intros AtomType M Gamma. induction Gamma as [|p Gamma IH].
  - simpl. split; [intro; constructor | intro; apply (@gmct_top_mem AtomType M)].
  - simpl. rewrite gmct_and_iff, IH, Forall_cons_iff. reflexivity.
Qed.

Lemma gmct_list_conj2_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType)
    Gamma,
    gmct_mem M (logic_list_conj2 Gamma) <->
    Forall (gmct_mem M) Gamma.
Proof.
  intros AtomType M Gamma. induction Gamma as [|p Gamma IH].
  - simpl. split; [intro; constructor | intro; apply (@gmct_top_mem AtomType M)].
  - destruct Gamma as [|q Gamma].
    + simpl. split.
      * intro Hp. constructor; [exact Hp | constructor].
      * intro H. inversion H; assumption.
    + simpl in IH |- *. rewrite gmct_and_iff, IH, !Forall_cons_iff.
      tauto.
Qed.

Corollary gmct_list_conj_members_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType)
    Gamma,
    gmct_mem M (logic_list_conj Gamma) <->
    forall p, In p Gamma -> gmct_mem M p.
Proof.
  intros AtomType M Gamma. rewrite gmct_list_conj_iff, Forall_forall.
  reflexivity.
Qed.

Corollary gmct_list_conj2_members_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType)
    Gamma,
    gmct_mem M (logic_list_conj2 Gamma) <->
    forall p, In p Gamma -> gmct_mem M p.
Proof.
  intros AtomType M Gamma. rewrite gmct_list_conj2_iff, Forall_forall.
  reflexivity.
Qed.

Lemma gmct_list_disj2_iff :
  forall (AtomType : Type) (M : generic_maximal_classical_theory AtomType)
    Gamma,
    gmct_mem M (logic_list_disj2 Gamma) <->
    Exists (gmct_mem M) Gamma.
Proof.
  intros AtomType M Gamma. induction Gamma as [|p Gamma IH].
  - simpl. split.
    + intro H. exfalso. exact (@gmct_bottom_absent AtomType M H).
    + intro H. inversion H.
  - destruct Gamma as [|q Gamma].
    + simpl. split.
      * intro Hp. now constructor.
      * intro H. inversion H; subst; [assumption | inversion H1].
    + simpl in IH |- *. rewrite gmct_or_iff, IH.
      split.
      * intros [Hp | Hrest]; [now constructor | now right].
      * intro H. inversion H; subst; [now left | now right].
Qed.

(** * Adapter for the existing normal-schema Lindenbaum construction *)

Definition normal_mct_classical_logic Ax
    (M : normal_maximal_consistent_theory Ax)
    : classical_logic (normal_mct_mem M).
Proof.
  constructor.
  - intros p Htaut. apply normal_mct_derivable_mem. apply ND_theorem.
    apply K_proves_normal, K_complete.
    now apply classical_tautology_valid.
  - intros p q Himp Hp. apply normal_mct_derivable_mem.
    eapply ND_mp; apply ND_assumption; eauto.
Defined.

Definition normal_mct_as_generic Ax
    (M : normal_maximal_consistent_theory Ax)
    : generic_maximal_classical_theory nat :=
  {| gmct_mem := normal_mct_mem M;
     gmct_classical := normal_mct_classical_logic M;
     gmct_bottom_absent_field := @normal_mct_bottom_absent Ax M;
     gmct_complete := @normal_mct_complete Ax M |}.

Arguments normal_mct_as_generic Ax M : clear implicits.

Lemma normal_mct_top_mem :
  forall Ax (M : normal_maximal_consistent_theory Ax),
    normal_mct_mem M Top.
Proof.
  intros Ax M.
  exact (@gmct_top_mem nat (normal_mct_as_generic Ax M)).
Qed.

Lemma normal_mct_negneg_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Neg (Neg p)) <-> normal_mct_mem M p.
Proof.
  intros Ax M p.
  apply (@gmct_negneg_iff nat (normal_mct_as_generic Ax M) p).
Qed.

Lemma normal_mct_and_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p q,
    normal_mct_mem M (And p q) <->
    normal_mct_mem M p /\ normal_mct_mem M q.
Proof.
  intros Ax M p q.
  apply (@gmct_and_iff nat (normal_mct_as_generic Ax M) p q).
Qed.

Lemma normal_mct_or_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p q,
    normal_mct_mem M (Or p q) <->
    normal_mct_mem M p \/ normal_mct_mem M q.
Proof.
  intros Ax M p q.
  apply (@gmct_or_iff nat (normal_mct_as_generic Ax M) p q).
Qed.

Lemma normal_mct_iff_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p q,
    normal_mct_mem M (Iff p q) <->
    (normal_mct_mem M p <-> normal_mct_mem M q).
Proof.
  intros Ax M p q.
  apply (@gmct_iff_iff nat (normal_mct_as_generic Ax M) p q).
Qed.

Lemma normal_mct_list_conj_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (logic_list_conj Gamma) <->
    Forall (normal_mct_mem M) Gamma.
Proof.
  intros Ax M Gamma.
  apply (@gmct_list_conj_iff nat (normal_mct_as_generic Ax M) Gamma).
Qed.

Lemma normal_mct_list_conj2_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (logic_list_conj2 Gamma) <->
    Forall (normal_mct_mem M) Gamma.
Proof.
  intros Ax M Gamma.
  apply (@gmct_list_conj2_iff nat (normal_mct_as_generic Ax M) Gamma).
Qed.

Lemma normal_mct_list_conj_members_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (logic_list_conj Gamma) <->
    forall p, In p Gamma -> normal_mct_mem M p.
Proof.
  intros Ax M Gamma.
  apply (@gmct_list_conj_members_iff nat
    (normal_mct_as_generic Ax M) Gamma).
Qed.

Lemma normal_mct_list_conj2_members_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (logic_list_conj2 Gamma) <->
    forall p, In p Gamma -> normal_mct_mem M p.
Proof.
  intros Ax M Gamma.
  apply (@gmct_list_conj2_members_iff nat
    (normal_mct_as_generic Ax M) Gamma).
Qed.

Lemma normal_mct_list_disj2_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) Gamma,
    normal_mct_mem M (logic_list_disj2 Gamma) <->
    Exists (normal_mct_mem M) Gamma.
Proof.
  intros Ax M Gamma.
  apply (@gmct_list_disj2_iff nat (normal_mct_as_generic Ax M) Gamma).
Qed.
