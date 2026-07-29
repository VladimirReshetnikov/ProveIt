(**
  Boolean soundness and completeness of the classical propositional Hilbert
  system.

  This module ports [Propositional/Boolean/Hilbert.lean].  Instead of porting
  its large two-sided saturated-tableau dependency, it specializes the
  smaller canonical construction already used elsewhere in this Coq port:
  a context derivation admits deduction, an enumerated Lindenbaum chain
  decides every formula consistently, and membership in its limit is exactly
  Boolean truth under the canonical valuation.

  Completeness needs only an explicit executable atom codec, replacing the
  source's separate [Encodable] and decidable-equality premises.  Classical
  logic selects a consistent branch at each stage; no semantic completeness
  axiom is assumed.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.ClassicalDescription Logic.Classical_Prop.
From FoundationModal Require Import
  GenericSemantics GenericCalculus PropositionalFormula PropositionalBoolean
  PropositionalLogic PropositionalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Soundness *)

Lemma ph_cl_proof_sound :
  forall (Atom : Type) (p : pformula Atom),
    ph_hilbert_proof (ph_hilbert_cl Atom) p ->
    forall v : pvaluation Atom, pboolean_eval v p.
Proof.
  intros Atom p d.
  induction d; intro v; simpl in *.
  - destruct p0.
    + unfold ph_axiom_efq. simpl. tauto.
    + unfold ph_axiom_lem. simpl. destruct (classic (pboolean_eval v p)); tauto.
  - exact (IHd1 v (IHd2 v)).
  - unfold ptop. simpl. tauto.
  - unfold ph_axiom_S, generic_axiom_S. simpl. tauto.
  - unfold ph_axiom_K, generic_axiom_K. simpl. tauto.
  - unfold ph_axiom_and1, generic_axiom_and1. simpl. tauto.
  - unfold ph_axiom_and2, generic_axiom_and2. simpl. tauto.
  - unfold ph_axiom_and3, generic_axiom_and3. simpl. tauto.
  - unfold ph_axiom_or1, generic_axiom_or1. simpl. tauto.
  - unfold ph_axiom_or2, generic_axiom_or2. simpl. tauto.
  - unfold ph_axiom_or3, generic_axiom_or3. simpl. tauto.
Qed.

Theorem ph_cl_provable_sound :
  forall (Atom : Type) (p : pformula Atom),
    ph_hilbert_provable (ph_hilbert_cl Atom) p ->
    pformula_is_tautology p.
Proof. intros Atom p [d] v. exact (ph_cl_proof_sound d v). Qed.

Lemma ph_cl_not_provable_of_countervaluation :
  forall (Atom : Type) (p : pformula Atom),
    (exists v : pvaluation Atom, ~ pboolean_eval v p) ->
    ~ ph_hilbert_provable (ph_hilbert_cl Atom) p.
Proof.
  intros Atom p [v Hv] Hp. apply Hv.
  exact (ph_cl_provable_sound Hp v).
Qed.

(** * Context derivations and deduction *)

Definition ph_theory (Atom : Type) : Type := pformula Atom -> Prop.

Definition ph_theory_included {Atom : Type}
    (Gamma Delta : ph_theory Atom) : Prop :=
  forall p, Gamma p -> Delta p.

Definition ph_theory_empty {Atom : Type} : ph_theory Atom := fun _ => False.

Definition ph_theory_insert {Atom : Type}
    (Gamma : ph_theory Atom) (p : pformula Atom) : ph_theory Atom :=
  fun q => q = p \/ Gamma q.

Inductive ph_cl_derives {Atom : Type}
    (Gamma : ph_theory Atom) : pformula Atom -> Type :=
| PCD_assumption : forall p, Gamma p -> ph_cl_derives Gamma p
| PCD_theorem : forall p,
    ph_hilbert_proof (ph_hilbert_cl Atom) p -> ph_cl_derives Gamma p
| PCD_mdp : forall p q,
    ph_cl_derives Gamma (PImp p q) ->
    ph_cl_derives Gamma p -> ph_cl_derives Gamma q.

Arguments PCD_assumption {Atom Gamma p} _.
Arguments PCD_theorem {Atom Gamma p} _.
Arguments PCD_mdp {Atom Gamma p q} _ _.

Definition ph_theory_consistent {Atom : Type}
    (Gamma : ph_theory Atom) : Prop :=
  ~ inhabited (ph_cl_derives Gamma PFalsum).

Fixpoint ph_cl_derives_weaken {Atom : Type}
    {Gamma Delta : ph_theory Atom}
    (incl : ph_theory_included Gamma Delta)
    {p : pformula Atom} (d : ph_cl_derives Gamma p) :
    ph_cl_derives Delta p :=
  match d with
  | PCD_assumption h => PCD_assumption (incl _ h)
  | PCD_theorem b => PCD_theorem b
  | PCD_mdp dpq dp =>
      PCD_mdp (ph_cl_derives_weaken incl dpq)
              (ph_cl_derives_weaken incl dp)
  end.

Definition ph_cl_derives_cast {Atom : Type} {Gamma : ph_theory Atom}
    {p q : pformula Atom} (d : ph_cl_derives Gamma p) (e : p = q) :
    ph_cl_derives Gamma q :=
  match e with eq_refl => d end.

(** Turn propositional insert membership into data once.  This is the exact
    Prop-to-Type boundary needed by the raw deduction recursor. *)
Definition ph_theory_insert_member_split {Atom : Type}
    (Gamma : ph_theory Atom) (a q : pformula Atom)
    (h : ph_theory_insert Gamma a q) : {q = a} + {Gamma q}.
Proof.
  destruct (excluded_middle_informative (q = a)) as [e | ne].
  - now left.
  - right. assert (Hq : Gamma q).
    { destruct h as [e | Hq]; [contradiction | exact Hq]. }
    exact Hq.
Defined.

Fixpoint ph_cl_derives_deduction {Atom : Type}
    (Gamma : ph_theory Atom) (a p : pformula Atom)
    (d : ph_cl_derives (ph_theory_insert Gamma a) p) :
    ph_cl_derives Gamma (PImp a p) :=
  match d with
  | @PCD_assumption _ _ q h =>
      match @ph_theory_insert_member_split Atom Gamma a q h with
      | left e =>
          ph_cl_derives_cast
            (PCD_theorem (ph_hilbert_identity (ph_hilbert_cl Atom) a))
            (f_equal (PImp a) (eq_sym e))
      | right hGamma =>
          PCD_mdp
            (PCD_theorem (PHPImplyK q a))
            (PCD_assumption hGamma)
      end
  | @PCD_theorem _ _ q b =>
      PCD_mdp (PCD_theorem (PHPImplyK q a)) (PCD_theorem b)
  | @PCD_mdp _ _ q r dqr dq =>
      PCD_mdp
        (PCD_mdp (PCD_theorem (PHPImplyS a q r))
          (@ph_cl_derives_deduction Atom Gamma a (PImp q r) dqr))
        (@ph_cl_derives_deduction Atom Gamma a q dq)
  end.

Lemma ph_cl_derives_empty_iff :
  forall (Atom : Type) (p : pformula Atom),
    inhabited (@ph_cl_derives Atom ph_theory_empty p) <->
    ph_hilbert_provable (ph_hilbert_cl Atom) p.
Proof.
  intros Atom p; split.
  - intros [d]. induction d.
    + contradiction.
    + now constructor.
    + destruct IHd1 as [dpq]. destruct IHd2 as [dp].
      constructor. exact (PHPModusPonens dpq dp).
  - intros [b]. constructor. exact (PCD_theorem b).
Qed.

Lemma ph_theory_consistent_insert_iff :
  forall (Atom : Type) (Gamma : ph_theory Atom) (p : pformula Atom),
    ph_theory_consistent (ph_theory_insert Gamma p) <->
    ~ inhabited (ph_cl_derives Gamma (pneg p)).
Proof.
  intros Atom Gamma p; split.
  - intros Hconsistent [dneg]. apply Hconsistent. constructor.
    eapply PCD_mdp.
    + eapply ph_cl_derives_weaken; [|exact dneg].
      intros q Hq. now right.
    + apply PCD_assumption. now left.
  - intros Hnot [dbottom]. apply Hnot. constructor.
    exact (@ph_cl_derives_deduction Atom Gamma p PFalsum dbottom).
Qed.

(** * Enumerated Lindenbaum construction *)

Definition ph_lindenbaum_step {Atom : Type}
    (Gamma : ph_theory Atom) (p : pformula Atom) : ph_theory Atom :=
  if excluded_middle_informative
       (ph_theory_consistent (ph_theory_insert Gamma p))
  then ph_theory_insert Gamma p
  else ph_theory_insert Gamma (pneg p).

Lemma ph_lindenbaum_step_includes :
  forall (Atom : Type) (Gamma : ph_theory Atom) p,
    ph_theory_included Gamma (ph_lindenbaum_step Gamma p).
Proof.
  intros Atom Gamma p. unfold ph_lindenbaum_step.
  destruct (excluded_middle_informative
    (ph_theory_consistent (ph_theory_insert Gamma p)));
    intros q Hq; now right.
Qed.

Lemma ph_lindenbaum_step_decides :
  forall (Atom : Type) (Gamma : ph_theory Atom) p,
    ph_lindenbaum_step Gamma p p \/
    ph_lindenbaum_step Gamma p (pneg p).
Proof.
  intros Atom Gamma p. unfold ph_lindenbaum_step.
  destruct (excluded_middle_informative
    (ph_theory_consistent (ph_theory_insert Gamma p)));
    [left | right]; now left.
Qed.

Lemma ph_lindenbaum_step_consistent :
  forall (Atom : Type) (Gamma : ph_theory Atom) p,
    ph_theory_consistent Gamma ->
    ph_theory_consistent (ph_lindenbaum_step Gamma p).
Proof.
  intros Atom Gamma p Hconsistent. unfold ph_lindenbaum_step.
  destruct (excluded_middle_informative
    (ph_theory_consistent (ph_theory_insert Gamma p))) as [Hpos | Hpos].
  - exact Hpos.
  - apply (proj2 (ph_theory_consistent_insert_iff Gamma (pneg p))).
    intros [dnn].
    assert (Hp : inhabited (ph_cl_derives Gamma p)).
    { constructor. eapply PCD_mdp.
      - apply PCD_theorem. exact (ph_hilbert_cl_dne p).
      - exact dnn. }
    assert (Hneg : inhabited (ph_cl_derives Gamma (pneg p))).
    { apply NNPP. intro Hnotneg. apply Hpos.
      apply (proj2 (ph_theory_consistent_insert_iff Gamma p)). exact Hnotneg. }
    destruct Hp as [dp]. destruct Hneg as [dn].
    apply Hconsistent. constructor. exact (PCD_mdp dn dp).
Qed.

Fixpoint ph_lindenbaum_chain {Atom : Type}
    (K : pformula_atom_codec Atom) (Gamma : ph_theory Atom)
    (n : nat) : ph_theory Atom :=
  match n with
  | 0 => Gamma
  | S k => ph_lindenbaum_step (ph_lindenbaum_chain K Gamma k)
             (pformula_enum K k)
  end.

Lemma ph_lindenbaum_chain_included_succ :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom) n,
    ph_theory_included (ph_lindenbaum_chain K Gamma n)
      (ph_lindenbaum_chain K Gamma (S n)).
Proof. intros Atom K Gamma n; simpl; apply ph_lindenbaum_step_includes. Qed.

Lemma ph_theory_included_refl :
  forall (Atom : Type) (Gamma : ph_theory Atom),
    ph_theory_included Gamma Gamma.
Proof. intros Atom Gamma p Hp; exact Hp. Qed.

Lemma ph_theory_included_trans :
  forall (Atom : Type) (A B C : ph_theory Atom),
    ph_theory_included A B -> ph_theory_included B C ->
    ph_theory_included A C.
Proof. intros Atom A B C Hab Hbc p Hp. apply Hbc, Hab, Hp. Qed.

Lemma ph_lindenbaum_chain_included_le :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom) m n,
    m <= n ->
    ph_theory_included (ph_lindenbaum_chain K Gamma m)
      (ph_lindenbaum_chain K Gamma n).
Proof.
  intros Atom K Gamma m n Hmn. induction Hmn.
  - apply ph_theory_included_refl.
  - eapply ph_theory_included_trans; [exact IHHmn |].
    apply ph_lindenbaum_chain_included_succ.
Qed.

Lemma ph_lindenbaum_chain_consistent :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom),
    ph_theory_consistent Gamma ->
    forall n, ph_theory_consistent (ph_lindenbaum_chain K Gamma n).
Proof.
  intros Atom K Gamma Hconsistent n; induction n; simpl.
  - exact Hconsistent.
  - now apply ph_lindenbaum_step_consistent.
Qed.

Definition ph_lindenbaum_limit {Atom : Type}
    (K : pformula_atom_codec Atom) (Gamma : ph_theory Atom) :
    ph_theory Atom :=
  fun p => exists n, ph_lindenbaum_chain K Gamma n p.

Lemma ph_lindenbaum_limit_includes :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom),
    ph_theory_included Gamma (ph_lindenbaum_limit K Gamma).
Proof. intros Atom K Gamma p Hp. exists 0. exact Hp. Qed.

Lemma ph_lindenbaum_limit_complete :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom) p,
    ph_lindenbaum_limit K Gamma p \/
    ph_lindenbaum_limit K Gamma (pneg p).
Proof.
  intros Atom K Gamma p.
  destruct (pformula_enum_surjective K p) as [n Henum].
  destruct (ph_lindenbaum_step_decides
    (ph_lindenbaum_chain K Gamma n) (pformula_enum K n)) as [H | H].
  - left. exists (S n). simpl. rewrite <- Henum. exact H.
  - right. exists (S n). simpl. rewrite <- Henum. exact H.
Qed.

Lemma ph_cl_derives_lindenbaum_limit_stage :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom) p,
    ph_cl_derives (ph_lindenbaum_limit K Gamma) p ->
    exists n, inhabited
      (ph_cl_derives (ph_lindenbaum_chain K Gamma n) p).
Proof.
  intros Atom K Gamma p d.
  induction d as [q Hq | q b | q r dqr IHqr dq IHq].
  - destruct Hq as [n Hn]. exists n. constructor. exact (PCD_assumption Hn).
  - exists 0. constructor. exact (PCD_theorem b).
  - destruct IHqr as [n [dn]]. destruct IHq as [m [dm]].
    exists (n + m). constructor. eapply PCD_mdp.
    + eapply ph_cl_derives_weaken; [|exact dn].
      apply ph_lindenbaum_chain_included_le. lia.
    + eapply ph_cl_derives_weaken; [|exact dm].
      apply ph_lindenbaum_chain_included_le. lia.
Qed.

Lemma ph_lindenbaum_limit_consistent :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom),
    ph_theory_consistent Gamma ->
    ph_theory_consistent (ph_lindenbaum_limit K Gamma).
Proof.
  intros Atom K Gamma Hconsistent [d].
  destruct (ph_cl_derives_lindenbaum_limit_stage d) as [n [dn]].
  exact ((@ph_lindenbaum_chain_consistent Atom K Gamma Hconsistent n)
    (inhabits dn)).
Qed.

(** * Maximal consistent theories *)

Record ph_maximal_consistent_theory (Atom : Type) : Type := {
  ph_mct_carrier :> ph_theory Atom;
  ph_mct_consistent : ph_theory_consistent ph_mct_carrier;
  ph_mct_complete : forall p,
    ph_mct_carrier p \/ ph_mct_carrier (pneg p)
}.

Arguments ph_mct_carrier {Atom} _.
Arguments ph_mct_consistent {Atom} _.
Arguments ph_mct_complete {Atom} _ _.

Definition ph_lindenbaum_mct {Atom : Type}
    (K : pformula_atom_codec Atom) (Gamma : ph_theory Atom)
    (Hconsistent : ph_theory_consistent Gamma) :
    ph_maximal_consistent_theory Atom :=
  {| ph_mct_carrier := ph_lindenbaum_limit K Gamma;
     ph_mct_consistent :=
       @ph_lindenbaum_limit_consistent Atom K Gamma Hconsistent;
     ph_mct_complete := @ph_lindenbaum_limit_complete Atom K Gamma |}.

Theorem ph_lindenbaum_extension :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (Gamma : ph_theory Atom),
    ph_theory_consistent Gamma ->
    {M : ph_maximal_consistent_theory Atom &
      ph_theory_included Gamma (ph_mct_carrier M)}.
Proof.
  intros Atom K Gamma Hconsistent.
  exists (@ph_lindenbaum_mct Atom K Gamma Hconsistent).
  apply ph_lindenbaum_limit_includes.
Defined.

Lemma ph_mct_not_both :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom) p,
    ph_mct_carrier M p -> ~ ph_mct_carrier M (pneg p).
Proof.
  intros Atom M p Hp Hnp. apply (ph_mct_consistent M). constructor.
  exact (PCD_mdp (PCD_assumption Hnp) (PCD_assumption Hp)).
Qed.

Lemma ph_mct_bottom_absent :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom),
    ~ ph_mct_carrier M PFalsum.
Proof.
  intros Atom M Hbottom. apply (ph_mct_consistent M). constructor.
  exact (PCD_assumption Hbottom).
Qed.

Lemma ph_mct_neg_iff :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom) p,
    ph_mct_carrier M (pneg p) <-> ~ ph_mct_carrier M p.
Proof.
  intros Atom M p; split.
  - intros Hnp Hp. exact (@ph_mct_not_both Atom M p Hp Hnp).
  - intro Hnot. destruct (ph_mct_complete M p) as [Hp | Hnp].
    + contradiction.
    + exact Hnp.
Qed.

Lemma ph_mct_derivable_mem :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom) p,
    ph_cl_derives (ph_mct_carrier M) p -> ph_mct_carrier M p.
Proof.
  intros Atom M p d. destruct (ph_mct_complete M p) as [Hp | Hnp].
  - exact Hp.
  - exfalso. apply (ph_mct_consistent M). constructor.
    exact (PCD_mdp (PCD_assumption Hnp) d).
Qed.

Lemma ph_mct_theorem_mem :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom) p,
    ph_hilbert_proof (ph_hilbert_cl Atom) p -> ph_mct_carrier M p.
Proof.
  intros Atom M p b. apply ph_mct_derivable_mem.
  exact (PCD_theorem b).
Qed.

Lemma ph_mct_and_iff :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom) p q,
    ph_mct_carrier M (PAnd p q) <->
    ph_mct_carrier M p /\ ph_mct_carrier M q.
Proof.
  intros Atom M p q; split.
  - intro Hpandq; split; apply ph_mct_derivable_mem.
    + exact (PCD_mdp (PCD_theorem (PHPAndElimL p q))
        (PCD_assumption Hpandq)).
    + exact (PCD_mdp (PCD_theorem (PHPAndElimR p q))
        (PCD_assumption Hpandq)).
  - intros [Hp Hq]. apply ph_mct_derivable_mem.
    exact (PCD_mdp
      (PCD_mdp (PCD_theorem (PHPAndIntro p q)) (PCD_assumption Hp))
      (PCD_assumption Hq)).
Qed.

Lemma ph_mct_or_iff :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom) p q,
    ph_mct_carrier M (POr p q) <->
    ph_mct_carrier M p \/ ph_mct_carrier M q.
Proof.
  intros Atom M p q; split.
  - intro Hporq.
    destruct (classic (ph_mct_carrier M p)) as [Hp | Hnp]; [now left |].
    destruct (classic (ph_mct_carrier M q)) as [Hq | Hnq]; [now right |].
    exfalso. apply (ph_mct_consistent M). constructor.
    exact (PCD_mdp
      (PCD_mdp
        (PCD_mdp (PCD_theorem (PHPOrElim p q PFalsum))
          (PCD_assumption ((proj2 (@ph_mct_neg_iff Atom M p)) Hnp)))
        (PCD_assumption ((proj2 (@ph_mct_neg_iff Atom M q)) Hnq)))
      (PCD_assumption Hporq)).
  - intros [Hp | Hq]; apply ph_mct_derivable_mem.
    + exact (PCD_mdp (PCD_theorem (PHPOrIntroL p q))
        (PCD_assumption Hp)).
    + exact (PCD_mdp (PCD_theorem (PHPOrIntroR p q))
        (PCD_assumption Hq)).
Qed.

Lemma ph_mct_imp_iff :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom) p q,
    ph_mct_carrier M (PImp p q) <->
    (ph_mct_carrier M p -> ph_mct_carrier M q).
Proof.
  intros Atom M p q; split.
  - intros Himp Hp. apply ph_mct_derivable_mem.
    exact (PCD_mdp (PCD_assumption Himp) (PCD_assumption Hp)).
  - intro Hpq. destruct (ph_mct_complete M p) as [Hp | Hnp].
    + apply ph_mct_derivable_mem.
      exact (PCD_mdp (PCD_theorem (PHPImplyK q p))
        (PCD_assumption (Hpq Hp))).
    + apply ph_mct_derivable_mem.
      exact (PCD_mdp
        (PCD_mdp
          (PCD_theorem (PHPImplyS p PFalsum q))
          (PCD_mdp (PCD_theorem (PHPImplyK (PImp PFalsum q) p))
            (PCD_theorem (ph_hilbert_cl_efq q))))
        (PCD_assumption Hnp)).
Qed.

(** The canonical valuation reads an atom as true precisely when its formula
    belongs to the maximal theory.  The connective cases are now immediate
    from the four factored closure lemmas above. *)
Theorem ph_mct_truth_lemma :
  forall (Atom : Type) (M : ph_maximal_consistent_theory Atom)
         (p : pformula Atom),
    ph_mct_carrier M p <->
    pboolean_eval (fun a => ph_mct_carrier M (PAtom a)) p.
Proof.
  intros Atom M p; induction p as
    [a | | p IHp q IHq | p IHp q IHq | p IHp q IHq]; simpl.
  - reflexivity.
  - split.
    + exact (@ph_mct_bottom_absent Atom M).
    + tauto.
  - rewrite (@ph_mct_and_iff Atom M p q), IHp, IHq. reflexivity.
  - rewrite (@ph_mct_or_iff Atom M p q), IHp, IHq. reflexivity.
  - rewrite (@ph_mct_imp_iff Atom M p q), IHp, IHq. reflexivity.
Qed.

(** * Completeness *)

Lemma ph_cl_neg_seed_consistent :
  forall (Atom : Type) (p : pformula Atom),
    ~ ph_hilbert_provable (ph_hilbert_cl Atom) p ->
    ph_theory_consistent
      (ph_theory_insert ph_theory_empty (pneg p)).
Proof.
  intros Atom p Hnot [dbottom].
  pose (dnn := @ph_cl_derives_deduction Atom ph_theory_empty
    (pneg p) PFalsum dbottom).
  assert (Hnn : ph_hilbert_provable (ph_hilbert_cl Atom) (pneg (pneg p))).
  { apply (proj1 (@ph_cl_derives_empty_iff Atom (pneg (pneg p)))).
    constructor. exact dnn. }
  apply Hnot. destruct Hnn as [bnn]. constructor.
  exact (PHPModusPonens (ph_hilbert_cl_dne p) bnn).
Qed.

Theorem ph_cl_provable_complete :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (p : pformula Atom),
    pformula_is_tautology p ->
    ph_hilbert_provable (ph_hilbert_cl Atom) p.
Proof.
  intros Atom K p Hvalid. apply NNPP. intro Hnot.
  pose proof (@ph_cl_neg_seed_consistent Atom p Hnot) as Hseed.
  destruct (@ph_lindenbaum_extension Atom K
    (ph_theory_insert ph_theory_empty (pneg p)) Hseed) as [M Hincl].
  pose (v := (fun a => ph_mct_carrier M (PAtom a)) : pvaluation Atom).
  assert (Hp : ph_mct_carrier M p).
  { apply (proj2 (@ph_mct_truth_lemma Atom M p)). exact (Hvalid v). }
  assert (Hnp : ph_mct_carrier M (pneg p)).
  { apply Hincl. now left. }
  exact (@ph_mct_not_both Atom M p Hp Hnp).
Qed.

Theorem ph_cl_provable_iff_tautology :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (p : pformula Atom),
    ph_hilbert_provable (ph_hilbert_cl Atom) p <->
    pformula_is_tautology p.
Proof.
  intros Atom K p; split.
  - apply ph_cl_provable_sound.
  - exact (@ph_cl_provable_complete Atom K p).
Qed.

Theorem ph_cl_exists_countervaluation_of_not_provable :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (p : pformula Atom),
    ~ ph_hilbert_provable (ph_hilbert_cl Atom) p ->
    exists v : pvaluation Atom, ~ pboolean_eval v p.
Proof.
  intros Atom K p Hnot.
  apply not_all_ex_not. intro Hvalid. apply Hnot.
  exact (@ph_cl_provable_complete Atom K p Hvalid).
Qed.

Theorem ph_logic_cl_iff_tautology :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
         (p : pformula Atom),
    pformula_logic_theorems (ph_logic_cl Atom) p <->
    pformula_is_tautology p.
Proof.
  intros Atom K p.
  exact (@ph_cl_provable_iff_tautology Atom K p).
Qed.
