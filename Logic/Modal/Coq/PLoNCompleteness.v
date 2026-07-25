(**
  Hilbert soundness, canonical completeness, and the logic N for PLoN.

  This file ports the mathematical surface of Foundation's
  [Modal/PLoN/Hilbert.lean], [Modal/PLoN/Completeness.lean],
  [Modal/PLoN/Logic/N.lean], and the umbrella [Modal/PLoN/Logic.lean] at the
  pinned read-only revision.

  Foundation's generic [Axiom] and [Entailment] typeclasses are represented
  concretely by a predicate [Ax] of already-instantiated axiom formulas and
  the calculus [plon_hilbert_proves Ax].  This is the smallest faithful local
  analogue: it retains arbitrary extra axiom instances, the classical
  Lukasiewicz basis, modus ponens, and necessitation.  In particular the
  empty predicate is Foundation's logic N.  It deliberately has neither
  regularity nor modal distribution K.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.ClassicalDescription Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms PLoN HilbertK FormulaEncoding.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The generic PLoN Hilbert calculus *)

Inductive plon_hilbert_proves (Ax : theory nat) : formula nat -> Prop :=
| PH_axiom : forall p, Ax p -> plon_hilbert_proves Ax p
| PH_imply_K : forall p q,
    plon_hilbert_proves Ax (Hilbert_imply_K p q)
| PH_imply_S : forall p q r,
    plon_hilbert_proves Ax (Hilbert_imply_S p q r)
| PH_elim_contra : forall p q,
    plon_hilbert_proves Ax (Hilbert_elim_contra p q)
| PH_mp : forall p q,
    plon_hilbert_proves Ax (Imp p q) ->
    plon_hilbert_proves Ax p ->
    plon_hilbert_proves Ax q
| PH_nec : forall p,
    plon_hilbert_proves Ax p -> plon_hilbert_proves Ax (Box p).

Arguments PH_axiom {Ax p} _.
Arguments PH_imply_K {Ax} p q.
Arguments PH_imply_S {Ax} p q r.
Arguments PH_elim_contra {Ax} p q.
Arguments PH_mp {Ax p q} _ _.
Arguments PH_nec {Ax p} _.

Lemma plon_proves_identity :
  forall Ax p, plon_hilbert_proves Ax (Imp p p).
Proof.
  intros Ax p.
  eapply PH_mp.
  - eapply PH_mp.
    + exact (PH_imply_S p (Imp p p) p).
    + exact (PH_imply_K p (Imp p p)).
  - exact (PH_imply_K p p).
Qed.

Lemma plon_proves_imply_intro :
  forall Ax p q,
    plon_hilbert_proves Ax q ->
    plon_hilbert_proves Ax (Imp p q).
Proof.
  intros Ax p q Hq.
  eapply PH_mp; [exact (PH_imply_K q p) | exact Hq].
Qed.

Lemma plon_proves_under_mp :
  forall Ax p q r,
    plon_hilbert_proves Ax (Imp p (Imp q r)) ->
    plon_hilbert_proves Ax (Imp p q) ->
    plon_hilbert_proves Ax (Imp p r).
Proof.
  intros Ax p q r Hqr Hq.
  eapply PH_mp.
  - eapply PH_mp; [exact (PH_imply_S p q r) | exact Hqr].
  - exact Hq.
Qed.

Lemma plon_proves_dne :
  forall Ax p, plon_hilbert_proves Ax (Imp (Neg (Neg p)) p).
Proof.
  intros Ax p.
  pose proof
    (plon_proves_imply_intro (Ax := Ax) (Neg (Neg p))
       (PH_elim_contra (Neg p) (Neg (Neg (Neg p))))) as H1.
  pose proof
    (PH_imply_K (Ax := Ax) (Neg (Neg p))
       (Neg (Neg (Neg (Neg p))))) as H2.
  pose proof
    (plon_proves_imply_intro (Ax := Ax) (Neg (Neg p))
       (PH_elim_contra (Neg (Neg p)) p)) as H3.
  pose proof (plon_proves_under_mp H1 H2) as H4.
  pose proof (plon_proves_under_mp H3 H4) as H5.
  exact (plon_proves_under_mp H5
    (@plon_proves_identity Ax (Neg (Neg p)))).
Qed.

Lemma plon_proves_dni :
  forall Ax p, plon_hilbert_proves Ax (Imp p (Neg (Neg p))).
Proof.
  intros Ax p.
  eapply PH_mp.
  - exact (PH_elim_contra p (Neg (Neg p))).
  - exact (@plon_proves_dne Ax (Neg p)).
Qed.

Lemma plon_proves_ex_falso :
  forall Ax p, plon_hilbert_proves Ax (Imp Bottom p).
Proof.
  intros Ax p.
  eapply PH_mp.
  - exact (PH_elim_contra Bottom p).
  - apply plon_proves_imply_intro.
    apply plon_proves_identity.
Qed.

(** Contexts contain assumptions and theorems and are closed only under
    modus ponens.  Necessitation remains a theorem rule, as in Foundation. *)
Inductive plon_derives (Ax : theory nat) (Gamma : theory nat)
    : formula nat -> Prop :=
| PD_assumption : forall p, Gamma p -> plon_derives Ax Gamma p
| PD_theorem : forall p,
    plon_hilbert_proves Ax p -> plon_derives Ax Gamma p
| PD_mp : forall p q,
    plon_derives Ax Gamma (Imp p q) ->
    plon_derives Ax Gamma p ->
    plon_derives Ax Gamma q.

Arguments PD_assumption {Ax Gamma p} _.
Arguments PD_theorem {Ax Gamma p} _.
Arguments PD_mp {Ax Gamma p q} _ _.

Lemma plon_derives_weaken :
  forall Ax Gamma Delta p,
    theory_included Gamma Delta ->
    plon_derives Ax Gamma p -> plon_derives Ax Delta p.
Proof.
  intros Ax Gamma Delta p Hin Hp; induction Hp.
  - apply PD_assumption; auto.
  - apply PD_theorem; assumption.
  - eapply PD_mp; eauto.
Qed.

Lemma plon_derives_empty_iff :
  forall Ax p,
    plon_derives Ax empty_theory p <-> plon_hilbert_proves Ax p.
Proof.
  intros Ax p; split.
  - intro Hp; induction Hp.
    + contradiction.
    + assumption.
    + eapply PH_mp; eauto.
  - now apply PD_theorem.
Qed.

Lemma plon_derives_imply_intro :
  forall Ax Gamma p q,
    plon_derives Ax Gamma q -> plon_derives Ax Gamma (Imp p q).
Proof.
  intros Ax Gamma p q Hq.
  eapply PD_mp.
  - apply PD_theorem; exact (PH_imply_K q p).
  - exact Hq.
Qed.

Lemma plon_derives_under_mp :
  forall Ax Gamma p q r,
    plon_derives Ax Gamma (Imp p (Imp q r)) ->
    plon_derives Ax Gamma (Imp p q) ->
    plon_derives Ax Gamma (Imp p r).
Proof.
  intros Ax Gamma p q r Hqr Hq.
  eapply PD_mp.
  - eapply PD_mp.
    + apply PD_theorem; exact (PH_imply_S p q r).
    + exact Hqr.
  - exact Hq.
Qed.

Lemma plon_derives_deduction :
  forall Ax Gamma p q,
    plon_derives Ax (theory_insert Gamma p) q ->
    plon_derives Ax Gamma (Imp p q).
Proof.
  intros Ax Gamma p q Hq.
  induction Hq as [r Hr | r Hr | r s Hrs IHrs Hr IHr].
  - destruct Hr as [-> | Hr].
    + apply PD_theorem; apply plon_proves_identity.
    + apply plon_derives_imply_intro; now apply PD_assumption.
  - apply plon_derives_imply_intro; now apply PD_theorem.
  - exact (plon_derives_under_mp IHrs IHr).
Qed.

Lemma plon_derives_undeduction :
  forall Ax Gamma p q,
    plon_derives Ax Gamma (Imp p q) ->
    plon_derives Ax (theory_insert Gamma p) q.
Proof.
  intros Ax Gamma p q Hpq.
  eapply PD_mp.
  - eapply plon_derives_weaken; [|exact Hpq].
    intros r Hr; now right.
  - apply PD_assumption; now left.
Qed.

Lemma plon_derives_dne :
  forall Ax Gamma p,
    plon_derives Ax Gamma (Neg (Neg p)) -> plon_derives Ax Gamma p.
Proof.
  intros Ax Gamma p Hp.
  eapply PD_mp; [apply PD_theorem; apply plon_proves_dne | exact Hp].
Qed.

Lemma plon_derives_ex_falso :
  forall Ax Gamma p,
    plon_derives Ax Gamma Bottom -> plon_derives Ax Gamma p.
Proof.
  intros Ax Gamma p Hbottom.
  eapply PD_mp;
    [apply PD_theorem; apply plon_proves_ex_falso | exact Hbottom].
Qed.

Definition plon_theory_consistent (Ax Gamma : theory nat) : Prop :=
  ~ plon_derives Ax Gamma Bottom.

Definition plon_system_consistent (Ax : theory nat) : Prop :=
  ~ plon_hilbert_proves Ax Bottom.

Lemma plon_empty_theory_consistent_iff :
  forall Ax,
    plon_theory_consistent Ax empty_theory <-> plon_system_consistent Ax.
Proof.
  intros Ax; unfold plon_theory_consistent, plon_system_consistent.
  rewrite plon_derives_empty_iff; reflexivity.
Qed.

Lemma plon_theory_consistent_insert_iff :
  forall Ax Gamma p,
    plon_theory_consistent Ax (theory_insert Gamma p) <->
    ~ plon_derives Ax Gamma (Neg p).
Proof.
  intros Ax Gamma p; split.
  - intros Hconsistent Hneg.
    apply Hconsistent; exact (plon_derives_undeduction Hneg).
  - intros Hnot Hbottom.
    apply Hnot; exact (plon_derives_deduction Hbottom).
Qed.

Lemma plon_theory_consistent_insert_neg_iff :
  forall Ax Gamma p,
    plon_theory_consistent Ax (theory_insert Gamma (Neg p)) <->
    ~ plon_derives Ax Gamma p.
Proof.
  intros Ax Gamma p; split.
  - intros Hconsistent Hp.
    apply Hconsistent.
    eapply PD_mp.
    + apply PD_assumption; now left.
    + eapply plon_derives_weaken; [|exact Hp].
      intros r Hr; now right.
  - intros Hnot Hbottom.
    apply Hnot; apply plon_derives_dne.
    exact (plon_derives_deduction Hbottom).
Qed.

(** * PLoN Hilbert soundness *)

Definition plon_axioms_valid (C : plon_frame_class) (Ax : theory nat)
    : Prop :=
  forall p, Ax p -> plon_frame_class_valid C p.

Definition plon_sound (Ax : theory nat) (C : plon_frame_class) : Prop :=
  forall p, plon_hilbert_proves Ax p -> plon_frame_class_valid C p.

Theorem plon_soundness_frameclass :
  forall Ax C,
    plon_axioms_valid C Ax -> plon_sound Ax C.
Proof.
  intros Ax C HAx p Hp; induction Hp.
  - now apply HAx.
  - intros F _ V; apply plon_model_valid_imply_K.
  - intros F _ V; apply plon_model_valid_imply_S.
  - intros F _ V; apply plon_model_valid_elim_contra.
  - intros F HF V.
    eapply plon_model_valid_mp; [apply IHHp1 | apply IHHp2]; exact HF.
  - intros F HF V.
    apply plon_model_valid_nec; apply IHHp; exact HF.
Qed.

Definition plon_frameclass_sound := plon_soundness_frameclass.

Theorem plon_consistent_of_nonempty_frameclass :
  forall Ax C,
    (exists F, C F) ->
    plon_sound Ax C ->
    plon_system_consistent Ax.
Proof.
  intros Ax C [F HF] Hsound Hbottom.
  apply (@plon_frame_invalid_bottom F).
  exact (Hsound Bottom Hbottom F HF).
Qed.

(** * Lindenbaum completion for the generic calculus *)

Lemma plon_theory_included_refl :
  forall Gamma : theory nat, theory_included Gamma Gamma.
Proof. intros Gamma p Hp; exact Hp. Qed.

Lemma plon_theory_included_trans :
  forall Gamma Delta Theta : theory nat,
    theory_included Gamma Delta ->
    theory_included Delta Theta ->
    theory_included Gamma Theta.
Proof. intros Gamma Delta Theta HGD HDT p Hp; auto. Qed.

Definition plon_lindenbaum_step
    (Ax Gamma : theory nat) (p : formula nat) : theory nat :=
  if excluded_middle_informative
       (plon_theory_consistent Ax (theory_insert Gamma p))
  then theory_insert Gamma p
  else theory_insert Gamma (Neg p).

Lemma plon_lindenbaum_step_includes :
  forall Ax Gamma p,
    theory_included Gamma (plon_lindenbaum_step Ax Gamma p).
Proof.
  intros Ax Gamma p; unfold plon_lindenbaum_step.
  destruct (excluded_middle_informative
    (plon_theory_consistent Ax (theory_insert Gamma p)));
    intros q Hq; right; exact Hq.
Qed.

Lemma plon_lindenbaum_step_decides :
  forall Ax Gamma p,
    plon_lindenbaum_step Ax Gamma p p \/
    plon_lindenbaum_step Ax Gamma p (Neg p).
Proof.
  intros Ax Gamma p; unfold plon_lindenbaum_step.
  destruct (excluded_middle_informative
    (plon_theory_consistent Ax (theory_insert Gamma p))).
  - left; now left.
  - right; now left.
Qed.

Lemma plon_lindenbaum_step_consistent :
  forall Ax Gamma p,
    plon_theory_consistent Ax Gamma ->
    plon_theory_consistent Ax (plon_lindenbaum_step Ax Gamma p).
Proof.
  intros Ax Gamma p Hconsistent; unfold plon_lindenbaum_step.
  destruct (excluded_middle_informative
    (plon_theory_consistent Ax (theory_insert Gamma p)))
    as [Hpositive | Hpositive].
  - exact Hpositive.
  - apply (proj2 (plon_theory_consistent_insert_neg_iff Ax Gamma p)).
    intro Hp.
    assert (Hneg : plon_derives Ax Gamma (Neg p)).
    { apply NNPP; intro Hnotneg.
      apply Hpositive.
      apply (proj2 (plon_theory_consistent_insert_iff Ax Gamma p)).
      exact Hnotneg. }
    apply Hconsistent.
    eapply PD_mp; [exact Hneg | exact Hp].
Qed.

Fixpoint plon_lindenbaum_chain
    (Ax Gamma : theory nat) (n : nat) : theory nat :=
  match n with
  | 0 => Gamma
  | S k => plon_lindenbaum_step Ax (plon_lindenbaum_chain Ax Gamma k)
             (modal_formula_enum k)
  end.

Lemma plon_lindenbaum_chain_included_succ :
  forall Ax Gamma n,
    theory_included (plon_lindenbaum_chain Ax Gamma n)
      (plon_lindenbaum_chain Ax Gamma (S n)).
Proof. intros; simpl; apply plon_lindenbaum_step_includes. Qed.

Lemma plon_lindenbaum_chain_included_le :
  forall Ax Gamma m n,
    m <= n ->
    theory_included (plon_lindenbaum_chain Ax Gamma m)
      (plon_lindenbaum_chain Ax Gamma n).
Proof.
  intros Ax Gamma m n Hmn; induction Hmn.
  - apply plon_theory_included_refl.
  - eapply plon_theory_included_trans.
    + exact IHHmn.
    + apply plon_lindenbaum_chain_included_succ.
Qed.

Lemma plon_lindenbaum_chain_consistent :
  forall Ax Gamma,
    plon_theory_consistent Ax Gamma ->
    forall n,
      plon_theory_consistent Ax (plon_lindenbaum_chain Ax Gamma n).
Proof.
  intros Ax Gamma Hconsistent n; induction n as [|n IH]; simpl.
  - exact Hconsistent.
  - now apply plon_lindenbaum_step_consistent.
Qed.

Definition plon_lindenbaum_limit
    (Ax Gamma : theory nat) : theory nat :=
  fun p => exists n, plon_lindenbaum_chain Ax Gamma n p.

Lemma plon_lindenbaum_limit_includes :
  forall Ax Gamma,
    theory_included Gamma (plon_lindenbaum_limit Ax Gamma).
Proof. intros Ax Gamma p Hp; exists 0; exact Hp. Qed.

Lemma plon_lindenbaum_limit_complete :
  forall Ax Gamma p,
    plon_lindenbaum_limit Ax Gamma p \/
    plon_lindenbaum_limit Ax Gamma (Neg p).
Proof.
  intros Ax Gamma p.
  destruct (modal_formula_enum_surjective p) as [n Henum].
  destruct (plon_lindenbaum_step_decides Ax
    (plon_lindenbaum_chain Ax Gamma n) (modal_formula_enum n)) as [H | H].
  - left; exists (S n).
    change (plon_lindenbaum_step Ax (plon_lindenbaum_chain Ax Gamma n)
      (modal_formula_enum n) p).
    now rewrite <- Henum.
  - right; exists (S n).
    change (plon_lindenbaum_step Ax (plon_lindenbaum_chain Ax Gamma n)
      (modal_formula_enum n) (Neg p)).
    now rewrite <- Henum.
Qed.

Lemma plon_derives_lindenbaum_limit_stage :
  forall Ax Gamma p,
    plon_derives Ax (plon_lindenbaum_limit Ax Gamma) p ->
    exists n, plon_derives Ax (plon_lindenbaum_chain Ax Gamma n) p.
Proof.
  intros Ax Gamma p Hder.
  induction Hder as [p Hp | p Hp | p q Hpq IHpq Hp IHp].
  - destruct Hp as [n Hp]. exists n. now apply PD_assumption.
  - exists 0. now apply PD_theorem.
  - destruct IHpq as [n Hpq_stage].
    destruct IHp as [m Hp_stage].
    exists (n + m). eapply PD_mp.
    + eapply plon_derives_weaken; [|exact Hpq_stage].
      apply plon_lindenbaum_chain_included_le; lia.
    + eapply plon_derives_weaken; [|exact Hp_stage].
      apply plon_lindenbaum_chain_included_le; lia.
Qed.

Lemma plon_lindenbaum_limit_consistent :
  forall Ax Gamma,
    plon_theory_consistent Ax Gamma ->
    plon_theory_consistent Ax (plon_lindenbaum_limit Ax Gamma).
Proof.
  intros Ax Gamma Hconsistent Hbottom.
  destruct (plon_derives_lindenbaum_limit_stage Hbottom) as [n Hstage].
  exact ((@plon_lindenbaum_chain_consistent Ax Gamma Hconsistent n) Hstage).
Qed.

Record plon_maximal_consistent_theory (Ax : theory nat) : Type := {
  plon_mct_carrier : theory nat;
  plon_mct_consistent : plon_theory_consistent Ax plon_mct_carrier;
  plon_mct_complete : forall p,
    plon_mct_carrier p \/ plon_mct_carrier (Neg p)
}.

Definition plon_mct_mem {Ax}
    (M : plon_maximal_consistent_theory Ax) (p : formula nat) : Prop :=
  plon_mct_carrier M p.

Definition plon_lindenbaum_mct
    (Ax Gamma : theory nat) (Hconsistent : plon_theory_consistent Ax Gamma)
    : plon_maximal_consistent_theory Ax.
Proof.
  refine {| plon_mct_carrier := plon_lindenbaum_limit Ax Gamma;
            plon_mct_consistent := _;
            plon_mct_complete := _ |}.
  - now apply plon_lindenbaum_limit_consistent.
  - intro p; apply plon_lindenbaum_limit_complete.
Defined.

Theorem plon_lindenbaum_extension :
  forall Ax Gamma,
    plon_theory_consistent Ax Gamma ->
    exists M : plon_maximal_consistent_theory Ax,
      theory_included Gamma (plon_mct_mem M).
Proof.
  intros Ax Gamma Hconsistent.
  exists (@plon_lindenbaum_mct Ax Gamma Hconsistent).
  apply plon_lindenbaum_limit_includes.
Qed.

Lemma plon_mct_not_both :
  forall Ax (M : plon_maximal_consistent_theory Ax) p,
    plon_mct_mem M p -> plon_mct_mem M (Neg p) -> False.
Proof.
  intros Ax M p Hp Hneg.
  apply (@plon_mct_consistent Ax M).
  eapply PD_mp.
  - apply PD_assumption; exact Hneg.
  - apply PD_assumption; exact Hp.
Qed.

Lemma plon_mct_bottom_absent :
  forall Ax (M : plon_maximal_consistent_theory Ax),
    ~ plon_mct_mem M Bottom.
Proof.
  intros Ax M Hbottom.
  apply (@plon_mct_consistent Ax M).
  now apply PD_assumption.
Qed.

Lemma plon_mct_neg_iff :
  forall Ax (M : plon_maximal_consistent_theory Ax) p,
    plon_mct_mem M (Neg p) <-> ~ plon_mct_mem M p.
Proof.
  intros Ax M p; split.
  - intros Hneg Hp; exact (@plon_mct_not_both Ax M p Hp Hneg).
  - intro Hnot; destruct (@plon_mct_complete Ax M p) as [Hp | Hneg].
    + contradiction.
    + exact Hneg.
Qed.

Lemma plon_mct_derivable_mem :
  forall Ax (M : plon_maximal_consistent_theory Ax) p,
    plon_derives Ax (plon_mct_mem M) p -> plon_mct_mem M p.
Proof.
  intros Ax M p Hder.
  destruct (@plon_mct_complete Ax M p) as [Hp | Hneg]; [exact Hp |].
  exfalso; apply (@plon_mct_consistent Ax M).
  eapply PD_mp.
  - apply PD_assumption; exact Hneg.
  - exact Hder.
Qed.

Lemma plon_proves_neg_imply :
  forall Ax p q,
    plon_hilbert_proves Ax (Imp (Neg p) (Imp p q)).
Proof.
  intros Ax p q.
  apply (proj1 (@plon_derives_empty_iff Ax (Imp (Neg p) (Imp p q)))).
  apply plon_derives_deduction.
  apply plon_derives_deduction.
  apply plon_derives_ex_falso.
  eapply PD_mp.
  - apply PD_assumption; right; now left.
  - apply PD_assumption; now left.
Qed.

Lemma plon_mct_imp_iff :
  forall Ax (M : plon_maximal_consistent_theory Ax) p q,
    plon_mct_mem M (Imp p q) <->
    (plon_mct_mem M p -> plon_mct_mem M q).
Proof.
  intros Ax M p q; split.
  - intros Himp Hp; apply plon_mct_derivable_mem.
    eapply PD_mp.
    + apply PD_assumption; exact Himp.
    + apply PD_assumption; exact Hp.
  - intro Hpq; destruct (@plon_mct_complete Ax M p) as [Hp | Hneg].
    + apply plon_mct_derivable_mem; eapply PD_mp.
      * apply PD_theorem; exact (PH_imply_K q p).
      * apply PD_assumption; exact (Hpq Hp).
    + apply plon_mct_derivable_mem; eapply PD_mp.
      * apply PD_theorem; apply plon_proves_neg_imply.
      * apply PD_assumption; exact Hneg.
Qed.

(** * Formula-indexed canonical model *)

Definition plon_canonical_default
    (Ax : theory nat) (Hsystem : plon_system_consistent Ax)
    : plon_maximal_consistent_theory Ax :=
  @plon_lindenbaum_mct Ax empty_theory
    ((proj2 (@plon_empty_theory_consistent_iff Ax)) Hsystem).

Definition plon_canonical_frame
    (Ax : theory nat) (Hsystem : plon_system_consistent Ax) : plon_frame :=
  {| plon_world := plon_maximal_consistent_theory Ax;
     plon_rel := fun p X Y =>
       plon_mct_mem X (Neg (Box p)) /\ plon_mct_mem Y (Neg p);
     plon_default := @plon_canonical_default Ax Hsystem |}.

Definition plon_canonical_model
    (Ax : theory nat) (Hsystem : plon_system_consistent Ax) : plon_model :=
  plon_model_on (@plon_canonical_frame Ax Hsystem)
    (fun X a => plon_mct_mem X (Atom a)).

Theorem plon_canonical_truth_lemma :
  forall Ax (Hsystem : plon_system_consistent Ax) p
         (X : plon_maximal_consistent_theory Ax),
    plon_satisfies (@plon_canonical_model Ax Hsystem) X p <->
    plon_mct_mem X p.
Proof.
  intros Ax Hsystem p; induction p as [a | | p IHp q IHq | p IHp]; intro X.
  - reflexivity.
  - split.
    + contradiction.
    + intro Hbottom; exact (@plon_mct_bottom_absent Ax X Hbottom).
  - change
      ((plon_satisfies (@plon_canonical_model Ax Hsystem) X p ->
        plon_satisfies (@plon_canonical_model Ax Hsystem) X q) <->
       plon_mct_mem X (Imp p q)).
    rewrite (IHp X), (IHq X).
    symmetry; apply plon_mct_imp_iff.
  - change
      ((forall Y : plon_maximal_consistent_theory Ax,
          (plon_mct_mem X (Neg (Box p)) /\ plon_mct_mem Y (Neg p)) ->
          plon_satisfies (@plon_canonical_model Ax Hsystem) Y p) <->
       plon_mct_mem X (Box p)).
    split.
    + intro Hsemantic.
      destruct (@plon_mct_complete Ax X (Box p)) as [Hbox | Hnegbox].
      * exact Hbox.
      * assert (Hnot_proves : ~ plon_hilbert_proves Ax p).
        { intro Hp.
          pose proof (@plon_mct_derivable_mem Ax X (Box p)
            (PD_theorem (PH_nec Hp))) as Hbox.
          exact (@plon_mct_not_both Ax X (Box p) Hbox Hnegbox). }
        assert (Hsingle :
          plon_theory_consistent Ax
            (theory_insert empty_theory (Neg p))).
        { apply (proj2
            (plon_theory_consistent_insert_neg_iff Ax empty_theory p)).
          intro Hder; apply Hnot_proves.
          apply (proj1 (@plon_derives_empty_iff Ax p)); exact Hder. }
        destruct (plon_lindenbaum_extension Hsingle) as [Y HY].
        assert (Hnegp : plon_mct_mem Y (Neg p)).
        { apply HY; now left. }
        assert (Hsatp :
          plon_satisfies (@plon_canonical_model Ax Hsystem) Y p).
        { apply Hsemantic; split; assumption. }
        assert (Hmem_p : plon_mct_mem Y p).
        { apply (proj1 (IHp Y)); exact Hsatp. }
        exfalso; exact (@plon_mct_not_both Ax Y p Hmem_p Hnegp).
    + intros Hbox Y [Hnegbox _].
      exfalso; exact (@plon_mct_not_both Ax X (Box p) Hbox Hnegbox).
Qed.

Definition plon_complete (Ax : theory nat) (C : plon_frame_class) : Prop :=
  forall p, plon_frame_class_valid C p -> plon_hilbert_proves Ax p.

Theorem plon_canonical_countermodel :
  forall Ax (Hsystem : plon_system_consistent Ax) p,
    ~ plon_hilbert_proves Ax p ->
    exists X : plon_maximal_consistent_theory Ax,
      ~ plon_satisfies (@plon_canonical_model Ax Hsystem) X p.
Proof.
  intros Ax Hsystem p Hnot.
  assert (Hsingle :
    plon_theory_consistent Ax (theory_insert empty_theory (Neg p))).
  { apply (proj2
      (plon_theory_consistent_insert_neg_iff Ax empty_theory p)).
    intro Hder; apply Hnot.
    apply (proj1 (@plon_derives_empty_iff Ax p)); exact Hder. }
  destruct (plon_lindenbaum_extension Hsingle) as [X HX].
  exists X; intro Hsat.
  apply (@plon_mct_not_both Ax X p).
  - apply (proj1 (plon_canonical_truth_lemma Hsystem p X)); exact Hsat.
  - apply HX; now left.
Qed.

Theorem plon_complete_of_canonical_frame :
  forall Ax C (Hsystem : plon_system_consistent Ax),
    C (@plon_canonical_frame Ax Hsystem) ->
    plon_complete Ax C.
Proof.
  intros Ax C Hsystem Hcanonical p Hvalid.
  apply NNPP; intro Hnot.
  destruct (@plon_canonical_countermodel Ax Hsystem p Hnot)
    as [X Hcounter].
  apply Hcounter.
  change (plon_satisfies
    (plon_model_on (@plon_canonical_frame Ax Hsystem)
      (fun X a => plon_mct_mem X (Atom a))) X p).
  exact (Hvalid (@plon_canonical_frame Ax Hsystem) Hcanonical
    (fun X a => plon_mct_mem X (Atom a)) X).
Qed.

Definition plon_inst_complete_of_mem_canonical_frame :=
  plon_complete_of_canonical_frame.

(** * The logic N: no extra modal axiom instances *)

Definition plon_no_axioms : theory nat := empty_theory.

Definition plon_N_proves (p : formula nat) : Prop :=
  plon_hilbert_proves plon_no_axioms p.

Definition plon_all_frames : plon_frame_class := fun _ => True.

Theorem plon_N_sound :
  plon_sound plon_no_axioms plon_all_frames.
Proof.
  apply plon_soundness_frameclass.
  intros p Hp; contradiction.
Qed.

Theorem plon_N_consistent :
  plon_system_consistent plon_no_axioms.
Proof.
  eapply (@plon_consistent_of_nonempty_frameclass
    plon_no_axioms plon_all_frames).
  - exists plon_terminal_frame; exact Logic.I.
  - exact plon_N_sound.
Qed.

Theorem plon_N_complete :
  plon_complete plon_no_axioms plon_all_frames.
Proof.
  apply (@plon_complete_of_canonical_frame
    plon_no_axioms plon_all_frames plon_N_consistent).
  exact Logic.I.
Qed.

Theorem plon_N_sound_complete :
  forall p,
    plon_N_proves p <-> plon_frame_class_valid plon_all_frames p.
Proof.
  intro p; split.
  - apply plon_N_sound.
  - apply plon_N_complete.
Qed.

Lemma plon_N_sound_on_model :
  forall p,
    plon_N_proves p -> forall M, plon_model_valid M p.
Proof.
  intros p Hp [F V].
  exact (@plon_N_sound p Hp F Logic.I V).
Qed.

(** * Strictness below K *)

Definition plon_weaker
    (P Q : formula nat -> Prop) : Prop :=
  forall p, P p -> Q p.

Definition plon_strictly_weaker
    (P Q : formula nat -> Prop) : Prop :=
  plon_weaker P Q /\ exists p, Q p /\ ~ P p.

Theorem plon_N_weaker_K :
  plon_weaker plon_N_proves (@K_proves nat).
Proof.
  intros p Hp; induction Hp.
  - contradiction.
  - apply Kp_imply_K.
  - apply Kp_imply_S.
  - apply Kp_elim_contra.
  - eapply Kp_mp; eauto.
  - now apply Kp_nec.
Qed.

Definition plon_K_counterexample_frame : plon_frame :=
  {| plon_world := bool;
     plon_rel := fun index x y =>
       index <> Imp (Atom 0) (Atom 1) /\ x = false /\ y = true;
     plon_default := false |}.

Definition plon_K_counterexample_model : plon_model :=
  plon_model_on plon_K_counterexample_frame
    (fun w a =>
      match a with
      | 0 => w = true
      | 1 => w = false
      | _ => False
      end).

Lemma plon_K_counterexample_invalid :
  ~ plon_model_valid plon_K_counterexample_model
      (K (Atom 0) (Atom 1)).
Proof.
  intro Hvalid; specialize (Hvalid false).
  assert (Hboximp :
    plon_satisfies plon_K_counterexample_model false
      (Box (Imp (Atom 0) (Atom 1)))).
  { intros u [Hneq _]; exfalso; apply Hneq; reflexivity. }
  assert (Hboxp :
    plon_satisfies plon_K_counterexample_model false (Box (Atom 0))).
  { intros u [_ [_ Hu]]; exact Hu. }
  specialize (Hvalid Hboximp Hboxp).
  specialize (Hvalid true).
  assert (Hrel :
    plon_rel plon_K_counterexample_frame (Atom 1) false true).
  { repeat split; try reflexivity; discriminate. }
  specialize (Hvalid Hrel).
  discriminate Hvalid.
Qed.

Theorem plon_N_strictly_weaker_K :
  plon_strictly_weaker plon_N_proves (@K_proves nat).
Proof.
  split.
  - exact plon_N_weaker_K.
  - exists (K (Atom 0) (Atom 1)); split.
    + apply Kp_modal_K.
    + intro HN.
      apply plon_K_counterexample_invalid.
      exact (@plon_N_sound_on_model _ HN plon_K_counterexample_model).
Qed.

(** * Strictness below EN (N plus replacement of equivalents) *)

Inductive plon_EN_proves : formula nat -> Prop :=
| PEN_from_N : forall p, plon_N_proves p -> plon_EN_proves p
| PEN_mp : forall p q,
    plon_EN_proves (Imp p q) ->
    plon_EN_proves p ->
    plon_EN_proves q
| PEN_nec : forall p,
    plon_EN_proves p -> plon_EN_proves (Box p)
| PEN_re : forall p q,
    plon_EN_proves (Iff p q) ->
    plon_EN_proves (Iff (Box p) (Box q)).

Arguments PEN_from_N {p} _.
Arguments PEN_mp {p q} _ _.
Arguments PEN_nec {p} _.
Arguments PEN_re {p q} _.

Theorem plon_N_weaker_EN :
  plon_weaker plon_N_proves plon_EN_proves.
Proof. intros p Hp; now apply PEN_from_N. Qed.

Lemma plon_N_proves_iff_dneg :
  forall p, plon_N_proves (Iff p (Neg (Neg p))).
Proof.
  intro p; apply plon_N_complete.
  intros F _ V w.
  apply (proj2 (@plon_satisfies_iff
    (plon_model_on F V) w p (Neg (Neg p)))).
  simpl; tauto.
Qed.

Definition plon_EN_witness : formula nat :=
  Iff (Box (Atom 0)) (Box (Neg (Neg (Atom 0)))).

Lemma plon_EN_proves_witness :
  plon_EN_proves plon_EN_witness.
Proof.
  unfold plon_EN_witness.
  apply PEN_re; apply PEN_from_N; apply plon_N_proves_iff_dneg.
Qed.

Definition plon_EN_counterexample_frame : plon_frame :=
  {| plon_world := bool;
     plon_rel := fun index _ _ => index = Neg (Neg (Atom 0));
     plon_default := false |}.

Definition plon_EN_counterexample_model : plon_model :=
  plon_model_on plon_EN_counterexample_frame
    (fun w _ => w = false).

Lemma plon_EN_counterexample_invalid :
  ~ plon_model_valid plon_EN_counterexample_model plon_EN_witness.
Proof.
  intro Hvalid; specialize (Hvalid false).
  apply (proj1 (@plon_satisfies_iff plon_EN_counterexample_model false
    (Box (Atom 0)) (Box (Neg (Neg (Atom 0)))))) in Hvalid.
  assert (Hboxp :
    plon_satisfies plon_EN_counterexample_model false (Box (Atom 0))).
  { intros u Hrel; discriminate Hrel. }
  specialize (proj1 Hvalid Hboxp) as Hboxdneg.
  specialize (Hboxdneg true eq_refl).
  apply Hboxdneg; intro Heq; discriminate Heq.
Qed.

Theorem plon_N_strictly_weaker_EN :
  plon_strictly_weaker plon_N_proves plon_EN_proves.
Proof.
  split.
  - exact plon_N_weaker_EN.
  - exists plon_EN_witness; split.
    + exact plon_EN_proves_witness.
    + intro HN.
      apply plon_EN_counterexample_invalid.
      exact (@plon_N_sound_on_model _ HN plon_EN_counterexample_model).
Qed.
