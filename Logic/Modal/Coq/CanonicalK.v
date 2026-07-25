(**
  Lindenbaum construction, canonical model, and completeness for modal K.

  Foundation splits this material across Modal/Tableau.lean,
  Modal/MaximalConsistentSet.lean, Modal/Kripke/Completeness.lean, and
  Modal/Kripke/Logic/K.lean.  For the concrete calculus [HilbertK], a
  one-sided maximal-consistent-theory presentation is substantially smaller:
  formulas are enumerated explicitly, each stage consistently decides the
  next formula, and the canonical relation unboxes the source theory.

  No semantic completeness principle is assumed.  Classical logic is used
  only to select a consistent branch at each Lindenbaum stage and to pass
  from semantic validity to derivability at the final contraposition step.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.ClassicalDescription Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax FormulaEncoding HilbertK Kripke HilbertKSoundness Filtration.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma theory_included_refl :
  forall (AtomType : Type) (Gamma : theory AtomType),
    theory_included Gamma Gamma.
Proof. intros AtomType Gamma p Hp; exact Hp. Qed.

Lemma theory_included_trans :
  forall (AtomType : Type) (Gamma Delta Theta : theory AtomType),
    theory_included Gamma Delta ->
    theory_included Delta Theta ->
    theory_included Gamma Theta.
Proof. intros AtomType Gamma Delta Theta HGD HDT p Hp; auto. Qed.

(** Add [p] when possible and [~p] otherwise. *)
Definition lindenbaum_step (Gamma : theory nat) (p : formula nat)
    : theory nat :=
  if excluded_middle_informative
       (theory_consistent (theory_insert Gamma p))
  then theory_insert Gamma p
  else theory_insert Gamma (Neg p).

Lemma lindenbaum_step_includes :
  forall Gamma p, theory_included Gamma (lindenbaum_step Gamma p).
Proof.
  intros Gamma p. unfold lindenbaum_step.
  destruct (excluded_middle_informative
    (theory_consistent (theory_insert Gamma p)));
    intros q Hq; right; exact Hq.
Qed.

Lemma lindenbaum_step_decides :
  forall Gamma p,
    lindenbaum_step Gamma p p \/ lindenbaum_step Gamma p (Neg p).
Proof.
  intros Gamma p. unfold lindenbaum_step.
  destruct (excluded_middle_informative
    (theory_consistent (theory_insert Gamma p))).
  - left. now left.
  - right. now left.
Qed.

Lemma lindenbaum_step_consistent :
  forall Gamma p,
    theory_consistent Gamma ->
    theory_consistent (lindenbaum_step Gamma p).
Proof.
  intros Gamma p Hconsistent. unfold lindenbaum_step.
  destruct (excluded_middle_informative
    (theory_consistent (theory_insert Gamma p))) as [Hpos | Hpos].
  - exact Hpos.
  - apply (proj2 (theory_consistent_insert_neg_iff Gamma p)).
    intro Hp.
    assert (Hneg : K_derives Gamma (Neg p)).
    { apply NNPP. intro Hnotneg.
      apply Hpos.
      apply (proj2 (theory_consistent_insert_iff Gamma p)).
      exact Hnotneg. }
    apply Hconsistent.
    eapply Kd_mp; [exact Hneg | exact Hp].
Qed.

Fixpoint lindenbaum_chain (Gamma : theory nat) (n : nat) : theory nat :=
  match n with
  | 0 => Gamma
  | S k => lindenbaum_step (lindenbaum_chain Gamma k)
             (modal_formula_enum k)
  end.

Lemma lindenbaum_chain_included_succ :
  forall Gamma n,
    theory_included (lindenbaum_chain Gamma n)
      (lindenbaum_chain Gamma (S n)).
Proof. intros Gamma n; simpl; apply lindenbaum_step_includes. Qed.

Lemma lindenbaum_chain_included_le :
  forall Gamma m n,
    m <= n ->
    theory_included (lindenbaum_chain Gamma m)
      (lindenbaum_chain Gamma n).
Proof.
  intros Gamma m n Hmn. induction Hmn.
  - apply theory_included_refl.
  - eapply theory_included_trans.
    + exact IHHmn.
    + apply lindenbaum_chain_included_succ.
Qed.

Lemma lindenbaum_chain_consistent :
  forall Gamma,
    theory_consistent Gamma ->
    forall n, theory_consistent (lindenbaum_chain Gamma n).
Proof.
  intros Gamma Hconsistent n; induction n as [|n IH]; simpl.
  - exact Hconsistent.
  - now apply lindenbaum_step_consistent.
Qed.

Definition lindenbaum_limit (Gamma : theory nat) : theory nat :=
  fun p => exists n, lindenbaum_chain Gamma n p.

Lemma lindenbaum_limit_includes :
  forall Gamma, theory_included Gamma (lindenbaum_limit Gamma).
Proof. intros Gamma p Hp. exists 0. exact Hp. Qed.

Lemma lindenbaum_limit_complete :
  forall Gamma p,
    lindenbaum_limit Gamma p \/ lindenbaum_limit Gamma (Neg p).
Proof.
  intros Gamma p.
  destruct (modal_formula_enum_surjective p) as [n Henum].
  destruct (lindenbaum_step_decides
    (lindenbaum_chain Gamma n) (modal_formula_enum n)) as [H | H].
  - left. exists (S n).
    change (lindenbaum_step (lindenbaum_chain Gamma n)
      (modal_formula_enum n) p).
    now rewrite <- Henum.
  - right. exists (S n).
    change (lindenbaum_step (lindenbaum_chain Gamma n)
      (modal_formula_enum n) (Neg p)).
    now rewrite <- Henum.
Qed.

(** Every finite derivation from the union already occurs at one stage. *)
Lemma K_derives_lindenbaum_limit_stage :
  forall Gamma p,
    K_derives (lindenbaum_limit Gamma) p ->
    exists n, K_derives (lindenbaum_chain Gamma n) p.
Proof.
  intros Gamma p Hder.
  induction Hder as [p Hp | p Hp | p q Hpq IHpq Hp IHp].
  - destruct Hp as [n Hp]. exists n. now apply Kd_assumption.
  - exists 0. now apply Kd_theorem.
  - destruct IHpq as [n Hpq_stage]. destruct IHp as [m Hp_stage].
    exists (n + m). eapply Kd_mp.
    + eapply K_derives_weaken; [|exact Hpq_stage].
      apply lindenbaum_chain_included_le. lia.
    + eapply K_derives_weaken; [|exact Hp_stage].
      apply lindenbaum_chain_included_le. lia.
Qed.

Lemma lindenbaum_limit_consistent :
  forall Gamma,
    theory_consistent Gamma ->
    theory_consistent (lindenbaum_limit Gamma).
Proof.
  intros Gamma Hconsistent Hbottom.
  destruct (K_derives_lindenbaum_limit_stage Hbottom) as [n Hstage].
  exact ((@lindenbaum_chain_consistent Gamma Hconsistent n) Hstage).
Qed.

Record maximal_consistent_theory : Type := {
  mct_carrier : theory nat;
  mct_consistent : theory_consistent mct_carrier;
  mct_complete : forall p, mct_carrier p \/ mct_carrier (Neg p)
}.

Definition mct_mem (M : maximal_consistent_theory) (p : formula nat) : Prop :=
  mct_carrier M p.

Theorem lindenbaum_extension :
  forall Gamma,
    theory_consistent Gamma ->
    exists M : maximal_consistent_theory,
      theory_included Gamma (mct_mem M).
Proof.
  intros Gamma Hconsistent.
  pose (Delta := lindenbaum_limit Gamma).
  assert (HDelta : theory_consistent Delta).
  { unfold Delta. now apply lindenbaum_limit_consistent. }
  assert (Hcomplete : forall p, Delta p \/ Delta (Neg p)).
  { intro p. unfold Delta. apply lindenbaum_limit_complete. }
  exists {| mct_carrier := Delta;
            mct_consistent := HDelta;
            mct_complete := Hcomplete |}.
  intros p Hp. unfold mct_mem, Delta. exists 0. exact Hp.
Qed.

Lemma mct_not_both :
  forall (M : maximal_consistent_theory) p,
    mct_mem M p -> mct_mem M (Neg p) -> False.
Proof.
  intros M p Hp Hneg.
  apply (@mct_consistent M).
  eapply Kd_mp.
  - apply Kd_assumption. exact Hneg.
  - apply Kd_assumption. exact Hp.
Qed.

Lemma mct_bottom_absent :
  forall M : maximal_consistent_theory,
    ~ mct_mem M Bottom.
Proof.
  intros M Hbottom. apply (@mct_consistent M).
  now apply Kd_assumption.
Qed.

Lemma mct_neg_iff :
  forall (M : maximal_consistent_theory) p,
    mct_mem M (Neg p) <-> ~ mct_mem M p.
Proof.
  intros M p; split.
  - intros Hneg Hp. exact (@mct_not_both M p Hp Hneg).
  - intro Hnot. destruct (@mct_complete M p) as [Hp | Hneg].
    + contradiction.
    + exact Hneg.
Qed.

Lemma mct_derivable_mem :
  forall (M : maximal_consistent_theory) p,
    K_derives (mct_mem M) p -> mct_mem M p.
Proof.
  intros M p Hder.
  destruct (@mct_complete M p) as [Hp | Hneg]; [exact Hp |].
  exfalso. apply (@mct_consistent M).
  eapply Kd_mp.
  - apply Kd_assumption. exact Hneg.
  - exact Hder.
Qed.

Lemma K_proves_neg_imply :
  forall (AtomType : Type) (p q : formula AtomType),
    K_proves (Imp (Neg p) (Imp p q)).
Proof.
  intros AtomType p q.
  apply (proj1 (@K_derives_empty_iff AtomType
    (Imp (Neg p) (Imp p q)))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_ex_falso.
  eapply Kd_mp.
  - apply Kd_assumption. right. now left.
  - apply Kd_assumption. now left.
Qed.

Lemma mct_imp_iff :
  forall (M : maximal_consistent_theory) p q,
    mct_mem M (Imp p q) <-> (mct_mem M p -> mct_mem M q).
Proof.
  intros M p q; split.
  - intros Himp Hp. apply mct_derivable_mem.
    eapply Kd_mp.
    + apply Kd_assumption. exact Himp.
    + apply Kd_assumption. exact Hp.
  - intro Hpq. destruct (@mct_complete M p) as [Hp | Hneg].
    + apply mct_derivable_mem. eapply Kd_mp.
      * apply Kd_theorem. exact (Kp_imply_K q p).
      * apply Kd_assumption. exact (Hpq Hp).
    + apply mct_derivable_mem. eapply Kd_mp.
      * apply Kd_theorem. apply K_proves_neg_imply.
      * apply Kd_assumption. exact Hneg.
Qed.

(** * The canonical frame and its existence lemma *)

Definition canonical_relation
    (M N : maximal_consistent_theory) : Prop :=
  forall p, mct_mem M (Box p) -> mct_mem N p.

Definition canonical_frame : frame :=
  {| World := maximal_consistent_theory;
     Rel := canonical_relation |}.

Definition canonical_valuation : valuation nat canonical_frame :=
  fun a M => mct_mem M (Atom a).

Theorem canonical_successor_of_neg_box :
  forall (M : maximal_consistent_theory) p,
    mct_mem M (Neg (Box p)) ->
    exists N : maximal_consistent_theory,
      canonical_relation M N /\ mct_mem N (Neg p).
Proof.
  intros M p Hnegbox.
  pose (Gamma := theory_insert
    (fun q => mct_mem M (Box q)) (Neg p)).
  assert (Hconsistent : theory_consistent Gamma).
  { unfold Gamma.
    apply (proj2 (theory_consistent_insert_neg_iff
      (fun q => mct_mem M (Box q)) p)).
    intro Hp.
    pose proof
      (@K_derives_box_from_unboxed nat (mct_mem M) p Hp) as Hbox.
    pose proof (@mct_derivable_mem M (Box p) Hbox) as Hboxmem.
    exact (@mct_not_both M (Box p) Hboxmem Hnegbox). }
  destruct (lindenbaum_extension Hconsistent) as [N Hinclude].
  exists N; split.
  - intros q Hbox. apply Hinclude. right. exact Hbox.
  - apply Hinclude. now left.
Qed.

Theorem canonical_truth_lemma :
  forall p : formula nat,
    forall M : maximal_consistent_theory,
      mct_mem M p <->
      satisfies canonical_frame canonical_valuation M p.
Proof.
  intro p; induction p as [a | | p IHp q IHq | p IHp]; intro M.
  - reflexivity.
  - split.
    + intro H. exact (@mct_bottom_absent M H).
    + intro Hfalse. contradiction.
  - change
      (mct_mem M (Imp p q) <->
       (satisfies canonical_frame canonical_valuation M p ->
        satisfies canonical_frame canonical_valuation M q)).
    rewrite <- (IHp M), <- (IHq M).
    apply mct_imp_iff.
  - change
      (mct_mem M (Box p) <->
       forall N, canonical_relation M N ->
         satisfies canonical_frame canonical_valuation N p).
    split.
    + intros Hbox N HMN.
      apply (proj1 (IHp N)). exact (HMN p Hbox).
    + intro Hsemantic.
      destruct (@mct_complete M (Box p)) as [Hbox | Hnegbox].
      * exact Hbox.
      * destruct (@canonical_successor_of_neg_box M p Hnegbox)
          as [N [HMN Hneg]].
        assert (Hp : mct_mem N p).
        { apply (proj2 (IHp N)). exact (Hsemantic N HMN). }
        exfalso. exact (@mct_not_both N p Hp Hneg).
Qed.

Theorem K_canonical_countermodel :
  forall p : formula nat,
    ~ K_proves p ->
    exists M : maximal_consistent_theory,
      ~ satisfies canonical_frame canonical_valuation M p.
Proof.
  intros p Hnot.
  assert (Hnot_empty : ~ K_derives empty_theory p).
  { intro Hder. apply Hnot.
    apply (proj1 (@K_derives_empty_iff nat p)). exact Hder. }
  assert (Hconsistent :
    theory_consistent (theory_insert empty_theory (Neg p))).
  { apply (proj2 (theory_consistent_insert_neg_iff empty_theory p)).
    exact Hnot_empty. }
  destruct (lindenbaum_extension Hconsistent) as [M Hinclude].
  exists M. intro Hsat.
  apply (@mct_not_both M p).
  - apply (proj2 (@canonical_truth_lemma p M)). exact Hsat.
  - apply Hinclude. now left.
Qed.

Theorem K_complete :
  forall p : formula nat,
    valid_on_all_frames p -> K_proves p.
Proof.
  intros p Hvalid. apply NNPP. intro Hnot.
  destruct (@K_canonical_countermodel p Hnot) as [M Hcounter].
  apply Hcounter. exact (Hvalid canonical_frame canonical_valuation M).
Qed.

Theorem K_sound_complete :
  forall p : formula nat,
    K_proves p <-> valid_on_all_frames p.
Proof.
  intro p; split.
  - intros Hp F. now apply K_proves_sound_on_frame.
  - apply K_complete.
Qed.

Theorem K_finite_sound_complete :
  forall p : formula nat,
    K_proves p <-> valid_on_finite_frames p.
Proof.
  intro p; split.
  - intros Hp F _; now apply K_proves_sound_on_frame.
  - intro Hfinite. apply K_complete.
    apply (proj1 (modal_finite_model_property p)). exact Hfinite.
Qed.
