(**
  Canonical completeness for normal Hilbert extensions.

  This module lifts the concrete construction in [CanonicalK] to the
  schema-parameterized calculus [normal_proves].  The generic part proves a
  Lindenbaum extension, maximal-theory laws, a canonical successor theorem,
  the truth lemma, and completeness for every class containing the resulting
  canonical frame.  The applications prove canonicality and hence full
  soundness/completeness for KT, K4, and S4.

  Foundation packages the same argument through generic entailment and
  canonical-frame typeclasses.  Here the dependencies are ordinary Coq
  propositions, which makes it impossible to use canonicality before it has
  actually been proved for the selected schema.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.ClassicalDescription Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax FormulaEncoding Axioms HilbertK Kripke HilbertKSoundness
  Correspondence Filtration FiltrationExtensions NormalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Contextual derivability for an arbitrary normal extension *)

Inductive normal_derives (Ax : modal_axiom_schema)
    (Gamma : theory nat) : formula nat -> Prop :=
| ND_assumption : forall p, Gamma p -> normal_derives Ax Gamma p
| ND_theorem : forall p, normal_proves Ax p -> normal_derives Ax Gamma p
| ND_mp : forall p q,
    normal_derives Ax Gamma (Imp p q) ->
    normal_derives Ax Gamma p ->
    normal_derives Ax Gamma q.

Arguments ND_assumption {Ax Gamma p} _.
Arguments ND_theorem {Ax Gamma p} _.
Arguments ND_mp {Ax Gamma p q} _ _.

Lemma normal_proves_identity :
  forall Ax (p : formula nat), normal_proves Ax (Imp p p).
Proof. intros Ax p. apply K_proves_normal. apply K_proves_identity. Qed.

Lemma normal_proves_imply_intro :
  forall Ax (p q : formula nat),
    normal_proves Ax q -> normal_proves Ax (Imp p q).
Proof.
  intros Ax p q Hq.
  eapply Np_mp; [exact (Np_imply_K q p) | exact Hq].
Qed.

Lemma normal_proves_under_mp :
  forall Ax (p q r : formula nat),
    normal_proves Ax (Imp p (Imp q r)) ->
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp p r).
Proof.
  intros Ax p q r Hqr Hq.
  eapply Np_mp.
  - eapply Np_mp; [exact (Np_imply_S p q r) | exact Hqr].
  - exact Hq.
Qed.

Lemma normal_proves_dni :
  forall Ax (p : formula nat), normal_proves Ax (Imp p (Neg (Neg p))).
Proof. intros Ax p. apply K_proves_normal. apply K_proves_dni. Qed.

Lemma normal_proves_dne :
  forall Ax (p : formula nat), normal_proves Ax (Imp (Neg (Neg p)) p).
Proof. intros Ax p. apply K_proves_normal. apply K_proves_dne. Qed.

Lemma normal_proves_ex_falso :
  forall Ax (p : formula nat), normal_proves Ax (Imp Bottom p).
Proof. intros Ax p. apply K_proves_normal. apply K_proves_ex_falso. Qed.

Lemma normal_derives_weaken :
  forall Ax Gamma Delta p,
    theory_included Gamma Delta ->
    normal_derives Ax Gamma p -> normal_derives Ax Delta p.
Proof.
  intros Ax Gamma Delta p Hinc Hp; induction Hp.
  - apply ND_assumption. now apply Hinc.
  - now apply ND_theorem.
  - eapply ND_mp; eauto.
Qed.

Lemma normal_derives_empty_iff :
  forall Ax p,
    normal_derives Ax empty_theory p <-> normal_proves Ax p.
Proof.
  intros Ax p; split.
  - intro Hp; induction Hp.
    + contradiction.
    + exact H.
    + eapply Np_mp; eauto.
  - now apply ND_theorem.
Qed.

Lemma normal_derives_imply_intro :
  forall Ax Gamma p q,
    normal_derives Ax Gamma q -> normal_derives Ax Gamma (Imp p q).
Proof.
  intros Ax Gamma p q Hq.
  eapply ND_mp.
  - apply ND_theorem. exact (Np_imply_K q p).
  - exact Hq.
Qed.

Lemma normal_derives_under_mp :
  forall Ax Gamma p q r,
    normal_derives Ax Gamma (Imp p (Imp q r)) ->
    normal_derives Ax Gamma (Imp p q) ->
    normal_derives Ax Gamma (Imp p r).
Proof.
  intros Ax Gamma p q r Hqr Hq.
  eapply ND_mp.
  - eapply ND_mp.
    + apply ND_theorem. exact (Np_imply_S p q r).
    + exact Hqr.
  - exact Hq.
Qed.

Lemma normal_derives_deduction :
  forall Ax Gamma p q,
    normal_derives Ax (theory_insert Gamma p) q ->
    normal_derives Ax Gamma (Imp p q).
Proof.
  intros Ax Gamma p q Hq.
  induction Hq as [r Hr | r Hr | r s Hrs IHrs Hr IHr].
  - destruct Hr as [-> | Hr].
    + apply ND_theorem. apply normal_proves_identity.
    + apply normal_derives_imply_intro. now apply ND_assumption.
  - apply normal_derives_imply_intro. now apply ND_theorem.
  - exact (normal_derives_under_mp IHrs IHr).
Qed.

Lemma normal_derives_undeduction :
  forall Ax Gamma p q,
    normal_derives Ax Gamma (Imp p q) ->
    normal_derives Ax (theory_insert Gamma p) q.
Proof.
  intros Ax Gamma p q Hpq.
  eapply ND_mp.
  - eapply normal_derives_weaken; [|exact Hpq].
    intros r Hr. now right.
  - apply ND_assumption. now left.
Qed.

Lemma normal_derives_dne :
  forall Ax Gamma p,
    normal_derives Ax Gamma (Neg (Neg p)) ->
    normal_derives Ax Gamma p.
Proof.
  intros Ax Gamma p Hp.
  eapply ND_mp; [apply ND_theorem; apply normal_proves_dne | exact Hp].
Qed.

Lemma normal_derives_ex_falso :
  forall Ax Gamma p,
    normal_derives Ax Gamma Bottom -> normal_derives Ax Gamma p.
Proof.
  intros Ax Gamma p Hbot.
  eapply ND_mp; [apply ND_theorem; apply normal_proves_ex_falso | exact Hbot].
Qed.

Definition normal_theory_consistent
    (Ax : modal_axiom_schema) (Gamma : theory nat) : Prop :=
  ~ normal_derives Ax Gamma Bottom.

Definition normal_system_consistent (Ax : modal_axiom_schema) : Prop :=
  ~ @normal_proves Ax nat Bottom.

Lemma normal_empty_theory_consistent_iff :
  forall Ax,
    normal_theory_consistent Ax empty_theory <->
    normal_system_consistent Ax.
Proof.
  intro Ax. unfold normal_theory_consistent, normal_system_consistent.
  now rewrite normal_derives_empty_iff.
Qed.

Lemma normal_theory_consistent_insert_iff :
  forall Ax Gamma p,
    normal_theory_consistent Ax (theory_insert Gamma p) <->
    ~ normal_derives Ax Gamma (Neg p).
Proof.
  intros Ax Gamma p; split.
  - intros Hconsistent Hneg.
    apply Hconsistent. exact (normal_derives_undeduction Hneg).
  - intros Hnot Hbottom.
    apply Hnot. exact (normal_derives_deduction Hbottom).
Qed.

Lemma normal_theory_consistent_insert_neg_iff :
  forall Ax Gamma p,
    normal_theory_consistent Ax (theory_insert Gamma (Neg p)) <->
    ~ normal_derives Ax Gamma p.
Proof.
  intros Ax Gamma p; split.
  - intros Hconsistent Hp. apply Hconsistent.
    eapply ND_mp.
    + apply ND_assumption. now left.
    + eapply normal_derives_weaken; [|exact Hp].
      intros r Hr. now right.
  - intros Hnot Hbottom. apply Hnot.
    apply normal_derives_dne.
    exact (normal_derives_deduction Hbottom).
Qed.

Lemma normal_derives_boxed :
  forall Ax Gamma p,
    normal_derives Ax Gamma p ->
    normal_derives Ax (boxed_theory Gamma) (Box p).
Proof.
  intros Ax Gamma p Hp; induction Hp.
  - apply ND_assumption. exists p; now split.
  - apply ND_theorem. now apply Np_nec.
  - eapply ND_mp.
    + eapply ND_mp.
      * apply ND_theorem. exact (Np_modal_K p q).
      * exact IHHp1.
    + exact IHHp2.
Qed.

Lemma normal_derives_box_from_unboxed :
  forall Ax Gamma p,
    normal_derives Ax (fun q => Gamma (Box q)) p ->
    normal_derives Ax Gamma (Box p).
Proof.
  intros Ax Gamma p Hp.
  assert (Hinc : theory_included
      (boxed_theory (fun q => Gamma (Box q))) Gamma).
  { intros r Hr. destruct Hr as [q [Hq ->]]. exact Hq. }
  exact (@normal_derives_weaken Ax
    (boxed_theory (fun q => Gamma (Box q))) Gamma (Box p)
    Hinc (normal_derives_boxed Hp)).
Qed.

(** * Lindenbaum completion *)

Definition normal_lindenbaum_step Ax (Gamma : theory nat)
    (p : formula nat) : theory nat :=
  if excluded_middle_informative
       (normal_theory_consistent Ax (theory_insert Gamma p))
  then theory_insert Gamma p
  else theory_insert Gamma (Neg p).

Lemma normal_lindenbaum_step_includes :
  forall Ax Gamma p,
    theory_included Gamma (normal_lindenbaum_step Ax Gamma p).
Proof.
  intros Ax Gamma p. unfold normal_lindenbaum_step.
  destruct (excluded_middle_informative
    (normal_theory_consistent Ax (theory_insert Gamma p)));
    intros q Hq; right; exact Hq.
Qed.

Lemma normal_lindenbaum_step_decides :
  forall Ax Gamma p,
    normal_lindenbaum_step Ax Gamma p p \/
    normal_lindenbaum_step Ax Gamma p (Neg p).
Proof.
  intros Ax Gamma p. unfold normal_lindenbaum_step.
  destruct (excluded_middle_informative
    (normal_theory_consistent Ax (theory_insert Gamma p))).
  - left. now left.
  - right. now left.
Qed.

Lemma normal_lindenbaum_step_consistent :
  forall Ax Gamma p,
    normal_theory_consistent Ax Gamma ->
    normal_theory_consistent Ax (normal_lindenbaum_step Ax Gamma p).
Proof.
  intros Ax Gamma p Hconsistent. unfold normal_lindenbaum_step.
  destruct (excluded_middle_informative
    (normal_theory_consistent Ax (theory_insert Gamma p))) as [Hpos | Hpos].
  - exact Hpos.
  - apply (proj2 (normal_theory_consistent_insert_neg_iff Ax Gamma p)).
    intro Hp.
    assert (Hneg : normal_derives Ax Gamma (Neg p)).
    { apply NNPP. intro Hnotneg. apply Hpos.
      apply (proj2 (normal_theory_consistent_insert_iff Ax Gamma p)).
      exact Hnotneg. }
    apply Hconsistent. eapply ND_mp; [exact Hneg | exact Hp].
Qed.

Fixpoint normal_lindenbaum_chain Ax (Gamma : theory nat) (n : nat)
    : theory nat :=
  match n with
  | 0 => Gamma
  | S k => normal_lindenbaum_step Ax (normal_lindenbaum_chain Ax Gamma k)
             (modal_formula_enum k)
  end.

Lemma normal_lindenbaum_chain_included_succ :
  forall Ax Gamma n,
    theory_included (normal_lindenbaum_chain Ax Gamma n)
      (normal_lindenbaum_chain Ax Gamma (S n)).
Proof. intros; simpl; apply normal_lindenbaum_step_includes. Qed.

Lemma normal_lindenbaum_chain_included_le :
  forall Ax Gamma m n,
    m <= n ->
    theory_included (normal_lindenbaum_chain Ax Gamma m)
      (normal_lindenbaum_chain Ax Gamma n).
Proof.
  intros Ax Gamma m n Hmn; induction Hmn.
  - intros p Hp; exact Hp.
  - intros p Hp.
    apply normal_lindenbaum_chain_included_succ.
    now apply IHHmn.
Qed.

Lemma normal_lindenbaum_chain_consistent :
  forall Ax Gamma,
    normal_theory_consistent Ax Gamma ->
    forall n, normal_theory_consistent Ax
      (normal_lindenbaum_chain Ax Gamma n).
Proof.
  intros Ax Gamma Hconsistent n; induction n as [|n IH]; simpl.
  - exact Hconsistent.
  - now apply normal_lindenbaum_step_consistent.
Qed.

Definition normal_lindenbaum_limit Ax (Gamma : theory nat) : theory nat :=
  fun p => exists n, normal_lindenbaum_chain Ax Gamma n p.

Lemma normal_lindenbaum_limit_includes :
  forall Ax Gamma,
    theory_included Gamma (normal_lindenbaum_limit Ax Gamma).
Proof. intros Ax Gamma p Hp. exists 0. exact Hp. Qed.

Lemma normal_lindenbaum_limit_complete :
  forall Ax Gamma p,
    normal_lindenbaum_limit Ax Gamma p \/
    normal_lindenbaum_limit Ax Gamma (Neg p).
Proof.
  intros Ax Gamma p.
  destruct (modal_formula_enum_surjective p) as [n Henum].
  destruct (normal_lindenbaum_step_decides Ax
    (normal_lindenbaum_chain Ax Gamma n) (modal_formula_enum n)) as [H | H].
  - left. exists (S n). simpl. now rewrite <- Henum.
  - right. exists (S n). simpl. now rewrite <- Henum.
Qed.

Lemma normal_derives_lindenbaum_limit_stage :
  forall Ax Gamma p,
    normal_derives Ax (normal_lindenbaum_limit Ax Gamma) p ->
    exists n, normal_derives Ax (normal_lindenbaum_chain Ax Gamma n) p.
Proof.
  intros Ax Gamma p Hder.
  induction Hder as [p Hp | p Hp | p q Hpq IHpq Hp IHp].
  - destruct Hp as [n Hp]. exists n. now apply ND_assumption.
  - exists 0. now apply ND_theorem.
  - destruct IHpq as [n Hpq_stage]. destruct IHp as [m Hp_stage].
    exists (n + m). eapply ND_mp.
    + eapply normal_derives_weaken; [|exact Hpq_stage].
      apply normal_lindenbaum_chain_included_le. lia.
    + eapply normal_derives_weaken; [|exact Hp_stage].
      apply normal_lindenbaum_chain_included_le. lia.
Qed.

Lemma normal_lindenbaum_limit_consistent :
  forall Ax Gamma,
    normal_theory_consistent Ax Gamma ->
    normal_theory_consistent Ax (normal_lindenbaum_limit Ax Gamma).
Proof.
  intros Ax Gamma Hconsistent Hbottom.
  destruct (normal_derives_lindenbaum_limit_stage Hbottom) as [n Hstage].
  exact ((@normal_lindenbaum_chain_consistent Ax Gamma Hconsistent n) Hstage).
Qed.

Record normal_maximal_consistent_theory (Ax : modal_axiom_schema) : Type := {
  normal_mct_carrier : theory nat;
  normal_mct_consistent : normal_theory_consistent Ax normal_mct_carrier;
  normal_mct_complete : forall p,
    normal_mct_carrier p \/ normal_mct_carrier (Neg p)
}.

Definition normal_mct_mem {Ax}
    (M : normal_maximal_consistent_theory Ax) (p : formula nat) : Prop :=
  normal_mct_carrier M p.

Theorem normal_lindenbaum_extension :
  forall Ax Gamma,
    normal_theory_consistent Ax Gamma ->
    exists M : normal_maximal_consistent_theory Ax,
      theory_included Gamma (normal_mct_mem M).
Proof.
  intros Ax Gamma Hconsistent.
  exists {| normal_mct_carrier := normal_lindenbaum_limit Ax Gamma;
            normal_mct_consistent :=
              normal_lindenbaum_limit_consistent Hconsistent;
            normal_mct_complete :=
              normal_lindenbaum_limit_complete Ax Gamma |}.
  apply normal_lindenbaum_limit_includes.
Qed.

Lemma normal_mct_not_both :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M p -> normal_mct_mem M (Neg p) -> False.
Proof.
  intros Ax M p Hp Hneg. apply (@normal_mct_consistent Ax M).
  eapply ND_mp; apply ND_assumption; eauto.
Qed.

Lemma normal_mct_bottom_absent :
  forall Ax (M : normal_maximal_consistent_theory Ax),
    ~ normal_mct_mem M Bottom.
Proof.
  intros Ax M Hbottom. apply (@normal_mct_consistent Ax M).
  now apply ND_assumption.
Qed.

Lemma normal_mct_neg_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Neg p) <-> ~ normal_mct_mem M p.
Proof.
  intros Ax M p; split.
  - intros Hneg Hp. exact (@normal_mct_not_both Ax M p Hp Hneg).
  - intro Hnot. destruct (@normal_mct_complete Ax M p) as [Hp | Hneg].
    + contradiction.
    + exact Hneg.
Qed.

Lemma normal_mct_derivable_mem :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_derives Ax (normal_mct_mem M) p -> normal_mct_mem M p.
Proof.
  intros Ax M p Hder.
  destruct (@normal_mct_complete Ax M p) as [Hp | Hneg]; [exact Hp |].
  exfalso. apply (@normal_mct_consistent Ax M).
  eapply ND_mp; [apply ND_assumption; exact Hneg | exact Hder].
Qed.

Lemma normal_proves_neg_imply :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp (Neg p) (Imp p q)).
Proof.
  intros Ax p q.
  apply (proj1 (normal_derives_empty_iff Ax
    (Imp (Neg p) (Imp p q)))).
  apply normal_derives_deduction.
  apply normal_derives_deduction.
  apply normal_derives_ex_falso.
  eapply ND_mp.
  - apply ND_assumption. right. now left.
  - apply ND_assumption. now left.
Qed.

Lemma normal_mct_imp_iff :
  forall Ax (M : normal_maximal_consistent_theory Ax) p q,
    normal_mct_mem M (Imp p q) <->
    (normal_mct_mem M p -> normal_mct_mem M q).
Proof.
  intros Ax M p q; split.
  - intros Himp Hp. apply normal_mct_derivable_mem.
    eapply ND_mp; apply ND_assumption; eauto.
  - intro Hpq. destruct (@normal_mct_complete Ax M p) as [Hp | Hneg].
    + apply normal_mct_derivable_mem. eapply ND_mp.
      * apply ND_theorem. exact (Np_imply_K q p).
      * apply ND_assumption. exact (Hpq Hp).
    + apply normal_mct_derivable_mem. eapply ND_mp.
      * apply ND_theorem. apply normal_proves_neg_imply.
      * apply ND_assumption. exact Hneg.
Qed.

(** * Generic canonical model *)

Definition normal_canonical_relation Ax
    (M N : normal_maximal_consistent_theory Ax) : Prop :=
  forall p, normal_mct_mem M (Box p) -> normal_mct_mem N p.

Definition normal_canonical_frame Ax : frame :=
  {| World := normal_maximal_consistent_theory Ax;
     Rel := @normal_canonical_relation Ax |}.

Definition normal_canonical_valuation Ax :
    valuation nat (normal_canonical_frame Ax) :=
  fun a M => normal_mct_mem M (Atom a).

Theorem normal_canonical_successor_of_neg_box :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Neg (Box p)) ->
    exists N : normal_maximal_consistent_theory Ax,
      @normal_canonical_relation Ax M N /\ normal_mct_mem N (Neg p).
Proof.
  intros Ax M p Hnegbox.
  pose (Gamma := theory_insert
    (fun q => normal_mct_mem M (Box q)) (Neg p)).
  assert (Hconsistent : normal_theory_consistent Ax Gamma).
  { unfold Gamma.
    apply (proj2 (normal_theory_consistent_insert_neg_iff Ax
      (fun q => normal_mct_mem M (Box q)) p)).
    intro Hp.
    pose proof (normal_derives_box_from_unboxed Hp) as Hbox.
    pose proof (@normal_mct_derivable_mem Ax M (Box p) Hbox) as Hboxmem.
    exact (@normal_mct_not_both Ax M (Box p) Hboxmem Hnegbox). }
  destruct (normal_lindenbaum_extension Hconsistent) as [N Hinclude].
  exists N; split.
  - intros q Hbox. apply Hinclude. right. exact Hbox.
  - apply Hinclude. now left.
Qed.

Theorem normal_canonical_truth_lemma :
  forall Ax (p : formula nat),
    forall M : normal_maximal_consistent_theory Ax,
      normal_mct_mem M p <->
      satisfies (normal_canonical_frame Ax)
        (@normal_canonical_valuation Ax) M p.
Proof.
  intros Ax p; induction p as [a | | p IHp q IHq | p IHp]; intro M.
  - reflexivity.
  - split.
    + intro H. exact (@normal_mct_bottom_absent Ax M H).
    + intro Hfalse. contradiction.
  - change (normal_mct_mem M (Imp p q) <->
      (satisfies (normal_canonical_frame Ax)
         (@normal_canonical_valuation Ax) M p ->
       satisfies (normal_canonical_frame Ax)
         (@normal_canonical_valuation Ax) M q)).
    rewrite <- (IHp M), <- (IHq M). apply normal_mct_imp_iff.
  - change (normal_mct_mem M (Box p) <->
      forall N, @normal_canonical_relation Ax M N ->
        satisfies (normal_canonical_frame Ax)
          (@normal_canonical_valuation Ax) N p).
    split.
    + intros Hbox N HMN. apply (proj1 (IHp N)). exact (HMN p Hbox).
    + intro Hsemantic.
      destruct (@normal_mct_complete Ax M (Box p)) as [Hbox | Hneg].
      * exact Hbox.
      * destruct (@normal_canonical_successor_of_neg_box Ax M p Hneg)
          as [N [HMN Hnegp]].
        assert (Hp : normal_mct_mem N p).
        { apply (proj2 (IHp N)). exact (Hsemantic N HMN). }
        exfalso. exact (@normal_mct_not_both Ax N p Hp Hnegp).
Qed.

Theorem normal_canonical_countermodel :
  forall Ax,
    normal_system_consistent Ax ->
    forall p : formula nat,
      ~ normal_proves Ax p ->
      exists M : normal_maximal_consistent_theory Ax,
        ~ satisfies (normal_canonical_frame Ax)
            (@normal_canonical_valuation Ax) M p.
Proof.
  intros Ax Hsystem p Hnot.
  assert (Hempty : normal_theory_consistent Ax empty_theory).
  { apply (proj2 (normal_empty_theory_consistent_iff Ax)). exact Hsystem. }
  assert (Hnot_empty : ~ normal_derives Ax empty_theory p).
  { intro Hder. apply Hnot. now apply (proj1 (normal_derives_empty_iff Ax p)). }
  assert (Hconsistent : normal_theory_consistent Ax
      (theory_insert empty_theory (Neg p))).
  { apply (proj2 (normal_theory_consistent_insert_neg_iff Ax
      empty_theory p)). exact Hnot_empty. }
  destruct (normal_lindenbaum_extension Hconsistent) as [M Hinclude].
  exists M. intro Hsat. apply (@normal_mct_not_both Ax M p).
  - apply (proj2 (@normal_canonical_truth_lemma Ax p M)). exact Hsat.
  - apply Hinclude. now left.
Qed.

Definition normal_valid_on_class
    (C : frame -> Prop) (p : formula nat) : Prop :=
  forall F, C F -> valid F p.

Theorem normal_complete_of_canonical_frame :
  forall Ax (C : frame -> Prop),
    normal_system_consistent Ax ->
    C (normal_canonical_frame Ax) ->
    forall p, normal_valid_on_class C p -> normal_proves Ax p.
Proof.
  intros Ax C Hsystem Hcanonical p Hvalid.
  apply NNPP. intro Hnot.
  destruct (@normal_canonical_countermodel Ax Hsystem p Hnot)
    as [M Hcounter].
  apply Hcounter. exact (Hvalid _ Hcanonical _ M).
Qed.

(** * KT, K4, and S4 canonical frames *)

Lemma KT_canonical_frame_reflexive :
  frame_reflexive (normal_canonical_frame schema_T).
Proof.
  intros M p Hbox. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma K4_canonical_frame_transitive :
  frame_transitive (normal_canonical_frame schema_Four).
Proof.
  intros M N O HMN HNO p Hbox.
  apply HNO. apply HMN. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma S4_canonical_frame_reflexive :
  frame_reflexive (normal_canonical_frame S4_schema).
Proof.
  intros M p Hbox. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. left. exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma S4_canonical_frame_transitive :
  frame_transitive (normal_canonical_frame S4_schema).
Proof.
  intros M N O HMN HNO p Hbox.
  apply HNO. apply HMN. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. right. exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Theorem KT_complete :
  forall p : formula nat,
    normal_valid_on_class frame_reflexive p -> KT_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_T) (C := frame_reflexive)).
  - exact (@KT_is_consistent nat).
  - exact KT_canonical_frame_reflexive.
Qed.

Theorem K4_complete :
  forall p : formula nat,
    normal_valid_on_class frame_transitive p -> K4_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_Four) (C := frame_transitive)).
  - exact (@K4_is_consistent nat).
  - exact K4_canonical_frame_transitive.
Qed.

Definition frame_preorder_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F.

Definition K4_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_transitive F.

Definition S4_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_preorder_class F.

Theorem S4_complete :
  forall p : formula nat,
    normal_valid_on_class frame_preorder_class p -> S4_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := S4_schema) (C := frame_preorder_class)).
  - exact (@S4_is_consistent nat).
  - split.
    + exact S4_canonical_frame_reflexive.
    + exact S4_canonical_frame_transitive.
Qed.

Theorem KT_sound_complete :
  forall p : formula nat,
    KT_proves p <-> normal_valid_on_class frame_reflexive p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply KT_proves_sound_on_reflexive_frame.
  - apply KT_complete.
Qed.

Theorem K4_sound_complete :
  forall p : formula nat,
    K4_proves p <-> normal_valid_on_class frame_transitive p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply K4_proves_sound_on_transitive_frame.
  - apply K4_complete.
Qed.

Theorem S4_sound_complete :
  forall p : formula nat,
    S4_proves p <-> normal_valid_on_class frame_preorder_class p.
Proof.
  intro p; split.
  - intros Hp F [HR HT]. now apply S4_proves_sound_on_preorder_frame.
  - apply S4_complete.
Qed.

(** * Finite-frame completeness for K4 and S4 *)

Theorem K4_finite_complete :
  forall p : formula nat,
    normal_valid_on_class K4_finite_frame_class p -> K4_proves p.
Proof.
  intros p Hfinite. apply K4_complete.
  intros F HT V w.
  pose (Q := @finest_tc_filtered_frame nat F V p).
  pose (VQ := @finest_tc_filtered_valuation nat F V p).
  assert (HsatQ : satisfies Q VQ
    (@profile_class nat F V p w) p).
  {
    apply (Hfinite Q). split.
    - unfold Q. apply finest_tc_filtered_frame_finite.
    - unfold Q. apply finest_tc_is_transitive.
  }
  apply (proj1 (@finest_tc_filtration_truth_at_class
    nat F V p HT p (subformulas_self p) w)).
  exact HsatQ.
Qed.

Theorem K4_finite_sound :
  forall p : formula nat,
    K4_proves p -> normal_valid_on_class K4_finite_frame_class p.
Proof.
  intros p Hp F [_ HT].
  now apply K4_proves_sound_on_transitive_frame.
Qed.

Theorem K4_finite_sound_complete :
  forall p : formula nat,
    K4_proves p <-> normal_valid_on_class K4_finite_frame_class p.
Proof.
  intro p; split.
  - apply K4_finite_sound.
  - apply K4_finite_complete.
Qed.

Theorem S4_finite_complete :
  forall p : formula nat,
    normal_valid_on_class S4_finite_frame_class p -> S4_proves p.
Proof.
  intros p Hfinite. apply S4_complete.
  intros F [HR HT] V w.
  pose (Q := @finest_tc_filtered_frame nat F V p).
  pose (VQ := @finest_tc_filtered_valuation nat F V p).
  assert (HsatQ : satisfies Q VQ
    (@profile_class nat F V p w) p).
  {
    apply (Hfinite Q). split.
    - unfold Q. apply finest_tc_filtered_frame_finite.
    - split.
      + unfold Q. now apply finest_tc_preserves_reflexive.
      + unfold Q. apply finest_tc_is_transitive.
  }
  apply (proj1 (@finest_tc_filtration_truth_at_class
    nat F V p HT p (subformulas_self p) w)).
  exact HsatQ.
Qed.

Theorem S4_finite_sound :
  forall p : formula nat,
    S4_proves p -> normal_valid_on_class S4_finite_frame_class p.
Proof.
  intros p Hp F [_ [HR HT]].
  now apply S4_proves_sound_on_preorder_frame.
Qed.

Theorem S4_finite_sound_complete :
  forall p : formula nat,
    S4_proves p <-> normal_valid_on_class S4_finite_frame_class p.
Proof.
  intro p; split.
  - apply S4_finite_sound.
  - apply S4_finite_complete.
Qed.

(** * Strict inclusions witnessed by small frames *)

Definition normal_strictly_weaker
    (P Q : formula nat -> Prop) : Prop :=
  (forall p, P p -> Q p) /\ exists p, Q p /\ ~ P p.

Inductive three_world : Type := W0 | W1 | W2.

Inductive kt_sink_world : Type := KT0 | KT1.

Definition kt_sink_frame : frame :=
  {| World := kt_sink_world;
     Rel := fun _ y => y = KT1 |}.

Lemma kt_sink_serial : frame_serial kt_sink_frame.
Proof. intro x. exists KT1. reflexivity. Qed.

Lemma kt_sink_not_reflexive : ~ frame_reflexive kt_sink_frame.
Proof.
  intro HR. specialize (HR KT0). discriminate.
Qed.

Definition three_chain_relation (x y : three_world) : Prop :=
  (x = W0 /\ y = W1) \/ (x = W1 /\ y = W2).

Definition three_chain_frame : frame :=
  {| World := three_world; Rel := three_chain_relation |}.

Lemma three_chain_not_transitive : ~ frame_transitive three_chain_frame.
Proof.
  intro Htrans.
  specialize (Htrans W0 W1 W2 (or_introl (conj eq_refl eq_refl))
    (or_intror (conj eq_refl eq_refl))).
  destruct Htrans as [[_ H] | [H _]]; discriminate.
Qed.

Definition reflexive_three_chain_frame : frame :=
  {| World := three_world;
     Rel := fun x y => x = y \/ three_chain_relation x y |}.

Lemma reflexive_three_chain_reflexive :
  frame_reflexive reflexive_three_chain_frame.
Proof. intro x. now left. Qed.

Lemma reflexive_three_chain_not_transitive :
  ~ frame_transitive reflexive_three_chain_frame.
Proof.
  intro Htrans.
  specialize (Htrans W0 W1 W2
    (or_intror (or_introl (conj eq_refl eq_refl)))
    (or_intror (or_intror (conj eq_refl eq_refl)))).
  destruct Htrans as [H | [[_ H] | [H _]]]; discriminate.
Qed.

Theorem K_strictly_weaker_KT :
  normal_strictly_weaker K_normal_proves KT_proves.
Proof.
  split.
  - apply K_weaker_than_normal.
  - exists (T (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HK. apply (proj1 (empty_normal_proves_iff_K _)) in HK.
      pose proof (K_proves_sound_on_frame
        (F := irreflexive_singleton_frame) HK) as Hvalid.
      pose proof (proj1 (valid_T_iff_reflexive
        irreflexive_singleton_frame) Hvalid) as Hrefl.
      exact (Hrefl tt).
Qed.

Theorem KD_weaker_than_KT :
  forall p : formula nat, KD_proves p -> KT_proves p.
Proof.
  intros p Hp. apply KT_complete.
  intros F HR.
  apply KD_proves_sound_on_serial_frame.
  - intro x. exists x. apply HR.
  - exact Hp.
Qed.

Theorem KD_strictly_weaker_KT :
  normal_strictly_weaker KD_proves KT_proves.
Proof.
  split.
  - exact KD_weaker_than_KT.
  - exists (T (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HKD.
      pose proof (KD_proves_sound_on_serial_frame kt_sink_serial HKD)
        as Hvalid.
      apply kt_sink_not_reflexive.
      now apply (proj1 (valid_T_iff_reflexive kt_sink_frame)).
Qed.

Theorem K_strictly_weaker_K4 :
  normal_strictly_weaker K_normal_proves K4_proves.
Proof.
  split.
  - apply K_weaker_than_normal.
  - exists (Four (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HK. apply (proj1 (empty_normal_proves_iff_K _)) in HK.
      pose proof (K_proves_sound_on_frame (F := three_chain_frame) HK)
        as Hvalid.
      apply three_chain_not_transitive.
      now apply (proj1 (valid_Four_iff_transitive three_chain_frame)).
Qed.

Theorem KT_strictly_weaker_S4 :
  normal_strictly_weaker KT_proves S4_proves.
Proof.
  split.
  - apply KT_weaker_than_S4.
  - exists (Four (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKT.
      pose proof (KT_proves_sound_on_reflexive_frame
        reflexive_three_chain_reflexive HKT) as Hvalid.
      apply reflexive_three_chain_not_transitive.
      now apply (proj1 (valid_Four_iff_transitive
        reflexive_three_chain_frame)).
Qed.

Theorem K4_strictly_weaker_S4 :
  normal_strictly_weaker K4_proves S4_proves.
Proof.
  split.
  - apply K4_weaker_than_S4.
  - exists (T (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HK4.
      pose proof (K4_proves_sound_on_transitive_frame
        irreflexive_singleton_transitive HK4) as Hvalid.
      pose proof (proj1 (valid_T_iff_reflexive
        irreflexive_singleton_frame) Hvalid) as Hrefl.
      exact (Hrefl tt).
Qed.
