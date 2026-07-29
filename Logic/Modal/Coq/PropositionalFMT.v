(** Formula-indexed Kripke semantics.

    This ports Foundation/Propositional/FMT/Basic and the elementary part of
    FMT/Axiom/Ser. Accessibility is indexed by the entire implication being
    evaluated; roots see every world at every formula. Repeated validity and
    countermodel arguments are factored through the same model/frame/class
    hierarchy used elsewhere in this port. *)

From Stdlib Require Import Logic.Classical_Prop Logic.Classical_Pred_Type.
From FoundationModal Require Import PropositionalFormula PropositionalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.

Record fmt_frame : Type := {
  fmt_world : Type;
  fmt_access : pformula nat -> fmt_world -> fmt_world -> Prop;
  fmt_root : fmt_world;
  fmt_root_access : forall p w, fmt_access p fmt_root w
}.

Arguments fmt_world _ : clear implicits.
Arguments fmt_access _ _ _ _ : clear implicits.
Arguments fmt_root _ : clear implicits.

Definition fmt_valuation (F : fmt_frame) := nat -> fmt_world F -> Prop.

Record fmt_model : Type := {
  fmt_model_frame : fmt_frame;
  fmt_model_valuation : fmt_valuation fmt_model_frame
}.

Fixpoint fmt_forces (M : fmt_model) (w : fmt_world (fmt_model_frame M))
    (p : pformula nat) : Prop :=
  match p with
  | PAtom a => @fmt_model_valuation M a w
  | PFalsum => False
  | PAnd q r => @fmt_forces M w q /\ @fmt_forces M w r
  | POr q r => @fmt_forces M w q \/ @fmt_forces M w r
  | PImp q r => forall v,
      fmt_access (fmt_model_frame M) (PImp q r) w v ->
      @fmt_forces M v q -> @fmt_forces M v r
  end.

Arguments fmt_forces M w p : clear implicits.

Lemma fmt_forces_atom : forall M w a,
  fmt_forces M w (PAtom a) <-> @fmt_model_valuation M a w.
Proof. reflexivity. Qed.

Lemma fmt_forces_bottom : forall M w, ~ fmt_forces M w PFalsum.
Proof. firstorder. Qed.

Lemma fmt_forces_top : forall M w, fmt_forces M w ptop.
Proof. firstorder. Qed.

Lemma fmt_forces_and : forall M w p q,
  fmt_forces M w (PAnd p q) <-> fmt_forces M w p /\ fmt_forces M w q.
Proof. reflexivity. Qed.

Lemma fmt_not_forces_and : forall M w p q,
  ~ fmt_forces M w (PAnd p q) <->
  ~ fmt_forces M w p \/ ~ fmt_forces M w q.
Proof. intros; cbn; destruct (classic (fmt_forces M w p)); tauto. Qed.

Lemma fmt_forces_or : forall M w p q,
  fmt_forces M w (POr p q) <-> fmt_forces M w p \/ fmt_forces M w q.
Proof. reflexivity. Qed.

Lemma fmt_not_forces_or : forall M w p q,
  ~ fmt_forces M w (POr p q) <->
  ~ fmt_forces M w p /\ ~ fmt_forces M w q.
Proof. intros; cbn; tauto. Qed.

Lemma fmt_forces_imp : forall M w p q,
  fmt_forces M w (PImp p q) <->
  (forall v, fmt_access (fmt_model_frame M) (PImp p q) w v ->
    fmt_forces M v p -> fmt_forces M v q).
Proof. reflexivity. Qed.

Lemma fmt_not_forces_imp : forall M w p q,
  ~ fmt_forces M w (PImp p q) <->
  exists v, fmt_access (fmt_model_frame M) (PImp p q) w v /\
    fmt_forces M v p /\ ~ fmt_forces M v q.
Proof.
  intros M w p q; cbn; split.
  - intro H. apply not_all_ex_not in H. destruct H as [v Hv].
    exists v. destruct (classic (fmt_access (fmt_model_frame M)
      (PImp p q) w v)); destruct (classic (fmt_forces M v p)); tauto.
  - firstorder.
Qed.

Lemma fmt_forces_neg : forall M w p,
  fmt_forces M w (pneg p) <->
  (forall v, fmt_access (fmt_model_frame M) (pneg p) w v ->
    ~ fmt_forces M v p).
Proof. reflexivity. Qed.

Lemma fmt_not_forces_neg : forall M w p,
  ~ fmt_forces M w (pneg p) <->
  exists v, fmt_access (fmt_model_frame M) (pneg p) w v /\
    fmt_forces M v p.
Proof. intros; unfold pneg; rewrite fmt_not_forces_imp; cbn; firstorder. Qed.

Definition fmt_iff (p q : pformula nat) :=
  PAnd (PImp p q) (PImp q p).

Lemma fmt_forces_iff : forall M w p q,
  fmt_forces M w (fmt_iff p q) <->
  ((forall v, fmt_access (fmt_model_frame M) (PImp p q) w v ->
      fmt_forces M v p -> fmt_forces M v q) /\
   (forall v, fmt_access (fmt_model_frame M) (PImp q p) w v ->
      fmt_forces M v q -> fmt_forces M v p)).
Proof. reflexivity. Qed.

Lemma fmt_not_forces_iff : forall M w p q,
  ~ fmt_forces M w (fmt_iff p q) <->
  (exists v, fmt_access (fmt_model_frame M) (PImp p q) w v /\
    fmt_forces M v p /\ ~ fmt_forces M v q) \/
  (exists v, fmt_access (fmt_model_frame M) (PImp q p) w v /\
    fmt_forces M v q /\ ~ fmt_forces M v p).
Proof. intros; unfold fmt_iff; rewrite fmt_not_forces_and; now rewrite !fmt_not_forces_imp. Qed.

Definition fmt_model_valid (M : fmt_model) (p : pformula nat) :=
  forall w, fmt_forces M w p.

Definition fmt_frame_valid (F : fmt_frame) (p : pformula nat) :=
  forall V, fmt_model_valid {| fmt_model_frame := F;
    fmt_model_valuation := V |} p.

Definition fmt_frame_class_valid (C : fmt_frame -> Prop) p :=
  forall F, C F -> fmt_frame_valid F p.

Definition fmt_model_class_valid (C : fmt_model -> Prop) p :=
  forall M, C M -> fmt_model_valid M p.

Lemma fmt_model_valid_top : forall M, fmt_model_valid M ptop.
Proof. intros M w; apply fmt_forces_top. Qed.

Lemma fmt_model_not_valid_bottom : forall M, ~ fmt_model_valid M PFalsum.
Proof.
  intros M H. exact ((@fmt_forces_bottom M (fmt_root (fmt_model_frame M)))
    (H (fmt_root (fmt_model_frame M)))).
Qed.

Lemma fmt_model_valid_at_root : forall M p,
  fmt_model_valid M p -> fmt_forces M (fmt_root (fmt_model_frame M)) p.
Proof. intros M p H; apply H. Qed.

Lemma fmt_frame_valid_top : forall F, fmt_frame_valid F ptop.
Proof. intros F V; apply fmt_model_valid_top. Qed.

Lemma fmt_frame_not_valid_bottom : forall F, ~ fmt_frame_valid F PFalsum.
Proof.
  intros F H. exact (@fmt_model_not_valid_bottom
    {| fmt_model_frame := F; fmt_model_valuation := fun _ _ => False |}
    (H (fun _ _ => False))).
Qed.

Lemma fmt_model_not_valid_iff : forall M p,
  ~ fmt_model_valid M p <-> exists w, ~ fmt_forces M w p.
Proof. intros; unfold fmt_model_valid; split; [apply not_all_ex_not | firstorder]. Qed.

Lemma fmt_frame_not_valid_iff : forall F p,
  ~ fmt_frame_valid F p <-> exists V, ~ fmt_model_valid
    {| fmt_model_frame := F; fmt_model_valuation := V |} p.
Proof. intros; unfold fmt_frame_valid; split; [apply not_all_ex_not | firstorder]. Qed.

Lemma fmt_frame_not_valid_iff_world : forall F p,
  ~ fmt_frame_valid F p <-> exists V w,
    ~ fmt_forces {| fmt_model_frame := F; fmt_model_valuation := V |} w p.
Proof.
  intros; rewrite fmt_frame_not_valid_iff; split.
  - intros [V H]; apply fmt_model_not_valid_iff in H; firstorder.
  - intros [V [w H]]; exists V; apply fmt_model_not_valid_iff; firstorder.
Qed.

Lemma fmt_frame_class_not_valid_iff_frame : forall C p,
  ~ fmt_frame_class_valid C p <-> exists F, C F /\ ~ fmt_frame_valid F p.
Proof.
  intros; unfold fmt_frame_class_valid; split.
  - intro H; apply not_all_ex_not in H; destruct H as [F HF].
    exists F; destruct (classic (C F)); tauto.
  - firstorder.
Qed.

Lemma fmt_frame_class_not_valid_iff_model_world : forall C p,
  ~ fmt_frame_class_valid C p <-> exists M w,
    C (fmt_model_frame M) /\ ~ fmt_forces M w p.
Proof.
  intros; rewrite fmt_frame_class_not_valid_iff_frame; split.
  - intros [F [HF H]]. apply fmt_frame_not_valid_iff_world in H.
    destruct H as [V [w Hw]]. now exists
      {| fmt_model_frame := F; fmt_model_valuation := V |}, w.
  - intros [[F V] [w [HF Hw]]]. exists F; split; [exact HF |].
    apply fmt_frame_not_valid_iff_world. now exists V, w.
Qed.

Lemma fmt_frame_class_not_valid_iff_model : forall C p,
  ~ fmt_frame_class_valid C p <-> exists M,
    C (fmt_model_frame M) /\ ~ fmt_model_valid M p.
Proof.
  intros C p; rewrite fmt_frame_class_not_valid_iff_frame; split.
  - intros [F [HC H]]. apply fmt_frame_not_valid_iff in H.
    destruct H as [V HV].
    now exists {| fmt_model_frame := F; fmt_model_valuation := V |}.
  - intros [[F V] [HC H]]. exists F; split; [exact HC |].
    apply fmt_frame_not_valid_iff. now exists V.
Qed.

Lemma fmt_model_class_not_valid_iff_model : forall C p,
  ~ fmt_model_class_valid C p <-> exists M, C M /\ ~ fmt_model_valid M p.
Proof.
  intros C p; unfold fmt_model_class_valid; split.
  - intro H. apply not_all_ex_not in H. destruct H as [M HM].
    exists M. destruct (classic (C M)); tauto.
  - firstorder.
Qed.

Lemma fmt_model_class_not_valid_iff_world : forall C p,
  ~ fmt_model_class_valid C p <-> exists M w, C M /\ ~ fmt_forces M w p.
Proof.
  intros; unfold fmt_model_class_valid; split.
  - intro H; apply not_all_ex_not in H; destruct H as [M HM].
    destruct (classic (C M)) as [HC|HC]; [|tauto].
    assert (Hworld : ~ forall w, fmt_forces M w p).
    { intro Hall. apply HM. intros _. exact Hall. }
    apply not_all_ex_not in Hworld. destruct Hworld as [w Hw].
    now exists M, w.
  - intros [M [w [HC Hw]]] Hall. apply Hw. exact (Hall M HC w).
Qed.

Definition fmt_collect_or_and (p q r : pformula nat) :=
  PImp (PAnd (POr p q) (POr p r)) (POr p (PAnd q r)).

Lemma fmt_valid_and1 : forall M p q, fmt_model_valid M (ph_axiom_and1 p q).
Proof. firstorder. Qed.
Lemma fmt_valid_and2 : forall M p q, fmt_model_valid M (ph_axiom_and2 p q).
Proof. firstorder. Qed.
Lemma fmt_valid_or1 : forall M p q, fmt_model_valid M (ph_axiom_or1 p q).
Proof. intros M p q x y _ Hp; now left. Qed.
Lemma fmt_valid_or2 : forall M p q, fmt_model_valid M (ph_axiom_or2 p q).
Proof. intros M p q x y _ Hq; now right. Qed.
Lemma fmt_valid_distribute_and_or : forall M p q r,
  fmt_model_valid M (PImp (PAnd p (POr q r))
    (POr (PAnd p q) (PAnd p r))).
Proof.
  intros M p q r x y _ [Hp [Hq|Hr]].
  - left; split; assumption.
  - right; split; assumption.
Qed.
Lemma fmt_valid_collect_or_and : forall M p q r,
  fmt_model_valid M (fmt_collect_or_and p q r).
Proof.
  intros M p q r x y _ [[Hp|Hq] [Hp'|Hr]].
  - now left.
  - now left.
  - now left.
  - right; now split.
Qed.
Lemma fmt_valid_identity : forall M p, fmt_model_valid M (PImp p p).
Proof. firstorder. Qed.
Lemma fmt_valid_efq : forall M p, fmt_model_valid M (ph_axiom_efq p).
Proof. firstorder. Qed.

Lemma fmt_valid_mdp : forall M p q,
  fmt_model_valid M (PImp p q) -> fmt_model_valid M p -> fmt_model_valid M q.
Proof.
  intros M p q Hpq Hp x. exact (Hpq (fmt_root (fmt_model_frame M)) x
    (@fmt_root_access (fmt_model_frame M) (PImp p q) x) (Hp x)).
Qed.
Lemma fmt_valid_afortiori : forall M p q,
  fmt_model_valid M p -> fmt_model_valid M (PImp q p).
Proof. firstorder. Qed.
Lemma fmt_valid_and_rule : forall M p q,
  fmt_model_valid M p -> fmt_model_valid M q -> fmt_model_valid M (PAnd p q).
Proof. firstorder. Qed.
Lemma fmt_valid_rule_D : forall M p q r,
  fmt_model_valid M (PImp p r) -> fmt_model_valid M (PImp q r) ->
  fmt_model_valid M (PImp (POr p q) r).
Proof.
  intros M p q r Hpr Hqr x y _ [Hp|Hq].
  - exact (Hpr (fmt_root _) y (@fmt_root_access _ (PImp p r) y) Hp).
  - exact (Hqr (fmt_root _) y (@fmt_root_access _ (PImp q r) y) Hq).
Qed.
Lemma fmt_valid_rule_C : forall M p q r,
  fmt_model_valid M (PImp p q) -> fmt_model_valid M (PImp p r) ->
  fmt_model_valid M (PImp p (PAnd q r)).
Proof.
  intros M p q r Hpq Hpr x y _ Hp; split.
  - exact (Hpq (fmt_root _) y (@fmt_root_access _ (PImp p q) y) Hp).
  - exact (Hpr (fmt_root _) y (@fmt_root_access _ (PImp p r) y) Hp).
Qed.
Lemma fmt_valid_rule_I : forall M p q r,
  fmt_model_valid M (PImp p q) -> fmt_model_valid M (PImp q r) ->
  fmt_model_valid M (PImp p r).
Proof.
  intros M p q r Hpq Hqr x y _ Hp.
  apply (Hqr (fmt_root _) y (@fmt_root_access _ (PImp q r) y)).
  exact (Hpq (fmt_root _) y (@fmt_root_access _ (PImp p q) y) Hp).
Qed.

Definition fmt_nt_serial (F : fmt_frame) := forall x, exists y,
  fmt_access F (pneg ptop) x y.

Theorem fmt_valid_ser_of_nt_serial : forall F,
  fmt_nt_serial F -> fmt_frame_valid F (pneg (pneg ptop)).
Proof.
  intros F Hser V x y _ Hneg. destruct (Hser y) as [z Ryz].
  exact (Hneg z Ryz
    (@fmt_forces_top {| fmt_model_frame := F; fmt_model_valuation := V |} z)).
Qed.

Theorem fmt_nt_serial_of_valid_neg_top : forall F,
  fmt_frame_valid F (pneg ptop) -> fmt_nt_serial F.
Proof.
  intros F H x. exfalso.
  exact (H (fun _ _ => True) (fmt_root F) x
    (@fmt_root_access F (pneg ptop) x)
    (@fmt_forces_top
      {| fmt_model_frame := F; fmt_model_valuation := fun _ _ => True |} x)).
Qed.

Corollary fmt_valid_ser_of_valid_neg_top : forall F,
  fmt_frame_valid F (pneg ptop) ->
  fmt_frame_valid F (pneg (pneg ptop)).
Proof. intros F H; apply fmt_valid_ser_of_nt_serial, fmt_nt_serial_of_valid_neg_top, H. Qed.
