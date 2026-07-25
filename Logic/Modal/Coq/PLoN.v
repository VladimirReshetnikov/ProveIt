(**
  Formula-indexed relational semantics (PLoN).

  This is an independent Rocq port of
  [Foundation/Modal/PLoN/Basic.lean] at the read-only Foundation revision
  pinned by this repository.  Unlike ordinary Kripke semantics, the
  accessibility relation used to interpret [Box p] is indexed by [p]
  itself.  Consequently necessitation remains sound, while replacement of
  provable equivalents under box need not be sound.

  Foundation assumes that every frame has a nonempty world type.  Recording
  a distinguished world is the constructive Rocq presentation of the same
  invariant; it avoids making a choice merely to refute validity of bottom.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Frames, valuations, and models. *)

Record plon_frame : Type := {
  plon_world : Type;
  plon_rel : formula nat -> plon_world -> plon_world -> Prop;
  plon_default : plon_world
}.

Arguments plon_world _ : clear implicits.
Arguments plon_rel _ _ _ _ : clear implicits.
Arguments plon_default _ : clear implicits.

Definition plon_terminal_frame : plon_frame :=
  {| plon_world := unit;
     plon_rel := fun _ _ _ => True;
     plon_default := tt |}.

Definition plon_frame_class : Type := plon_frame -> Prop.

Definition plon_valuation (F : plon_frame) : Type :=
  plon_world F -> nat -> Prop.

Record plon_model : Type := {
  plon_model_frame : plon_frame;
  plon_model_valuation : plon_valuation plon_model_frame
}.

Arguments plon_model_frame _ : clear implicits.
Arguments plon_model_valuation _ _ _ : clear implicits.

Definition plon_model_on (F : plon_frame) (V : plon_valuation F)
    : plon_model :=
  {| plon_model_frame := F; plon_model_valuation := V |}.

Arguments plon_model_on _ _ : clear implicits.

(** Satisfaction.  The box clause is the characteristic PLoN clause: its
    relation is selected by the formula occurring immediately below box. *)

Fixpoint plon_satisfies (M : plon_model)
    (w : plon_world (plon_model_frame M)) (p : formula nat) : Prop :=
  match p with
  | Atom a => plon_model_valuation M w a
  | Bottom => False
  | Imp q r => @plon_satisfies M w q -> @plon_satisfies M w r
  | Box q => forall u,
      plon_rel (plon_model_frame M) q w u -> @plon_satisfies M u q
  end.

Arguments plon_satisfies _ _ _ : clear implicits.

Definition plon_not_satisfies (M : plon_model)
    (w : plon_world (plon_model_frame M)) (p : formula nat) : Prop :=
  ~ plon_satisfies M w p.

Lemma plon_satisfies_bottom :
  forall M (w : plon_world (plon_model_frame M)),
    ~ plon_satisfies M w Bottom.
Proof. intros; simpl; auto. Qed.

Lemma plon_satisfies_top :
  forall M (w : plon_world (plon_model_frame M)),
    plon_satisfies M w Top.
Proof. intros; simpl; auto. Qed.

Lemma plon_satisfies_imp :
  forall M (w : plon_world (plon_model_frame M)) p q,
    plon_satisfies M w (Imp p q) <->
    (plon_satisfies M w p -> plon_satisfies M w q).
Proof. reflexivity. Qed.

Lemma plon_not_satisfies_imp :
  forall M (w : plon_world (plon_model_frame M)) p q,
    ~ plon_satisfies M w (Imp p q) <->
    plon_satisfies M w p /\ ~ plon_satisfies M w q.
Proof. intros; simpl; tauto. Qed.

Lemma plon_satisfies_or :
  forall M (w : plon_world (plon_model_frame M)) p q,
    plon_satisfies M w (Or p q) <->
    plon_satisfies M w p \/ plon_satisfies M w q.
Proof. intros; unfold Or, Neg; simpl; tauto. Qed.

Lemma plon_not_satisfies_or :
  forall M (w : plon_world (plon_model_frame M)) p q,
    ~ plon_satisfies M w (Or p q) <->
    ~ plon_satisfies M w p /\ ~ plon_satisfies M w q.
Proof. intros; rewrite plon_satisfies_or; tauto. Qed.

Lemma plon_satisfies_and :
  forall M (w : plon_world (plon_model_frame M)) p q,
    plon_satisfies M w (And p q) <->
    plon_satisfies M w p /\ plon_satisfies M w q.
Proof. intros; unfold And, Neg; simpl; tauto. Qed.

Lemma plon_not_satisfies_and :
  forall M (w : plon_world (plon_model_frame M)) p q,
    ~ plon_satisfies M w (And p q) <->
    ~ plon_satisfies M w p \/ ~ plon_satisfies M w q.
Proof. intros; rewrite plon_satisfies_and; tauto. Qed.

Lemma plon_satisfies_neg :
  forall M (w : plon_world (plon_model_frame M)) p,
    plon_satisfies M w (Neg p) <-> ~ plon_satisfies M w p.
Proof. reflexivity. Qed.

Lemma plon_not_satisfies_neg :
  forall M (w : plon_world (plon_model_frame M)) p,
    ~ plon_satisfies M w (Neg p) <-> plon_satisfies M w p.
Proof. intros; simpl; tauto. Qed.

Lemma plon_satisfies_iff :
  forall M (w : plon_world (plon_model_frame M)) p q,
    plon_satisfies M w (Iff p q) <->
    (plon_satisfies M w p <-> plon_satisfies M w q).
Proof.
  intros; unfold Iff; rewrite plon_satisfies_and; simpl; tauto.
Qed.

Lemma plon_not_satisfies_iff :
  forall M (w : plon_world (plon_model_frame M)) p q,
    ~ plon_satisfies M w (Iff p q) <->
    (plon_satisfies M w p /\ ~ plon_satisfies M w q) \/
    (~ plon_satisfies M w p /\ plon_satisfies M w q).
Proof. intros; rewrite plon_satisfies_iff; tauto. Qed.

Lemma plon_satisfies_box :
  forall M (w : plon_world (plon_model_frame M)) p,
    plon_satisfies M w (Box p) <->
    forall u, plon_rel (plon_model_frame M) p w u ->
      plon_satisfies M u p.
Proof. reflexivity. Qed.

Lemma plon_not_satisfies_box :
  forall M (w : plon_world (plon_model_frame M)) p,
    ~ plon_satisfies M w (Box p) <->
    exists u, plon_rel (plon_model_frame M) p w u /\
      ~ plon_satisfies M u p.
Proof.
  intros M w p; split.
  - intro Hbox.
    apply NNPP; intro Hnone.
    apply Hbox; intros u Rwu.
    apply NNPP; intro Hnot.
    apply Hnone; exists u; auto.
  - intros [u [Rwu Hnot]] Hbox.
    exact (Hnot (Hbox u Rwu)).
Qed.

(** Model and frame validity. *)

Definition plon_model_valid (M : plon_model) (p : formula nat) : Prop :=
  forall w, plon_satisfies M w p.

Definition plon_model_invalid (M : plon_model) (p : formula nat) : Prop :=
  ~ plon_model_valid M p.

Lemma plon_model_valid_iff :
  forall M p,
    plon_model_valid M p <-> forall w, plon_satisfies M w p.
Proof. reflexivity. Qed.

Lemma plon_model_invalid_iff :
  forall M p,
    plon_model_invalid M p <->
    exists w, ~ plon_satisfies M w p.
Proof.
  intros M p; unfold plon_model_invalid, plon_model_valid; split.
  - intro H.
    apply NNPP; intro Hnone.
    apply H; intro w.
    apply NNPP; intro Hnot.
    apply Hnone; exists w; exact Hnot.
  - intros [w Hnot] Hvalid; exact (Hnot (Hvalid w)).
Qed.

Lemma plon_model_valid_top :
  forall M, plon_model_valid M Top.
Proof. intros M w; apply plon_satisfies_top. Qed.

Lemma plon_model_invalid_bottom :
  forall M, plon_model_invalid M Bottom.
Proof.
  intros M Hvalid.
  exact (plon_satisfies_bottom (Hvalid (plon_default (plon_model_frame M)))).
Qed.

(** The classical Lukasiewicz schemata used by Foundation's PLoN layer. *)
Definition plon_imply_K (p q : formula nat) : formula nat :=
  Imp p (Imp q p).

Definition plon_imply_S (p q r : formula nat) : formula nat :=
  Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r)).

Definition plon_elim_contra (p q : formula nat) : formula nat :=
  Imp (Imp (Neg q) (Neg p)) (Imp p q).

Lemma plon_model_valid_imply_K :
  forall M p q, plon_model_valid M (plon_imply_K p q).
Proof. intros M p q w Hp _; exact Hp. Qed.

Lemma plon_model_valid_imply_S :
  forall M p q r, plon_model_valid M (plon_imply_S p q r).
Proof. intros M p q r w Hpqr Hpq Hp; exact (Hpqr Hp (Hpq Hp)). Qed.

Lemma plon_model_valid_elim_contra :
  forall M p q, plon_model_valid M (plon_elim_contra p q).
Proof.
  intros M p q w Hcontra Hp.
  apply NNPP; intro Hnq.
  exact (Hcontra Hnq Hp).
Qed.

Lemma plon_model_valid_nec :
  forall M p,
    plon_model_valid M p -> plon_model_valid M (Box p).
Proof. intros M p Hp w u _; apply Hp. Qed.

Lemma plon_model_valid_mp :
  forall M p q,
    plon_model_valid M (Imp p q) ->
    plon_model_valid M p ->
    plon_model_valid M q.
Proof. intros M p q Hpq Hp w; exact (Hpq w (Hp w)). Qed.

(** Replacement of equivalents is not valid for formula-indexed relations.
    The two atoms receive identical truth values, but only the relation
    indexed by atom 1 has edges. *)

Definition plon_re_frame : plon_frame :=
  {| plon_world := bool;
     plon_rel := fun p _ _ => p = Atom 1;
     plon_default := false |}.

Definition plon_re_model : plon_model :=
  plon_model_on plon_re_frame (fun w _ => w = false).

Theorem plon_replacement_of_equivalents_fails :
  ~ (forall (M : plon_model) (p q : formula nat),
      plon_model_valid M (Iff p q) ->
      plon_model_valid M (Iff (Box p) (Box q))).
Proof.
  intro Hre.
  specialize (Hre plon_re_model (Atom 0) (Atom 1)).
  assert (Heq : plon_model_valid plon_re_model (Iff (Atom 0) (Atom 1))).
  { intro w.
    apply (proj2 (@plon_satisfies_iff plon_re_model w (Atom 0) (Atom 1)));
      reflexivity. }
  specialize (Hre Heq false).
  apply (proj1
    (@plon_satisfies_iff plon_re_model false (Box (Atom 0)) (Box (Atom 1))))
    in Hre.
  assert (Hbox0 : plon_satisfies plon_re_model false (Box (Atom 0))).
  { intros u Hrel; discriminate Hrel. }
  specialize (proj1 Hre Hbox0) as Hbox1.
  specialize (Hbox1 true eq_refl).
  discriminate Hbox1.
Qed.

Definition plon_frame_valid (F : plon_frame) (p : formula nat) : Prop :=
  forall V : plon_valuation F, plon_model_valid (plon_model_on F V) p.

Definition plon_frame_invalid (F : plon_frame) (p : formula nat) : Prop :=
  ~ plon_frame_valid F p.

Lemma plon_frame_valid_iff :
  forall F p,
    plon_frame_valid F p <->
    forall V, plon_model_valid (plon_model_on F V) p.
Proof. reflexivity. Qed.

Lemma plon_frame_invalid_iff :
  forall F p,
    plon_frame_invalid F p <->
    exists V, plon_model_invalid (plon_model_on F V) p.
Proof.
  intros F p; unfold plon_frame_invalid, plon_frame_valid; split.
  - intro H.
    apply NNPP; intro Hnone.
    apply H; intro V.
    apply NNPP; intro Hnot.
    apply Hnone; exists V; exact Hnot.
  - intros [V Hnot] Hvalid; exact (Hnot (Hvalid V)).
Qed.

Lemma plon_frame_valid_top :
  forall F, plon_frame_valid F Top.
Proof. intros F V; apply plon_model_valid_top. Qed.

Lemma plon_frame_invalid_bottom :
  forall F, plon_frame_invalid F Bottom.
Proof.
  intros F Hvalid.
  pose (V := fun (_ : plon_world F) (_ : nat) => False).
  exact (plon_model_invalid_bottom (Hvalid V)).
Qed.

(** Validity over a class of PLoN frames, together with all three
    countermodel presentations from Foundation. *)

Definition plon_frame_class_valid (C : plon_frame_class)
    (p : formula nat) : Prop :=
  forall F, C F -> plon_frame_valid F p.

Definition plon_frame_class_invalid (C : plon_frame_class)
    (p : formula nat) : Prop :=
  ~ plon_frame_class_valid C p.

Lemma plon_frame_class_invalid_iff_frame :
  forall C p,
    plon_frame_class_invalid C p <->
    exists F, C F /\ plon_frame_invalid F p.
Proof.
  intros C p; unfold plon_frame_class_invalid, plon_frame_class_valid; split.
  - intro H.
    apply NNPP; intro Hnone.
    apply H; intros F HCF.
    apply NNPP; intro Hbad.
    apply Hnone; exists F; auto.
  - intros [F [HCF Hbad]] Hvalid.
    exact (Hbad (Hvalid F HCF)).
Qed.

Lemma plon_frame_class_invalid_iff_model :
  forall C p,
    plon_frame_class_invalid C p <->
    exists M : plon_model,
      C (plon_model_frame M) /\ plon_model_invalid M p.
Proof.
  intros C p; split.
  - intro H.
    apply plon_frame_class_invalid_iff_frame in H.
    destruct H as [F [HCF HF]].
    apply plon_frame_invalid_iff in HF.
    destruct HF as [V HV].
    exists (plon_model_on F V); auto.
  - intros [M [HCM HM]].
    apply plon_frame_class_invalid_iff_frame.
    exists (plon_model_frame M); split; [exact HCM |].
    apply plon_frame_invalid_iff.
    exists (plon_model_valuation M).
    destruct M as [F V]; exact HM.
Qed.

Lemma plon_frame_class_invalid_iff_model_world :
  forall C p,
    plon_frame_class_invalid C p <->
    exists (M : plon_model) (w : plon_world (plon_model_frame M)),
      C (plon_model_frame M) /\ ~ plon_satisfies M w p.
Proof.
  intros C p; rewrite plon_frame_class_invalid_iff_model; split.
  - intros [M [HCM HM]].
    apply plon_model_invalid_iff in HM.
    destruct HM as [w Hw].
    exists M, w; auto.
  - intros [M [w [HCM Hw]]].
    exists M; split; [exact HCM |].
    apply plon_model_invalid_iff; exists w; exact Hw.
Qed.

(** Directional aliases mirror Foundation's exported elimination/introduction
    names and are convenient in later soundness and completeness files. *)
Definition plon_exists_frame_of_class_invalid :=
  fun C p => @proj1 _ _ (plon_frame_class_invalid_iff_frame C p).

Definition plon_class_invalid_of_exists_frame :=
  fun C p => @proj2 _ _ (plon_frame_class_invalid_iff_frame C p).

Definition plon_exists_model_of_class_invalid :=
  fun C p => @proj1 _ _ (plon_frame_class_invalid_iff_model C p).

Definition plon_class_invalid_of_exists_model :=
  fun C p => @proj2 _ _ (plon_frame_class_invalid_iff_model C p).

Definition plon_exists_model_world_of_class_invalid :=
  fun C p => @proj1 _ _ (plon_frame_class_invalid_iff_model_world C p).

Definition plon_class_invalid_of_exists_model_world :=
  fun C p => @proj2 _ _ (plon_frame_class_invalid_iff_model_world C p).
