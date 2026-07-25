(**
  Boxdot translation, its semantic/proof-theoretic metatheory, and the
  named boxdot results.

  This file ports the mathematical surfaces of Foundation's pinned
  [Modal/Boxdot] directory.  The local development already defines the
  recursive translation in [FrameTransformations]; it is reused here rather
  than duplicated.  Results whose upstream proofs depend on named canonical
  completeness or the global finite-consequence API are exposed with those
  dependencies as explicit hypotheses near the end of the file.  Nothing is
  postulated.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence CorrespondenceExtensions
  FrameProperties FrameTransformations Preservation Root WeakCorrespondence
  HilbertK CanonicalK NormalHilbert Filtration Loeb.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Basic semantic translation laws *)

Lemma boxdot_reflexive_closure_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         x (p : formula AtomType),
    satisfies F V x (boxdot_translate p) <->
    satisfies (frame_refl_gen F) V x p.
Proof.
  intros AtomType F V x p; revert x.
  induction p as [a | | p IHp q IHq | p IHp]; intro x; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHp, IHq; reflexivity.
  - rewrite (@satisfies_and AtomType F V x
      (boxdot_translate p) (Box (boxdot_translate p))).
    split.
    + intros [Hlocal Hbox] y [Heq | Rxy].
      * subst y; now apply (proj1 (IHp x)).
      * apply (proj1 (IHp y)); exact (Hbox y Rxy).
    + intro Hreflexive; split.
      * apply (proj2 (IHp x)); apply Hreflexive; now left.
      * intros y Rxy. apply (proj2 (IHp y)).
        apply Hreflexive; now right.
Qed.

Lemma boxdot_reflexive_closure_valid_iff :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    valid F (boxdot_translate p) <-> valid (frame_refl_gen F) p.
Proof.
  intros AtomType F p; split; intros H V x.
  - apply (proj1 (@boxdot_reflexive_closure_truth AtomType F V x p)); apply H.
  - apply (proj2 (@boxdot_reflexive_closure_truth AtomType F V x p)); apply H.
Qed.

Lemma refl_gen_idempotent_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         x (p : formula AtomType),
    satisfies (frame_refl_gen (frame_refl_gen F)) V x p <->
    satisfies (frame_refl_gen F) V x p.
Proof.
  intros AtomType F V x p; revert x.
  induction p as [a | | p IHp q IHq | p IHp]; intro x; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHp, IHq; reflexivity.
  - split; intros Hbox y Rxy.
    + apply (proj1 (IHp y)), Hbox. now right.
    + apply (proj2 (IHp y)), Hbox.
      destruct Rxy as [-> | Rxy]; [now left | exact Rxy].
Qed.

Lemma boxdot_translate_idempotent_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         x (p : formula AtomType),
    satisfies F V x (boxdot_translate (boxdot_translate p)) <->
    satisfies F V x (boxdot_translate p).
Proof.
  intros AtomType F V x p.
  etransitivity.
  - apply boxdot_reflexive_closure_truth.
  - etransitivity.
    + apply boxdot_reflexive_closure_truth.
    + etransitivity.
      * apply refl_gen_idempotent_truth.
      * symmetry; apply boxdot_reflexive_closure_truth.
Qed.

Lemma boxdot_translate_and_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         x (p q : formula AtomType),
    satisfies F V x (boxdot_translate (And p q)) <->
    satisfies F V x (And (boxdot_translate p) (boxdot_translate q)).
Proof.
  reflexivity.
Qed.

Fixpoint formula_list_conj {AtomType}
    (ps : list (formula AtomType)) : formula AtomType :=
  match ps with
  | [] => Top
  | p :: rest => And p (formula_list_conj rest)
  end.

Lemma boxdot_translate_list_conj :
  forall (AtomType : Type) (ps : list (formula AtomType)),
    boxdot_translate (formula_list_conj ps) =
    formula_list_conj (map boxdot_translate ps).
Proof.
  intros AtomType ps; induction ps as [|p ps IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma boxdot_translate_list_conj_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         x (ps : list (formula AtomType)),
    satisfies F V x (boxdot_translate (formula_list_conj ps)) <->
    satisfies F V x (formula_list_conj (map boxdot_translate ps)).
Proof.
  intros AtomType F V x ps.
  now rewrite boxdot_translate_list_conj.
Qed.

(** [box_upto] is an inductive list-free presentation of Foundation's
    finite conjunction [box^0 p /\ ... /\ box^n p].  Distributing box over
    conjunction makes the two presentations semantically identical. *)
Fixpoint box_upto {AtomType} (n : nat) (p : formula AtomType)
    : formula AtomType :=
  match n with
  | 0 => p
  | S k => And (box_upto k p) (Box (box_upto k p))
  end.

Lemma boxdot_translate_box_iter_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         n x (p : formula AtomType),
    satisfies F V x (boxdot_translate (box_iter n p)) <->
    satisfies F V x (box_upto n (boxdot_translate p)).
Proof.
  intros AtomType F V n; induction n as [|n IH]; intros x p.
  - reflexivity.
  - change
      (satisfies F V x
        (And (boxdot_translate (box_iter n p))
          (Box (boxdot_translate (box_iter n p)))) <->
       satisfies F V x
        (And (box_upto n (boxdot_translate p))
          (Box (box_upto n (boxdot_translate p))))).
    rewrite !satisfies_and. split.
    + intros [Hlocal Hbox]; split.
      * apply (proj1 (IH x p)); exact Hlocal.
      * intros y Rxy. apply (proj1 (IH y p)); exact (Hbox y Rxy).
    + intros [Hlocal Hbox]; split.
      * apply (proj2 (IH x p)); exact Hlocal.
      * intros y Rxy. apply (proj2 (IH y p)); exact (Hbox y Rxy).
Qed.

(** Foundation's reflexivize-after-irreflexivize theorem is already the
    independently ported [irreflexivize_reflexive_truth]. *)
Definition boxdot_irreflexivize_reflexive_truth :=
  irreflexivize_reflexive_truth.

Definition boxdot_irreflexivize_reflexive_valid_iff :=
  irreflexivize_reflexive_valid_iff.

(** * Proof-theoretic preservation *)

Lemma normal_proves_of_K_valid :
  forall Ax (p : formula nat),
    valid_on_all_frames p -> normal_proves Ax p.
Proof.
  intros Ax p Hvalid.
  apply K_proves_normal, K_complete; exact Hvalid.
Qed.

Lemma normal_proves_K_rule1 :
  forall Ax (p q : formula nat),
    valid_on_all_frames (Imp p q) ->
    normal_proves Ax p -> normal_proves Ax q.
Proof.
  intros Ax p q Hvalid Hp.
  eapply Np_mp; [apply normal_proves_of_K_valid; exact Hvalid | exact Hp].
Qed.

Lemma normal_proves_K_rule2 :
  forall Ax (p q r : formula nat),
    valid_on_all_frames (Imp p (Imp q r)) ->
    normal_proves Ax p -> normal_proves Ax q -> normal_proves Ax r.
Proof.
  intros Ax p q r Hvalid Hp Hq.
  eapply Np_mp.
  - eapply Np_mp.
    + apply normal_proves_of_K_valid; exact Hvalid.
    + exact Hp.
  - exact Hq.
Qed.

Lemma normal_proves_iff_refl :
  forall Ax (p : formula nat),
    normal_proves Ax (Iff p p).
Proof.
  intros; apply normal_proves_of_K_valid.
  intros F V w; apply (proj2 (@satisfies_iff nat F V w p p)); reflexivity.
Qed.

Lemma normal_proves_iff_intro :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp q p) ->
    normal_proves Ax (Iff p q).
Proof.
  intros Ax p q Hpq Hqp.
  eapply normal_proves_K_rule2; [|exact Hpq | exact Hqp].
  intros F V w H1 H2.
  apply (proj2 (@satisfies_iff nat F V w p q)); split; assumption.
Qed.

Lemma normal_proves_iff_left :
  forall Ax (p q : formula nat),
    normal_proves Ax (Iff p q) -> normal_proves Ax (Imp p q).
Proof.
  intros Ax p q Hiff.
  eapply normal_proves_K_rule1; [|exact Hiff].
  intros F V w H; apply (proj1 (@satisfies_iff nat F V w p q)) in H.
  exact (proj1 H).
Qed.

Lemma normal_proves_iff_right :
  forall Ax (p q : formula nat),
    normal_proves Ax (Iff p q) -> normal_proves Ax (Imp q p).
Proof.
  intros Ax p q Hiff.
  eapply normal_proves_K_rule1; [|exact Hiff].
  intros F V w H; apply (proj1 (@satisfies_iff nat F V w p q)) in H.
  exact (proj2 H).
Qed.

Lemma normal_proves_iff_trans :
  forall Ax (p q r : formula nat),
    normal_proves Ax (Iff p q) ->
    normal_proves Ax (Iff q r) ->
    normal_proves Ax (Iff p r).
Proof.
  intros Ax p q r Hpq Hqr.
  eapply normal_proves_K_rule2; [|exact Hpq | exact Hqr].
  intros F V w H1 H2.
  apply (proj1 (@satisfies_iff nat F V w p q)) in H1.
  apply (proj1 (@satisfies_iff nat F V w q r)) in H2.
  apply (proj2 (@satisfies_iff nat F V w p r)); tauto.
Qed.

Lemma normal_proves_imp_iff :
  forall Ax (p p' q q' : formula nat),
    normal_proves Ax (Iff p p') ->
    normal_proves Ax (Iff q q') ->
    normal_proves Ax (Iff (Imp p q) (Imp p' q')).
Proof.
  intros Ax p p' q q' Hp Hq.
  eapply normal_proves_K_rule2; [|exact Hp | exact Hq].
  intros F V w H1 H2.
  apply (proj1 (@satisfies_iff nat F V w p p')) in H1.
  apply (proj1 (@satisfies_iff nat F V w q q')) in H2.
  apply (proj2 (@satisfies_iff nat F V w (Imp p q) (Imp p' q'))).
  simpl; tauto.
Qed.

Lemma normal_proves_box_regularity :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp (Box p) (Box q)).
Proof.
  intros Ax p q Hpq.
  eapply Np_mp; [exact (Np_modal_K p q) | now apply Np_nec].
Qed.

Lemma normal_proves_box_iff :
  forall Ax (p q : formula nat),
    normal_proves Ax (Iff p q) ->
    normal_proves Ax (Iff (Box p) (Box q)).
Proof.
  intros Ax p q Hiff; apply normal_proves_iff_intro.
  - apply normal_proves_box_regularity, normal_proves_iff_left; exact Hiff.
  - apply normal_proves_box_regularity, normal_proves_iff_right; exact Hiff.
Qed.

Lemma normal_proves_boxdot_nec :
  forall Ax (p : formula nat),
    normal_proves Ax p -> normal_proves Ax (Boxdot p).
Proof.
  intros Ax p Hp.
  eapply normal_proves_K_rule2.
  - intros F V w Hlocal Hbox.
    apply (proj2 (@satisfies_and nat F V w p (Box p))).
    split.
    + exact Hlocal.
    + exact Hbox.
  - exact Hp.
  - now apply Np_nec.
Qed.

Lemma normal_proves_boxdot_axiom_K :
  forall Ax (p q : formula nat),
    normal_proves Ax (boxdot_translate (K p q)).
Proof.
  intros Ax p q; apply normal_proves_of_K_valid.
  intros F V w Himp Hp.
  apply (proj1 (@satisfies_and nat F V w _ _)) in Himp.
  apply (proj1 (@satisfies_and nat F V w _ _)) in Hp.
  apply (proj2 (@satisfies_and nat F V w _ _)); split.
  - exact (proj1 Himp (proj1 Hp)).
  - intros u Rwu; exact (proj2 Himp u Rwu (proj2 Hp u Rwu)).
Qed.

Theorem normal_proves_boxdot_translation :
  forall (AxSource AxTarget : modal_axiom_schema),
    (forall p : formula nat,
      AxSource nat p ->
      normal_proves AxTarget (boxdot_translate p)) ->
    forall p : formula nat,
      normal_proves AxSource p ->
      normal_proves AxTarget (boxdot_translate p).
Proof.
  intros AxSource AxTarget Hextra p Hp; induction Hp; simpl.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply normal_proves_boxdot_axiom_K.
  - now apply Hextra.
  - eapply Np_mp; eauto.
  - now apply normal_proves_boxdot_nec.
Qed.

(** * K4 / S4 *)

Lemma K4_proves_boxdot_T :
  forall p : formula nat,
    K4_proves (boxdot_translate (T p)).
Proof.
  intro p; apply normal_proves_of_K_valid.
  intros F V w Hboxdot.
  exact (proj1 (proj1 (@satisfies_and nat F V w _ _) Hboxdot)).
Qed.

Lemma K4_proves_boxdot_Four :
  forall p : formula nat,
    K4_proves (boxdot_translate (Four p)).
Proof.
  intro p.
  pose (t := boxdot_translate p).
  assert (Hfour : K4_proves (Four t)).
  { apply Np_extra; exists t; reflexivity. }
  eapply normal_proves_K_rule1; [|exact Hfour].
  intros F V w Hfour_sem Hboxdot.
  apply (proj1 (@satisfies_and nat F V w _ _)) in Hboxdot.
  apply (proj2 (@satisfies_and nat F V w _ _)); split.
  - apply (proj2 (@satisfies_and nat F V w _ _)); exact Hboxdot.
  - intros u Rwu.
    apply (proj2 (@satisfies_and nat F V u _ _)); split.
    + exact (proj2 Hboxdot u Rwu).
    + exact (Hfour_sem (proj2 Hboxdot) u Rwu).
Qed.

Theorem S4_proves_to_K4_boxdot :
  forall p : formula nat,
    S4_proves p -> K4_proves (boxdot_translate p).
Proof.
  intros p Hp.
  eapply normal_proves_boxdot_translation; [|exact Hp].
  intros q [HT | HFour].
  - destruct HT as [r ->]; apply K4_proves_boxdot_T.
  - destruct HFour as [r ->]; apply K4_proves_boxdot_Four.
Qed.

Lemma S4_proves_box_iff_boxdot :
  forall p : formula nat,
    S4_proves (Iff (Box p) (Boxdot p)).
Proof.
  intro p; apply normal_proves_iff_intro.
  - assert (HT : S4_proves (T p)).
    { apply Np_extra; left; exists p; reflexivity. }
    eapply normal_proves_K_rule1; [|exact HT].
    intros F V w Ht Hbox.
    apply (proj2 (@satisfies_and nat F V w _ _)); auto.
  - apply normal_proves_of_K_valid.
    intros F V w Hboxdot.
    exact (proj2 (proj1 (@satisfies_and nat F V w _ _) Hboxdot)).
Qed.

Lemma S4_proves_iff_boxdot_translate :
  forall p : formula nat,
    S4_proves (Iff p (boxdot_translate p)).
Proof.
  intro p; induction p as [a | | p IHp q IHq | p IHp].
  - apply normal_proves_iff_refl.
  - apply normal_proves_iff_refl.
  - now apply normal_proves_imp_iff.
  - eapply (normal_proves_iff_trans
      (p := Box p) (q := Box (boxdot_translate p))
      (r := Boxdot (boxdot_translate p))).
    + apply normal_proves_box_iff; exact IHp.
    + apply S4_proves_box_iff_boxdot.
Qed.

Theorem K4_boxdot_proves_to_S4 :
  forall p : formula nat,
    K4_proves (boxdot_translate p) -> S4_proves p.
Proof.
  intros p Htranslated.
  eapply Np_mp.
  - apply normal_proves_iff_right, S4_proves_iff_boxdot_translate.
  - now apply K4_weaker_than_S4.
Qed.

Theorem K4_boxdot_iff_S4 :
  forall p : formula nat,
    K4_proves (boxdot_translate p) <-> S4_proves p.
Proof.
  split; [apply K4_boxdot_proves_to_S4 | apply S4_proves_to_K4_boxdot].
Qed.

(** * GL / Grz

    The upstream equivalence uses finite-frame completeness of both named
    calculi.  [NormalHilbert] currently supplies their soundness but not
    those two completeness theorems.  We therefore prove all frame
    transformations unconditionally and make the missing completeness
    statements ordinary, explicit hypotheses of the proof-theoretic results. *)

Definition boxdot_GL_frame (F : frame) : Prop :=
  frame_transitive F /\ frame_converse_well_founded F.

Definition boxdot_Grz_frame (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\
  frame_weak_converse_well_founded F.

Definition boxdot_finite_GL_frame (F : frame) : Prop :=
  finite_frame F /\ boxdot_GL_frame F.

Definition boxdot_finite_Grz_frame (F : frame) : Prop :=
  finite_frame F /\ boxdot_Grz_frame F.

Lemma frame_refl_gen_finite_iff :
  forall F, finite_frame (frame_refl_gen F) <-> finite_frame F.
Proof. intros F; unfold finite_frame; reflexivity. Qed.

Lemma frame_refl_gen_weak_cwf_of_cwf :
  forall F,
    frame_converse_well_founded F ->
    frame_weak_converse_well_founded (frame_refl_gen F).
Proof.
  intros F Hcwf X HX.
  destruct (Hcwf X HX) as [m [Hm Hmax]].
  exists m; split; [exact Hm |].
  intros y Hy Rmy.
  destruct Rmy as [-> | Rmy]; [reflexivity |].
  exfalso; exact (Hmax y Hy Rmy).
Qed.

Theorem finite_GL_to_reflexive_closure_finite_Grz :
  forall F,
    boxdot_finite_GL_frame F ->
    boxdot_finite_Grz_frame (frame_refl_gen F).
Proof.
  intros F [Hfinite [Htrans Hcwf]].
  split.
  - apply (proj2 (frame_refl_gen_finite_iff F)); exact Hfinite.
  - repeat split.
    + apply frame_refl_gen_reflexive.
    + now apply frame_refl_gen_transitive.
    + now apply frame_refl_gen_weak_cwf_of_cwf.
Qed.

Lemma irreflexivize_cwf_of_weak_cwf :
  forall F,
    frame_weak_converse_well_founded F ->
    frame_converse_well_founded (irreflexivize_frame F).
Proof.
  intros F Hweak.
  change (frame_converse_well_founded (frame_irreflexive_reduction F)).
  now apply (proj1 (weak_cwf_iff_cwf_irreflexive_reduction F)).
Qed.

Theorem finite_Grz_to_irreflexivize_finite_GL :
  forall F,
    boxdot_finite_Grz_frame F ->
    boxdot_finite_GL_frame (irreflexivize_frame F).
Proof.
  intros F [Hfinite [Hrefl [Htrans Hweak]]].
  split.
  - apply (proj2 (irreflexivize_finite_iff F)); exact Hfinite.
  - split.
    + apply irreflexivize_transitive.
      * now apply weak_cwf_antisymmetric.
      * exact Htrans.
    + now apply irreflexivize_cwf_of_weak_cwf.
Qed.

Definition boxdot_GL_finite_complete : Prop :=
  forall p : formula nat,
    (forall F, boxdot_finite_GL_frame F -> valid F p) -> GL_proves p.

Definition boxdot_Grz_finite_complete : Prop :=
  forall p : formula nat,
    (forall F, boxdot_finite_Grz_frame F -> valid F p) -> Grz_proves p.

Lemma GL_proves_boxdot_Grz_axiom :
  boxdot_GL_finite_complete ->
  forall p : formula nat, GL_proves (boxdot_translate (Grz p)).
Proof.
  intros Hcomplete p; apply Hcomplete.
  intros F HGL.
  apply (proj2 (boxdot_reflexive_closure_valid_iff F (Grz p))).
  destruct (@finite_GL_to_reflexive_closure_finite_Grz F HGL)
    as [_ [Hrefl [Htrans Hweak]]].
  now apply valid_Grz_of_reflexive_transitive_weak_cwf.
Qed.

Theorem Grz_proves_to_GL_boxdot :
  boxdot_GL_finite_complete ->
  forall p : formula nat,
    Grz_proves p -> GL_proves (boxdot_translate p).
Proof.
  intros Hcomplete p Hp.
  eapply normal_proves_boxdot_translation; [|exact Hp].
  intros q [r ->]. now apply GL_proves_boxdot_Grz_axiom.
Qed.

Theorem GL_boxdot_proves_to_Grz :
  boxdot_Grz_finite_complete ->
  forall p : formula nat,
    GL_proves (boxdot_translate p) -> Grz_proves p.
Proof.
  intros Hcomplete p Hp; apply Hcomplete.
  intros F HGrz.
  destruct HGrz as [Hfinite [Hrefl [Htrans Hweak]]].
  assert (HGL : boxdot_finite_GL_frame (irreflexivize_frame F)).
  { apply finite_Grz_to_irreflexivize_finite_GL.
    repeat split; assumption. }
  destruct HGL as [_ [Hitrans Hicwf]].
  assert (Hvalid_i : valid (irreflexivize_frame F) (boxdot_translate p)).
  { now apply GL_proves_sound_on_transitive_cwf_frame. }
  assert (Hvalid_r : valid
      (frame_refl_gen (irreflexivize_frame F)) p).
  { now apply (proj1 (boxdot_reflexive_closure_valid_iff
      (irreflexivize_frame F) p)). }
  now apply (proj2 (@irreflexivize_reflexive_valid_iff nat F p Hrefl)).
Qed.

Theorem GL_boxdot_iff_Grz :
  boxdot_GL_finite_complete -> boxdot_Grz_finite_complete ->
  forall p : formula nat,
    GL_proves (boxdot_translate p) <-> Grz_proves p.
Proof.
  intros HGL HGrz p; split.
  - now apply GL_boxdot_proves_to_Grz.
  - now apply Grz_proves_to_GL_boxdot.
Qed.

(** * GL.3 / Grz.3 *)

Definition schema_WeakPoint3 : modal_axiom_schema :=
  fun AtomType p => exists q r : formula AtomType, p = WeakPoint3 q r.

Definition schema_Point3 : modal_axiom_schema :=
  fun AtomType p => exists q r : formula AtomType, p = Point3 q r.

Definition GLPoint3_schema := schema_union schema_L schema_WeakPoint3.
Definition GrzPoint3_schema := schema_union schema_Grz schema_Point3.

Definition GLPoint3_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves GLPoint3_schema AtomType.

Definition GrzPoint3_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves GrzPoint3_schema AtomType.

Definition boxdot_finite_GLPoint3_frame (F : frame) : Prop :=
  boxdot_finite_GL_frame F /\ frame_piecewise_connected F.

Definition boxdot_finite_GrzPoint3_frame (F : frame) : Prop :=
  boxdot_finite_Grz_frame F /\ frame_piecewise_strongly_connected F.

Lemma frame_refl_gen_piecewise_strongly_connected :
  forall F,
    frame_piecewise_connected F ->
    frame_piecewise_strongly_connected (frame_refl_gen F).
Proof.
  intros F Hpiece x y z Rxy Rxz.
  destruct Rxy as [-> | Rxy].
  - now left.
  - destruct Rxz as [-> | Rxz].
    + right; right; exact Rxy.
    + destruct (Hpiece x y z Rxy Rxz) as [Ryz | [-> | Rzy]].
      * left; right; exact Ryz.
      * left; left; reflexivity.
      * right; right; exact Rzy.
Qed.

Theorem finite_GLPoint3_to_reflexive_closure_finite_GrzPoint3 :
  forall F,
    boxdot_finite_GLPoint3_frame F ->
    boxdot_finite_GrzPoint3_frame (frame_refl_gen F).
Proof.
  intros F [HGL Hpiece]; split.
  - now apply finite_GL_to_reflexive_closure_finite_Grz.
  - now apply frame_refl_gen_piecewise_strongly_connected.
Qed.

Theorem finite_GrzPoint3_to_irreflexivize_finite_GLPoint3 :
  forall F,
    boxdot_finite_GrzPoint3_frame F ->
    boxdot_finite_GLPoint3_frame (irreflexivize_frame F).
Proof.
  intros F [HGrz Hpiece]; split.
  - now apply finite_Grz_to_irreflexivize_finite_GL.
  - now apply irreflexivize_piecewise_connected.
Qed.

Lemma schema_WeakPoint3_valid_on_piecewise_connected :
  forall F,
    frame_piecewise_connected F ->
    schema_valid_on_frame schema_WeakPoint3 F.
Proof.
  intros F Hpiece AtomType p [q [r ->]].
  now apply valid_WeakPoint3_of_piecewise_connected.
Qed.

Lemma schema_Point3_valid_on_piecewise_strongly_connected :
  forall F,
    frame_piecewise_strongly_connected F ->
    schema_valid_on_frame schema_Point3 F.
Proof.
  intros F Hpiece AtomType p [q [r ->]].
  now apply valid_Point3_of_piecewise_strong_connected.
Qed.

Theorem GLPoint3_proves_sound_on_finite_frame :
  forall (p : formula nat) F,
    boxdot_finite_GLPoint3_frame F ->
    GLPoint3_proves p -> valid F p.
Proof.
  intros p F [[_ [Htrans Hcwf]] Hpiece] Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_L_valid_on_GL_frame.
  - now apply schema_WeakPoint3_valid_on_piecewise_connected.
Qed.

Theorem GrzPoint3_proves_sound_on_finite_frame :
  forall (p : formula nat) F,
    boxdot_finite_GrzPoint3_frame F ->
    GrzPoint3_proves p -> valid F p.
Proof.
  intros p F [[_ [Hrefl [Htrans Hweak]]] Hpiece] Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_Grz_valid_on_Grz_frame.
  - now apply schema_Point3_valid_on_piecewise_strongly_connected.
Qed.

Definition boxdot_GLPoint3_finite_complete : Prop :=
  forall p : formula nat,
    (forall F, boxdot_finite_GLPoint3_frame F -> valid F p) ->
    GLPoint3_proves p.

Definition boxdot_GrzPoint3_finite_complete : Prop :=
  forall p : formula nat,
    (forall F, boxdot_finite_GrzPoint3_frame F -> valid F p) ->
    GrzPoint3_proves p.

Lemma GLPoint3_proves_boxdot_Grz_axiom :
  boxdot_GLPoint3_finite_complete ->
  forall p : formula nat, GLPoint3_proves (boxdot_translate (Grz p)).
Proof.
  intros Hcomplete p; apply Hcomplete.
  intros F HGL3.
  apply (proj2 (boxdot_reflexive_closure_valid_iff F (Grz p))).
  destruct (@finite_GLPoint3_to_reflexive_closure_finite_GrzPoint3 F HGL3)
    as [[_ [Hrefl [Htrans Hweak]]] _].
  now apply valid_Grz_of_reflexive_transitive_weak_cwf.
Qed.

Lemma GLPoint3_proves_boxdot_Point3_axiom :
  boxdot_GLPoint3_finite_complete ->
  forall p q : formula nat,
    GLPoint3_proves (boxdot_translate (Point3 p q)).
Proof.
  intros Hcomplete p q; apply Hcomplete.
  intros F HGL3.
  apply (proj2 (boxdot_reflexive_closure_valid_iff F (Point3 p q))).
  destruct (@finite_GLPoint3_to_reflexive_closure_finite_GrzPoint3 F HGL3)
    as [_ Hpiece].
  now apply valid_Point3_of_piecewise_strong_connected.
Qed.

Theorem GrzPoint3_proves_to_GLPoint3_boxdot :
  boxdot_GLPoint3_finite_complete ->
  forall p : formula nat,
    GrzPoint3_proves p -> GLPoint3_proves (boxdot_translate p).
Proof.
  intros Hcomplete p Hp.
  eapply normal_proves_boxdot_translation; [|exact Hp].
  intros q [HGrz | HPoint3].
  - destruct HGrz as [r ->].
    now apply GLPoint3_proves_boxdot_Grz_axiom.
  - destruct HPoint3 as [r [s ->]].
    now apply GLPoint3_proves_boxdot_Point3_axiom.
Qed.

Theorem GLPoint3_boxdot_proves_to_GrzPoint3 :
  boxdot_GrzPoint3_finite_complete ->
  forall p : formula nat,
    GLPoint3_proves (boxdot_translate p) -> GrzPoint3_proves p.
Proof.
  intros Hcomplete p Hp; apply Hcomplete.
  intros F HGrz3.
  assert (HGL3 : boxdot_finite_GLPoint3_frame (irreflexivize_frame F)).
  { now apply finite_GrzPoint3_to_irreflexivize_finite_GLPoint3. }
  assert (Hvalid_i : valid (irreflexivize_frame F) (boxdot_translate p)).
  { now apply GLPoint3_proves_sound_on_finite_frame. }
  assert (Hvalid_r : valid
      (frame_refl_gen (irreflexivize_frame F)) p).
  { now apply (proj1 (boxdot_reflexive_closure_valid_iff
      (irreflexivize_frame F) p)). }
  destruct HGrz3 as [[_ [Hrefl _]] _].
  now apply (proj2 (@irreflexivize_reflexive_valid_iff nat F p Hrefl)).
Qed.

Theorem GLPoint3_boxdot_iff_GrzPoint3 :
  boxdot_GLPoint3_finite_complete ->
  boxdot_GrzPoint3_finite_complete ->
  forall p : formula nat,
    GLPoint3_proves (boxdot_translate p) <-> GrzPoint3_proves p.
Proof.
  intros HGL3 HGrz3 p; split.
  - now apply GLPoint3_boxdot_proves_to_GrzPoint3.
  - now apply GrzPoint3_proves_to_GLPoint3_boxdot.
Qed.

Definition iff_boxdotTranslated_GLPoint3_GrzPoint3 :=
  GLPoint3_boxdot_iff_GrzPoint3.

Definition iff_boxdot_GLPoint3_GrzPoint3 :=
  GLPoint3_boxdot_iff_GrzPoint3.

(** * Ver / Triv *)

Definition schema_Ver : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Ver q.

Definition schema_Tc : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Tc q.

Definition Triv_schema := schema_union schema_T schema_Tc.

Definition Ver_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves schema_Ver AtomType.

Definition Triv_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves Triv_schema AtomType.

Definition boxdot_Triv_frame (F : frame) : Prop :=
  frame_reflexive F /\ frame_coreflexive F.

Lemma irreflexivize_isolated_of_coreflexive :
  forall F,
    frame_coreflexive F -> frame_isolated (irreflexivize_frame F).
Proof.
  intros F Hcore x y [Rxy Hneq].
  apply Hneq; now apply Hcore.
Qed.

Lemma Ver_proves_boxdot_T :
  forall p : formula nat, Ver_proves (boxdot_translate (T p)).
Proof.
  intro p; apply normal_proves_of_K_valid.
  intros F V w Hboxdot.
  exact (proj1 (proj1 (@satisfies_and nat F V w _ _) Hboxdot)).
Qed.

Lemma Ver_proves_boxdot_Tc :
  forall p : formula nat, Ver_proves (boxdot_translate (Tc p)).
Proof.
  intro p; pose (t := boxdot_translate p).
  assert (Hver : Ver_proves (Box t)).
  { apply Np_extra; exists t; reflexivity. }
  eapply Np_mp; [|exact Hver].
  apply normal_proves_of_K_valid.
  intros F V w Hbox Hlocal.
  apply (proj2 (@satisfies_and nat F V w t (Box t))).
  now split.
Qed.

Theorem Triv_proves_to_Ver_boxdot :
  forall p : formula nat,
    Triv_proves p -> Ver_proves (boxdot_translate p).
Proof.
  intros p Hp.
  eapply normal_proves_boxdot_translation; [|exact Hp].
  intros q [HT | HTc].
  - destruct HT as [r ->]; apply Ver_proves_boxdot_T.
  - destruct HTc as [r ->]; apply Ver_proves_boxdot_Tc.
Qed.

Lemma Ver_proves_sound_on_isolated_frame :
  forall (p : formula nat) F,
    frame_isolated F -> Ver_proves p -> valid F p.
Proof.
  intros p F Hisolated Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  intros AtomType q [r ->].
  now apply valid_Ver_of_isolated.
Qed.

Definition boxdot_Triv_complete : Prop :=
  forall p : formula nat,
    (forall F, boxdot_Triv_frame F -> valid F p) -> Triv_proves p.

Theorem Ver_boxdot_proves_to_Triv :
  boxdot_Triv_complete ->
  forall p : formula nat,
    Ver_proves (boxdot_translate p) -> Triv_proves p.
Proof.
  intros Hcomplete p Hp; apply Hcomplete.
  intros F [Hrefl Hcore].
  assert (Hvalid_i : valid (irreflexivize_frame F) (boxdot_translate p)).
  { apply Ver_proves_sound_on_isolated_frame; [|exact Hp].
    now apply irreflexivize_isolated_of_coreflexive. }
  assert (Hvalid_r : valid
      (frame_refl_gen (irreflexivize_frame F)) p).
  { now apply (proj1 (boxdot_reflexive_closure_valid_iff
      (irreflexivize_frame F) p)). }
  now apply (proj2 (@irreflexivize_reflexive_valid_iff nat F p Hrefl)).
Qed.

Theorem Ver_boxdot_iff_Triv :
  boxdot_Triv_complete ->
  forall p : formula nat,
    Ver_proves (boxdot_translate p) <-> Triv_proves p.
Proof.
  intros Hcomplete p; split.
  - now apply Ver_boxdot_proves_to_Triv.
  - apply Triv_proves_to_Ver_boxdot.
Qed.

Definition iff_boxdotTranslated_Ver_Triv' := Ver_boxdot_iff_Triv.
Definition iff_boxdotTranslated_Ver_Triv := Ver_boxdot_iff_Triv.

(** * Jeřábek's doubling construction *)

Definition frame_twice (F : frame) : frame :=
  {| World := (World F * bool)%type;
     Rel := fun x y => Rel F (fst x) (fst y) |}.

Lemma frame_twice_reflexive :
  forall F,
    frame_reflexive F -> frame_reflexive (frame_twice F).
Proof. intros F Hrefl [x b]; apply Hrefl. Qed.

Lemma frame_twice_transitive :
  forall F,
    frame_transitive F -> frame_transitive (frame_twice F).
Proof.
  intros F Htrans [x i] [y j] [z k] Rxy Ryz.
  exact (Htrans x y z Rxy Ryz).
Qed.

Lemma frame_twice_symmetric :
  forall F,
    frame_symmetric F -> frame_symmetric (frame_twice F).
Proof. intros F Hsym [x i] [y j] Rxy; exact (Hsym x y Rxy). Qed.

Lemma frame_twice_piecewise_strongly_convergent :
  forall F,
    frame_piecewise_strongly_convergent F ->
    frame_piecewise_strongly_convergent (frame_twice F).
Proof.
  intros F Hconv [x i] [y j] [z k] Rxy Rxz.
  destruct (Hconv x y z Rxy Rxz) as [u [Ryu Rzu]].
  exists (u, i); now split.
Qed.

Lemma frame_twice_piecewise_strongly_connected :
  forall F,
    frame_piecewise_strongly_connected F ->
    frame_piecewise_strongly_connected (frame_twice F).
Proof.
  intros F Hconn [x i] [y j] [z k] Rxy Rxz.
  now apply (Hconn x y z Rxy Rxz).
Qed.

Definition frame_twice_p_morphism (F : frame) :
    @p_morphism (frame_twice F) F.
Proof.
  refine {| pmap := fun (u : World (frame_twice F)) => fst u |}.
  - intros [x i] [y j] Rxy; exact Rxy.
  - intros [x i] z Rxz.
    exists (z, true); split; [reflexivity | exact Rxz].
Defined.

Lemma frame_twice_p_morphism_surjective :
  forall F z,
    exists x, pmap (frame_twice_p_morphism F) x = z.
Proof. intros F z; exists (z, true); reflexivity. Qed.

Theorem frame_twice_valid_reflects :
  forall (AtomType : Type) F (p : formula AtomType),
    valid (frame_twice F) p -> valid F p.
Proof.
  intros AtomType F p Hvalid.
  eapply valid_of_surjective_p_morphism
    with (f := frame_twice_p_morphism F).
  - apply frame_twice_p_morphism_surjective.
  - exact Hvalid.
Qed.

Definition frame_class := frame -> Prop.

Definition jerabek_frameclass_closed (C : frame_class) : Prop :=
  forall F, C F -> C (frame_twice F).

Definition KT_frame_class : frame_class := frame_reflexive.

Definition KTB_frame_class : frame_class :=
  fun F => frame_reflexive F /\ frame_symmetric F.

Definition S4_frame_class : frame_class :=
  fun F => frame_reflexive F /\ frame_transitive F.

Definition S4Point2_frame_class : frame_class :=
  fun F => frame_reflexive F /\ frame_transitive F /\
    frame_piecewise_strongly_convergent F.

Definition S4Point3_frame_class : frame_class :=
  fun F => frame_reflexive F /\ frame_transitive F /\
    frame_piecewise_strongly_connected F.

Definition S5_frame_class : frame_class :=
  fun F => frame_reflexive F /\ frame_transitive F /\ frame_symmetric F.

Lemma KT_frameclass_jerabek : jerabek_frameclass_closed KT_frame_class.
Proof. intros F HF; now apply frame_twice_reflexive. Qed.

Lemma KTB_frameclass_jerabek : jerabek_frameclass_closed KTB_frame_class.
Proof.
  intros F [HR HS]; split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_symmetric.
Qed.

Lemma S4_frameclass_jerabek : jerabek_frameclass_closed S4_frame_class.
Proof.
  intros F [HR HT]; split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
Qed.

Lemma S4Point2_frameclass_jerabek :
  jerabek_frameclass_closed S4Point2_frame_class.
Proof.
  intros F [HR [HT HC]]; repeat split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
  - now apply frame_twice_piecewise_strongly_convergent.
Qed.

Lemma S4Point3_frameclass_jerabek :
  jerabek_frameclass_closed S4Point3_frame_class.
Proof.
  intros F [HR [HT HC]]; repeat split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
  - now apply frame_twice_piecewise_strongly_connected.
Qed.

Lemma S5_frameclass_jerabek : jerabek_frameclass_closed S5_frame_class.
Proof.
  intros F [HR [HT HS]]; repeat split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
  - now apply frame_twice_symmetric.
Qed.

Definition formula_flag {AtomType} (p : formula AtomType) (b : bool)
    : formula AtomType :=
  if b then p else Neg p.

Lemma atom_flag_boxdot_translated :
  forall (a : nat) b,
    boxdot_translate (formula_flag (Atom a) b) = formula_flag (Atom a) b.
Proof. intros a []; reflexivity. Qed.

Lemma satisfies_neither_flag :
  forall (AtomType : Type) F (V : valuation AtomType F) w
         (p : formula AtomType) b,
    ~ (satisfies F V w (formula_flag p b) /\
       satisfies F V w (formula_flag p (negb b))).
Proof. intros AtomType F V w p []; simpl; tauto. Qed.

(** * Logic-level boxdot properties

    A logic is represented extensionally as a predicate on formulas.  The
    small [boxdot_normal_logic] interface is exactly what the boxdot
    properties quantify over: containment of K, modus ponens, and
    necessitation. *)

Definition modal_logic := formula nat -> Prop.

Definition logic_included (L M : modal_logic) : Prop :=
  forall p, L p -> M p.

Definition boxdot_preimage (L : modal_logic) : modal_logic :=
  fun p => L p /\ L (boxdot_translate p).

Record boxdot_normal_logic (L : modal_logic) : Prop := {
  boxdot_normal_contains_K : forall p, K_proves p -> L p;
  boxdot_normal_mp : forall p q, L (Imp p q) -> L p -> L q;
  boxdot_normal_nec : forall p, L p -> L (Box p)
}.

Lemma normal_system_is_boxdot_normal :
  forall Ax,
    boxdot_normal_logic (@normal_proves Ax nat).
Proof.
  intro Ax; constructor.
  - intros p Hp; now apply K_proves_normal.
  - intros p q; apply Np_mp.
  - intros p; apply Np_nec.
Qed.

Definition BoxdotProperty (L0 : modal_logic) : Prop :=
  forall L,
    boxdot_normal_logic L ->
    (forall p, boxdot_preimage L p <-> L0 p) ->
    logic_included L L0.

Definition StrongBoxdotProperty (L0 : modal_logic) : Prop :=
  forall L,
    boxdot_normal_logic L ->
    logic_included (boxdot_preimage L) L0 ->
    logic_included L L0.

Lemma BDP_of_SBDP :
  forall L0,
    StrongBoxdotProperty L0 -> BoxdotProperty L0.
Proof.
  intros L0 Hstrong L Hnormal Heq.
  apply Hstrong; [exact Hnormal |].
  intros p Hp; now apply (proj1 (Heq p)).
Qed.

Definition logic_sound_on (L : modal_logic) (C : frame_class) : Prop :=
  forall p, L p -> forall F, C F -> valid F p.

Definition logic_complete_on (L : modal_logic) (C : frame_class) : Prop :=
  forall p, (forall F, C F -> valid F p) -> L p.

(** The upstream proof of Jeřábek's theorem uses its global-consequence
    compactness theorem, finite contexts, subformula traversal, and a fresh
    atom construction.  Those APIs do not exist in this repository yet.
    [jerabek_global_consequence_bridge] isolates precisely the missing
    counterexample-lifting conclusion as an explicit proposition; it is not
    assumed globally and no axiom is introduced. *)
Definition jerabek_global_consequence_bridge
    (L0 : modal_logic) (C : frame_class) : Prop :=
  logic_included (@KT_proves nat) L0 ->
  logic_sound_on L0 C ->
  logic_complete_on L0 C ->
  jerabek_frameclass_closed C ->
  forall L,
    boxdot_normal_logic L ->
    ~ logic_included L L0 ->
    exists chi,
      L chi /\ L (boxdot_translate chi) /\ ~ L0 chi.

Theorem jerabek_SBDP :
  forall (L0 : modal_logic) (C : frame_class),
    logic_included (@KT_proves nat) L0 ->
    logic_sound_on L0 C ->
    logic_complete_on L0 C ->
    jerabek_frameclass_closed C ->
    jerabek_global_consequence_bridge L0 C ->
    StrongBoxdotProperty L0.
Proof.
  intros L0 C HKT Hsound Hcomplete Htwice Hbridge.
  intros L Hnormal Hpre p Hp.
  apply NNPP; intro Hnotp.
  assert (Hnotincl : ~ logic_included L L0).
  { intro Hincl; exact (Hnotp (Hincl p Hp)). }
  destruct (Hbridge HKT Hsound Hcomplete Htwice L Hnormal Hnotincl)
    as [chi [Hchi [Hchib Hnotchi]]].
  apply Hnotchi, Hpre; now split.
Qed.

Theorem jerabek_BDP :
  forall (L0 : modal_logic) (C : frame_class),
    logic_included (@KT_proves nat) L0 ->
    logic_sound_on L0 C ->
    logic_complete_on L0 C ->
    jerabek_frameclass_closed C ->
    jerabek_global_consequence_bridge L0 C ->
    BoxdotProperty L0.
Proof.
  intros L0 C HKT Hsound Hcomplete Htwice Hbridge.
  apply BDP_of_SBDP.
  exact (@jerabek_SBDP L0 C HKT Hsound Hcomplete Htwice Hbridge).
Qed.

(** Named logics used by the six upstream corollaries. *)

Definition schema_Point2 : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Point2 q.

Definition KTB_schema := schema_union schema_T schema_B.
Definition S4Point2_schema := schema_union S4_schema schema_Point2.
Definition S4Point3_schema := schema_union S4_schema schema_Point3.

Definition KTB_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KTB_schema AtomType.

Definition S4Point2_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4Point2_schema AtomType.

Definition S4Point3_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4Point3_schema AtomType.

Lemma schema_Point2_valid_on_piecewise_strongly_convergent :
  forall F,
    frame_piecewise_strongly_convergent F ->
    schema_valid_on_frame schema_Point2 F.
Proof.
  intros F Hconv AtomType p [q ->].
  now apply valid_Point2_of_strong_confluence.
Qed.

Lemma KT_logic_extends_KT :
  logic_included (@KT_proves nat) (@KT_proves nat).
Proof. firstorder. Qed.

Lemma KTB_logic_extends_KT :
  logic_included (@KT_proves nat) (@KTB_proves nat).
Proof.
  intros p Hp; eapply normal_proves_weaken; [|exact Hp].
  intros AtomType q Hq; now left.
Qed.

Lemma S4_logic_extends_KT :
  logic_included (@KT_proves nat) (@S4_proves nat).
Proof. intros p; apply KT_weaker_than_S4. Qed.

Lemma S4Point2_logic_extends_KT :
  logic_included (@KT_proves nat) (@S4Point2_proves nat).
Proof.
  intros p Hp; eapply normal_proves_weaken; [|exact Hp].
  intros AtomType q Hq; left; now left.
Qed.

Lemma S4Point3_logic_extends_KT :
  logic_included (@KT_proves nat) (@S4Point3_proves nat).
Proof.
  intros p Hp; eapply normal_proves_weaken; [|exact Hp].
  intros AtomType q Hq; left; now left.
Qed.

Lemma S5_logic_extends_KT :
  logic_included (@KT_proves nat) (@S5_proves nat).
Proof. intros p; apply KT_weaker_than_S5. Qed.

Lemma KT_logic_sound :
  logic_sound_on (@KT_proves nat) KT_frame_class.
Proof.
  intros p Hp F Hrefl.
  now apply KT_proves_sound_on_reflexive_frame.
Qed.

Lemma KTB_logic_sound :
  logic_sound_on (@KTB_proves nat) KTB_frame_class.
Proof.
  intros p Hp F [Hrefl Hsym].
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_T_valid_on_reflexive.
  - now apply schema_B_valid_on_symmetric.
Qed.

Lemma S4_logic_sound :
  logic_sound_on (@S4_proves nat) S4_frame_class.
Proof.
  intros p Hp F [Hrefl Htrans].
  now apply S4_proves_sound_on_preorder_frame.
Qed.

Lemma S4Point2_logic_sound :
  logic_sound_on (@S4Point2_proves nat) S4Point2_frame_class.
Proof.
  intros p Hp F [Hrefl [Htrans Hconv]].
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply schema_Point2_valid_on_piecewise_strongly_convergent.
Qed.

Lemma S4Point3_logic_sound :
  logic_sound_on (@S4Point3_proves nat) S4Point3_frame_class.
Proof.
  intros p Hp F [Hrefl [Htrans Hconn]].
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply schema_Point3_valid_on_piecewise_strongly_connected.
Qed.

Lemma S5_logic_sound :
  logic_sound_on (@S5_proves nat) S5_frame_class.
Proof.
  intros p Hp F [Hrefl [Htrans Hsym]].
  apply S5_proves_sound_on_reflexive_euclidean_frame;
    [exact Hrefl | | exact Hp].
  intros x y z Rxy Rxz.
  exact (Htrans y x z (Hsym x y Rxy) Rxz).
Qed.

(** Each named corollary below is conditional only on the two pieces still
    absent locally: completeness for its named frame class and the global
    finite-consequence bridge isolated above.  The extension, soundness, and
    doubling-closure obligations are discharged here. *)

Theorem KT_BDP :
  logic_complete_on (@KT_proves nat) KT_frame_class ->
  jerabek_global_consequence_bridge (@KT_proves nat) KT_frame_class ->
  BoxdotProperty (@KT_proves nat).
Proof.
  intros Hcomplete Hbridge.
  exact (@jerabek_BDP (@KT_proves nat) KT_frame_class
    KT_logic_extends_KT KT_logic_sound Hcomplete
    KT_frameclass_jerabek Hbridge).
Qed.

Definition boxdot_conjecture := KT_BDP.

Theorem KTB_BDP :
  logic_complete_on (@KTB_proves nat) KTB_frame_class ->
  jerabek_global_consequence_bridge (@KTB_proves nat) KTB_frame_class ->
  BoxdotProperty (@KTB_proves nat).
Proof.
  intros Hcomplete Hbridge.
  exact (@jerabek_BDP (@KTB_proves nat) KTB_frame_class
    KTB_logic_extends_KT KTB_logic_sound Hcomplete
    KTB_frameclass_jerabek Hbridge).
Qed.

Theorem S4_BDP :
  logic_complete_on (@S4_proves nat) S4_frame_class ->
  jerabek_global_consequence_bridge (@S4_proves nat) S4_frame_class ->
  BoxdotProperty (@S4_proves nat).
Proof.
  intros Hcomplete Hbridge.
  exact (@jerabek_BDP (@S4_proves nat) S4_frame_class
    S4_logic_extends_KT S4_logic_sound Hcomplete
    S4_frameclass_jerabek Hbridge).
Qed.

Theorem S4Point2_BDP :
  logic_complete_on (@S4Point2_proves nat) S4Point2_frame_class ->
  jerabek_global_consequence_bridge
    (@S4Point2_proves nat) S4Point2_frame_class ->
  BoxdotProperty (@S4Point2_proves nat).
Proof.
  intros Hcomplete Hbridge.
  exact (@jerabek_BDP (@S4Point2_proves nat) S4Point2_frame_class
    S4Point2_logic_extends_KT S4Point2_logic_sound Hcomplete
    S4Point2_frameclass_jerabek Hbridge).
Qed.

Theorem S4Point3_BDP :
  logic_complete_on (@S4Point3_proves nat) S4Point3_frame_class ->
  jerabek_global_consequence_bridge
    (@S4Point3_proves nat) S4Point3_frame_class ->
  BoxdotProperty (@S4Point3_proves nat).
Proof.
  intros Hcomplete Hbridge.
  exact (@jerabek_BDP (@S4Point3_proves nat) S4Point3_frame_class
    S4Point3_logic_extends_KT S4Point3_logic_sound Hcomplete
    S4Point3_frameclass_jerabek Hbridge).
Qed.

Theorem S5_BDP :
  logic_complete_on (@S5_proves nat) S5_frame_class ->
  jerabek_global_consequence_bridge (@S5_proves nat) S5_frame_class ->
  BoxdotProperty (@S5_proves nat).
Proof.
  intros Hcomplete Hbridge.
  exact (@jerabek_BDP (@S5_proves nat) S5_frame_class
    S5_logic_extends_KT S5_logic_sound Hcomplete
    S5_frameclass_jerabek Hbridge).
Qed.

(** * Source-name compatibility aliases

    These retain the recognizable theorem names from the pinned Lean
    modules while the primary Coq declarations above use descriptive names. *)

Definition iff_boxdotboxdot := boxdot_translate_idempotent_truth.
Definition boxdot_and := boxdot_translate_and_truth.
Definition boxdotTranslate_lconj := boxdot_translate_list_conj_truth.
Definition iff_boxdotTranslateMultibox_boxdotTranslateBoxlt :=
  boxdot_translate_box_iter_truth.
Definition iff_boxdot_reflexive_closure :=
  boxdot_reflexive_closure_truth.
Definition iff_frame_boxdot_reflexive_closure :=
  boxdot_reflexive_closure_valid_iff.
Definition iff_reflexivize_irreflexivize :=
  boxdot_irreflexivize_reflexive_truth.
Definition iff_reflexivize_irreflexivize' :=
  boxdot_irreflexivize_reflexive_valid_iff.

Definition provable_boxdotTranslated_K4_of_provable_S4 :=
  S4_proves_to_K4_boxdot.
Definition provable_S4_iff_boxdotTranslated :=
  S4_proves_iff_boxdot_translate.
Definition provable_S4_of_provable_boxdotTranslated_K4 :=
  K4_boxdot_proves_to_S4.
Definition iff_boxdotTranslatedK4_S4 := K4_boxdot_iff_S4.

Definition provable_boxdot_GL_of_provable_Grz :=
  Grz_proves_to_GL_boxdot.
Definition provable_Grz_of_provable_boxdot_GL :=
  GL_boxdot_proves_to_Grz.
Definition iff_provable_boxdot_GL_provable_Grz := GL_boxdot_iff_Grz.

Definition provable_boxdotTranslated_GLPoint3_of_GrzPoint3 :=
  GrzPoint3_proves_to_GLPoint3_boxdot.
Definition provable_GrzPoint3_of_boxdotTranslated_GLPoint3 :=
  GLPoint3_boxdot_proves_to_GrzPoint3.

Definition provable_boxdotTranslated_Ver_of_Triv :=
  Triv_proves_to_Ver_boxdot.
Definition provable_Triv_of_boxdotTranslated_Ver :=
  Ver_boxdot_proves_to_Triv.
