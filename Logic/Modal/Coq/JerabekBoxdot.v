(**
  Jeřábek's boxdot theorem.

  This module discharges the global-consequence bridge that [Boxdot]
  previously exposed as a hypothesis.  It follows the finite-context proof
  from Foundation's pinned [Modal/Boxdot/Jerabek.lean], but uses lists for
  finite sets and the repository's generic [global_consequence] calculus.
*)

From Stdlib Require Import
  Arith.PeanoNat Lia Lists.List Logic.Classical_Prop Logic.Classical_Pred_Type.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence CorrespondenceExtensions
  FrameTransformations Filtration FiltrationExtensions
  HilbertK CanonicalK NormalHilbert LogicInfrastructure Boxdot CanonicalExtensions CanonicalTB
  CanonicalPoint2 CanonicalPoint3 Modality.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * A fresh natural-number atom and the finite Jeřábek context *)

Fixpoint jerabek_fresh_atom (p : formula nat) : nat :=
  match p with
  | Atom a => S a
  | Bottom => 0
  | Imp q r => Nat.max (jerabek_fresh_atom q) (jerabek_fresh_atom r)
  | Box q => jerabek_fresh_atom q
  end.

Lemma jerabek_fresh_atom_bounds_subformula :
  forall (p : formula nat) a,
    In (Atom a) (subformulas p) -> a < jerabek_fresh_atom p.
Proof.
  intro p; induction p as [b | | p IHp q IHq | p IHp];
    intros a Ha; simpl in Ha |- *.
  - destruct Ha as [Ha | []]. inversion Ha; lia.
  - destruct Ha as [Ha | []]. discriminate.
  - destruct Ha as [Ha | Ha]; [discriminate |].
    apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + eapply Nat.lt_le_trans; [now apply IHp | apply Nat.le_max_l].
    + eapply Nat.lt_le_trans; [now apply IHq | apply Nat.le_max_r].
  - destruct Ha as [Ha | Ha]; [discriminate |].
    now apply IHp.
Qed.

Corollary jerabek_fresh_atom_not_subformula :
  forall p : formula nat,
    ~ In (Atom (jerabek_fresh_atom p)) (subformulas p).
Proof.
  intros p Hin.
  pose proof (jerabek_fresh_atom_bounds_subformula Hin).
  lia.
Qed.

Definition jerabek_generator
    (fresh : nat) (b : bool) (p : formula nat) : formula nat :=
  Imp (Box (Imp (formula_flag (Atom fresh) b) p)) p.

Fixpoint jerabek_context
    (fresh : nat) (Gamma : list (formula nat)) : list (formula nat) :=
  match Gamma with
  | [] => []
  | p :: rest =>
      jerabek_generator fresh true p ::
      jerabek_generator fresh false p ::
      jerabek_context fresh rest
  end.

Definition jerabek_context_for (target : formula nat) : list (formula nat) :=
  jerabek_context (jerabek_fresh_atom target) (subformulas target).

Definition jerabek_boxdot_context (target : formula nat)
    : list (formula nat) :=
  map boxdot_translate (jerabek_context_for target).

Lemma jerabek_generator_in_context :
  forall fresh Gamma p b,
    In p Gamma -> In (jerabek_generator fresh b p)
      (jerabek_context fresh Gamma).
Proof.
  intros fresh Gamma; induction Gamma as [|q Gamma IH];
    intros p b Hp; simpl in *.
  - contradiction.
  - destruct Hp as [-> | Hp].
    + destruct b; simpl; auto.
    + right; right; now apply IH.
Qed.

Lemma jerabek_context_spec :
  forall fresh Gamma r,
    In r (jerabek_context fresh Gamma) <->
    exists p b, In p Gamma /\ r = jerabek_generator fresh b p.
Proof.
  intros fresh Gamma; induction Gamma as [|q Gamma IH]; intro r; simpl.
  - split; [contradiction |].
    intros [p [b [[] _]]].
  - split.
    + intros [Hr | [Hr | Hr]].
      * exists q, true; auto.
      * exists q, false; auto.
      * apply IH in Hr. destruct Hr as [p [b [Hp ->]]].
        exists p, b; auto.
    + intros [p [b [[Hp | Hp] ->]]].
      * subst p; destruct b; simpl; auto.
      * right; right; apply IH. exists p, b; auto.
Qed.

Lemma jerabek_boxdot_generator_in_context :
  forall target p b,
    In p (subformulas target) ->
    In (boxdot_translate
          (jerabek_generator (jerabek_fresh_atom target) b p))
       (jerabek_boxdot_context target).
Proof.
  intros target p b Hp.
  unfold jerabek_boxdot_context, jerabek_context_for.
  apply in_map.
  now apply jerabek_generator_in_context.
Qed.

(** Exact structural equations used to turn the finite global-consequence
    antecedent back into one boxdot translation. *)

Lemma boxdot_translate_logic_list_conj2 :
  forall Gamma : list (formula nat),
    boxdot_translate (logic_list_conj2 Gamma) =
    logic_list_conj2 (map boxdot_translate Gamma).
Proof.
  intro Gamma; induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - destruct Gamma as [|q Gamma]; simpl in *; [reflexivity |].
    now rewrite IH.
Qed.

Lemma boxdot_translate_box_iter_global :
  forall n (p : formula nat),
    boxdot_translate (box_iter n p) =
    global_box_le n (boxdot_translate p).
Proof.
  intro n; induction n as [|n IH]; intro p; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(** * The two local proof-theoretic claims *)

Lemma jerabek_global_K_valid :
  forall L (Hnormal : boxdot_normal_logic L) X p,
    valid_on_all_frames p -> global_consequence L X p.
Proof.
  intros L Hnormal X p Hp.
  apply GC_theorem, (boxdot_normal_contains_K Hnormal), K_complete, Hp.
Qed.

Lemma jerabek_two_generators_K_valid :
  forall fresh p,
    valid_on_all_frames
      (Imp (boxdot_translate (jerabek_generator fresh true p))
        (Imp (boxdot_translate (jerabek_generator fresh false p))
          (Imp (Box (boxdot_translate p)) (boxdot_translate p)))).
Proof.
  intros fresh p F V w Htrue Hfalse Hbox.
  destruct (classic (V fresh w)) as [Hat | Hnat].
  - apply Hfalse.
    apply (proj2 (@satisfies_and nat F V w
      (Imp (formula_flag (Atom fresh) false) (boxdot_translate p))
      (Box (Imp (formula_flag (Atom fresh) false)
        (boxdot_translate p))))).
    split.
    + intros Hneg. exfalso. exact (Hneg Hat).
    + intros y Rwy _. now apply Hbox.
  - apply Htrue.
    apply (proj2 (@satisfies_and nat F V w
      (Imp (formula_flag (Atom fresh) true) (boxdot_translate p))
      (Box (Imp (formula_flag (Atom fresh) true)
        (boxdot_translate p))))).
    split.
    + intros Hatom. exfalso. exact (Hnat Hatom).
    + intros y Rwy _. now apply Hbox.
Qed.

Lemma jerabek_global_boxdot_T :
  forall L (Hnormal : boxdot_normal_logic L) target p,
    In p (subformulas target) ->
    global_consequence L
      (fun r => In r (jerabek_boxdot_context target))
      (Imp (Box (boxdot_translate p)) (boxdot_translate p)).
Proof.
  intros L Hnormal target p Hp.
  eapply global_consequence_modus_ponens.
  - eapply global_consequence_modus_ponens.
    + apply jerabek_global_K_valid; [exact Hnormal |].
      apply jerabek_two_generators_K_valid.
    + apply GC_context.
      now apply jerabek_boxdot_generator_in_context.
  - apply GC_context.
    now apply jerabek_boxdot_generator_in_context.
Qed.

Lemma jerabek_imp_congruence_K_valid :
  forall p p' q q' : formula nat,
    valid_on_all_frames
      (Imp (Iff p p')
        (Imp (Iff q q') (Iff (Imp p q) (Imp p' q')))).
Proof.
  intros p p' q q' F V w Hp Hq.
  apply (proj2 (@satisfies_iff nat F V w (Imp p q) (Imp p' q'))).
  apply (proj1 (@satisfies_iff nat F V w p p')) in Hp.
  apply (proj1 (@satisfies_iff nat F V w q q')) in Hq.
  split; intros Himp Harg.
  - apply (proj1 Hq), Himp, (proj2 Hp), Harg.
  - apply (proj2 Hq), Himp, (proj1 Hp), Harg.
Qed.

Lemma jerabek_box_congruence_K_valid :
  forall p q : formula nat,
    valid_on_all_frames
      (Imp (Box (Iff p q)) (Iff (Box p) (Box q))).
Proof.
  intros p q F V w Hbox.
  apply (proj2 (@satisfies_iff nat F V w (Box p) (Box q))).
  split; intros Hp y Rwy.
  - pose proof (proj1 (@satisfies_iff nat F V y p q)
      (Hbox y Rwy)) as Heq.
    exact (proj1 Heq (Hp y Rwy)).
  - pose proof (proj1 (@satisfies_iff nat F V y p q)
      (Hbox y Rwy)) as Heq.
    exact (proj2 Heq (Hp y Rwy)).
Qed.

Lemma jerabek_boxdot_box_step_K_valid :
  forall p q : formula nat,
    valid_on_all_frames
      (Imp (Iff (Box p) (Box q))
        (Imp (Imp (Box q) q)
          (Iff (Box p) (And q (Box q))))).
Proof.
  intros p q F V w Hboxes HT.
  apply (proj2 (@satisfies_iff nat F V w (Box p) (And q (Box q)))).
  apply (proj1 (@satisfies_iff nat F V w (Box p) (Box q))) in Hboxes.
  split.
  - intro Hboxp.
    pose proof (proj1 Hboxes Hboxp) as Hboxq.
    apply (proj2 (@satisfies_and nat F V w q (Box q))).
    split; [now apply HT | exact Hboxq].
  - intro Hand.
    apply (proj2 Hboxes).
    exact (proj2 (proj1 (@satisfies_and nat F V w q (Box q)) Hand)).
Qed.

Theorem jerabek_subformula_boxdot_equiv :
  forall L (Hnormal : boxdot_normal_logic L) target p,
    In p (subformulas target) ->
    global_consequence L
      (fun r => In r (jerabek_boxdot_context target))
      (Iff p (boxdot_translate p)).
Proof.
  intros L Hnormal target p; induction p as [a | | p IHp q IHq | p IHp];
    intro Hsub.
  - apply jerabek_global_K_valid; [exact Hnormal |].
    intros F V w. apply (proj2 (@satisfies_iff nat F V w (Atom a) (Atom a))).
    reflexivity.
  - apply jerabek_global_K_valid; [exact Hnormal |].
    intros F V w. apply (proj2 (@satisfies_iff nat F V w Bottom Bottom)).
    reflexivity.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left, subformulas_self. }
    assert (Hsubq : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right, subformulas_self. }
    eapply global_consequence_modus_ponens.
    + eapply global_consequence_modus_ponens.
      * apply jerabek_global_K_valid; [exact Hnormal |].
        apply jerabek_imp_congruence_K_valid.
      * now apply IHp.
    + now apply IHq.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box, subformulas_self. }
    pose proof (IHp Hsubp) as Hiff.
    pose proof (global_consequence_necessitation Hiff) as Hboxed_iff.
    assert (Hbox_cong :
      global_consequence L
        (fun r => In r (jerabek_boxdot_context target))
        (Iff (Box p) (Box (boxdot_translate p)))).
    { eapply global_consequence_modus_ponens.
      - apply jerabek_global_K_valid; [exact Hnormal |].
        apply jerabek_box_congruence_K_valid.
      - exact Hboxed_iff. }
    change (global_consequence L
      (fun r => In r (jerabek_boxdot_context target))
      (Iff (Box p)
        (And (boxdot_translate p) (Box (boxdot_translate p))))).
    eapply global_consequence_modus_ponens.
    + eapply global_consequence_modus_ponens.
      * apply jerabek_global_K_valid; [exact Hnormal |].
        apply jerabek_boxdot_box_step_K_valid.
      * exact Hbox_cong.
    + now apply jerabek_global_boxdot_T.
Qed.

Lemma jerabek_global_boxdot_target :
  forall L (Hnormal : boxdot_normal_logic L) target,
    L target ->
    global_consequence L
      (fun r => In r (jerabek_boxdot_context target))
      (boxdot_translate target).
Proof.
  intros L Hnormal target Htarget.
  pose proof (jerabek_subformula_boxdot_equiv Hnormal
    (subformulas_self target)) as Hiff.
  eapply global_consequence_modus_ponens.
  - eapply global_consequence_modus_ponens.
    + apply jerabek_global_K_valid; [exact Hnormal |].
      intros F V w Heq.
      apply (proj1 (@satisfies_iff nat F V w target
        (boxdot_translate target))) in Heq.
      exact (proj1 Heq).
    + exact Hiff.
  - now apply GC_theorem.
Qed.

(** * The doubled countermodel *)

Definition jerabek_twice_valuation {F : frame}
    (fresh : nat) (V : valuation nat F) : valuation nat (frame_twice F) :=
  fun a x =>
    if Nat.eq_dec a fresh then snd x = true else V a (fst x).

Lemma jerabek_selected_flag_true :
  forall F (V : valuation nat F) fresh w b,
    satisfies (frame_twice F) (jerabek_twice_valuation fresh V)
      (w, b) (formula_flag (Atom fresh) b).
Proof.
  intros F V fresh w []; unfold formula_flag; simpl.
  - unfold jerabek_twice_valuation; simpl.
    destruct (Nat.eq_dec fresh fresh); [reflexivity | contradiction].
  - unfold jerabek_twice_valuation; simpl.
    destruct (Nat.eq_dec fresh fresh); [discriminate | contradiction].
Qed.

Theorem jerabek_doubled_subformula_truth :
  forall target F (V : valuation nat F) p,
    In p (subformulas target) -> forall w b,
    satisfies (frame_twice F)
      (jerabek_twice_valuation (jerabek_fresh_atom target) V)
      (w, b) p <-> satisfies F V w p.
Proof.
  intros target F V p; induction p as [a | | p IHp q IHq | p IHp];
    intros Hsub w b; simpl.
  - unfold jerabek_twice_valuation; simpl.
    destruct (Nat.eq_dec a (jerabek_fresh_atom target)) as [Heq | Hne].
    + subst a. exfalso. apply (@jerabek_fresh_atom_not_subformula target).
      exact Hsub.
    + reflexivity.
  - reflexivity.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left, subformulas_self. }
    assert (Hsubq : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right, subformulas_self. }
    rewrite (IHp Hsubp w b), (IHq Hsubq w b). reflexivity.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box, subformulas_self. }
    split.
    + intros Hbox y Rwy.
      apply (proj1 (IHp Hsubp y b)).
      exact (Hbox (y, b) Rwy).
    + intros Hbox [y c] Rwy.
      apply (proj2 (IHp Hsubp y c)).
      exact (Hbox y Rwy).
Qed.

Lemma jerabek_doubled_generator_true :
  forall target F (V : valuation nat F),
    frame_reflexive F -> forall p,
    In p (subformulas target) -> forall b w,
    satisfies (frame_twice F)
      (jerabek_twice_valuation (jerabek_fresh_atom target) V)
      w (jerabek_generator (jerabek_fresh_atom target) b p).
Proof.
  intros target F V Hrefl p Hsub b [w c] Hbox.
  apply (proj2 (@jerabek_doubled_subformula_truth
    target F V p Hsub w c)).
  apply NNPP; intro Hnot.
  apply Hnot.
  apply (proj1 (@jerabek_doubled_subformula_truth
    target F V p Hsub w b)).
  apply Hbox with (u := (w, b)).
  - apply Hrefl.
  - apply jerabek_selected_flag_true.
Qed.

Lemma satisfies_logic_list_conj2_jerabek :
  forall F (V : valuation nat F) w Gamma,
    satisfies F V w (logic_list_conj2 Gamma) <->
    forall p, In p Gamma -> satisfies F V w p.
Proof.
  intros F V w Gamma; induction Gamma as [|p Gamma IH].
  - simpl; split.
    + intros _ q Hq; contradiction.
    + intros _ Hfalse; exact Hfalse.
  - destruct Gamma as [|q Gamma].
    + simpl; split.
      * intros Hp r [-> | Hr]; [exact Hp | contradiction].
      * intro Hall. apply Hall. now left.
    + change
        (satisfies F V w (And p (logic_list_conj2 (q :: Gamma))) <->
         forall r, In r (p :: q :: Gamma) -> satisfies F V w r).
      rewrite satisfies_and, IH.
      split.
      * intros [Hp Hall] r [-> | Hr]; [exact Hp | now apply Hall].
      * intro Hall; split.
        -- apply Hall. now left.
        -- intros r Hr. apply Hall. now right.
Qed.

Lemma jerabek_doubled_context_true :
  forall target F (V : valuation nat F),
    frame_reflexive F -> forall w,
    satisfies (frame_twice F)
      (jerabek_twice_valuation (jerabek_fresh_atom target) V) w
      (logic_list_conj2 (jerabek_context_for target)).
Proof.
  intros target F V Hrefl w.
  apply (proj2 (@satisfies_logic_list_conj2_jerabek
    (frame_twice F)
    (jerabek_twice_valuation (jerabek_fresh_atom target) V)
    w (jerabek_context_for target))).
  intros r Hr.
  unfold jerabek_context_for in Hr.
  apply jerabek_context_spec in Hr.
  destruct Hr as [p [b [Hp ->]]].
  now apply jerabek_doubled_generator_true.
Qed.

(** * The discharged bridge and Jeřábek's theorem *)

Polymorphic Definition jerabek_frameclass_closed_poly@{u}
    (C : frame_class@{u}) : Prop :=
  forall F, C F -> C (frame_twice@{u u} F).

Polymorphic Lemma KT_frameclass_jerabek_poly@{u} :
  jerabek_frameclass_closed_poly@{u} KT_frame_class@{u}.
Proof. intros F HF; now apply frame_twice_reflexive. Qed.

Polymorphic Lemma KTB_frameclass_jerabek_poly@{u} :
  jerabek_frameclass_closed_poly@{u} KTB_frame_class@{u}.
Proof.
  intros F [HR HS]; split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_symmetric.
Qed.

Polymorphic Lemma S4_frameclass_jerabek_poly@{u} :
  jerabek_frameclass_closed_poly@{u} S4_frame_class@{u}.
Proof.
  intros F [HR HT]; split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
Qed.

Polymorphic Lemma S4Point2_frameclass_jerabek_poly@{u} :
  jerabek_frameclass_closed_poly@{u} S4Point2_frame_class@{u}.
Proof.
  intros F [HR [HT HC]]; repeat split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
  - now apply frame_twice_piecewise_strongly_convergent.
Qed.

Polymorphic Lemma S4Point3_frameclass_jerabek_poly@{u} :
  jerabek_frameclass_closed_poly@{u} S4Point3_frame_class@{u}.
Proof.
  intros F [HR [HT HC]]; repeat split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
  - now apply frame_twice_piecewise_strongly_connected.
Qed.

Polymorphic Lemma S5_frameclass_jerabek_poly@{u} :
  jerabek_frameclass_closed_poly@{u} S5_frame_class@{u}.
Proof.
  intros F [HR [HT HS]]; repeat split.
  - now apply frame_twice_reflexive.
  - now apply frame_twice_transitive.
  - now apply frame_twice_symmetric.
Qed.

Polymorphic Theorem jerabek_counterexample_lift :
  forall (L0 : modal_logic) (C : frame_class),
    logic_included (@KT_proves nat) L0 ->
    logic_sound_on L0 C ->
    logic_complete_on L0 C ->
    jerabek_frameclass_closed_poly C ->
    forall L,
    boxdot_normal_logic L ->
    ~ logic_included L L0 ->
    exists chi,
      L chi /\ L (boxdot_translate chi) /\ ~ L0 chi.
Proof.
  intros L0 C HKT Hsound Hcomplete Htwice.
  intros L Hnormal Hnotincluded.
  unfold logic_included in Hnotincluded.
  apply not_all_ex_not in Hnotincluded.
  destruct Hnotincluded as [target Htarget].
  assert (HL : L target) by tauto.
  assert (HnotL0 : ~ L0 target) by tauto.
  pose proof (boxdot_normal_to_normal_logic Hnormal) as Hnormal_logic.
  pose proof (quasi_classical (normal_quasi Hnormal_logic)) as Hclass.
  pose proof (jerabek_global_boxdot_target Hnormal HL) as Hglobal.
  destruct
    (proj1
      (@global_consequence_iff_finite_foundation_box_le_provable
        nat L Hnormal_logic
        (fun r => In r (jerabek_boxdot_context target))
        (boxdot_translate target))
      Hglobal)
    as [Gamma [n [HGamma Hdeduction]]].
  assert (Hcontext_to_Gamma :
    L (Imp
      (logic_list_conj2 (jerabek_boxdot_context target))
      (logic_list_conj2 Gamma))).
  {
    eapply logic_imp_trans; [exact Hclass | |].
    - apply logic_list_conj2_to_conj; exact Hclass.
    - eapply logic_imp_trans; [exact Hclass | |].
      + apply logic_list_conj_incl; [exact Hclass |].
        intros r Hr. exact (HGamma r Hr).
      + apply logic_list_conj_to_conj2; exact Hclass.
  }
  assert (Hfull_deduction :
    L (Imp
      (foundation_box_le n
        (logic_list_conj2 (jerabek_boxdot_context target)))
      (boxdot_translate target))).
  {
    eapply logic_imp_trans; [exact Hclass | |exact Hdeduction].
    now apply logic_foundation_box_le_regularity.
  }
  set (chi := Imp
    (box_iter n (logic_list_conj2 (jerabek_context_for target))) target).
  exists chi; repeat split.
  - unfold chi. apply logic_imply_intro; [exact Hclass | exact HL].
  - unfold chi; simpl.
    rewrite boxdot_translate_box_iter_global.
    rewrite boxdot_translate_logic_list_conj2.
    eapply logic_imp_trans; [exact Hclass | |exact Hfull_deduction].
    apply logic_global_box_le_to_foundation; exact Hnormal_logic.
  - intro HL0chi.
    assert (Hnotvalid : ~ (forall F, C F -> valid F target)).
    { intro Hvalid. apply HnotL0, Hcomplete, Hvalid. }
    apply not_all_ex_not in Hnotvalid.
    destruct Hnotvalid as [F HF].
    assert (HCF : C F) by tauto.
    assert (HnotvalidF : ~ valid F target) by tauto.
    unfold valid in HnotvalidF.
    apply not_all_ex_not in HnotvalidF.
    destruct HnotvalidF as [V HV].
    apply not_all_ex_not in HV.
    destruct HV as [w Hw].
    assert (HKT_T : @KT_proves nat (T (Atom 0))).
    { apply Np_extra. exists (Atom 0). reflexivity. }
    assert (Hrefl : frame_reflexive F).
    { apply reflexive_of_valid_T.
      exact (Hsound (T (Atom 0)) (HKT (T (Atom 0)) HKT_T) F HCF). }
    pose (Vtwice := jerabek_twice_valuation
      (jerabek_fresh_atom target) V).
    assert (Hantecedent :
      satisfies (frame_twice F) Vtwice (w, true)
        (box_iter n
          (logic_list_conj2 (jerabek_context_for target)))).
    { apply (proj2 (@satisfies_box_iter nat (frame_twice F) Vtwice n
        (w, true) (logic_list_conj2 (jerabek_context_for target)))).
      intros u _. unfold Vtwice.
      now apply jerabek_doubled_context_true. }
    pose proof
      (Hsound chi HL0chi (frame_twice F) (Htwice F HCF)
        Vtwice (w, true)) as Hchi.
    unfold chi in Hchi.
    apply Hw.
    apply (proj1 (@jerabek_doubled_subformula_truth
      target F V target (subformulas_self target) w true)).
    exact (Hchi Hantecedent).
Qed.

Theorem jerabek_global_consequence_bridge_checked :
  forall (L0 : modal_logic) (C : frame_class),
    jerabek_global_consequence_bridge L0 C.
Proof.
  intros L0 C HKT Hsound Hcomplete Htwice L Hnormal Hnotincluded.
  exact (jerabek_counterexample_lift
    HKT Hsound Hcomplete Htwice Hnormal Hnotincluded).
Qed.

Polymorphic Theorem jerabek_SBDP_unconditional :
  forall (L0 : modal_logic) (C : frame_class),
    logic_included (@KT_proves nat) L0 ->
    logic_sound_on L0 C ->
    logic_complete_on L0 C ->
    jerabek_frameclass_closed_poly C ->
    StrongBoxdotProperty L0.
Proof.
  intros L0 C HKT Hsound Hcomplete Htwice.
  intros L Hnormal Hpre p Hp.
  apply NNPP; intro Hnotp.
  assert (Hnotincluded : ~ logic_included L L0).
  { intro Hincluded. exact (Hnotp (Hincluded p Hp)). }
  destruct (jerabek_counterexample_lift
    HKT Hsound Hcomplete Htwice Hnormal Hnotincluded)
    as [chi [Hchi [Hboxdot Hnotchi]]].
  apply Hnotchi, Hpre. now split.
Qed.

Polymorphic Theorem jerabek_BDP_unconditional :
  forall (L0 : modal_logic) (C : frame_class),
    logic_included (@KT_proves nat) L0 ->
    logic_sound_on L0 C ->
    logic_complete_on L0 C ->
    jerabek_frameclass_closed_poly C ->
    BoxdotProperty L0.
Proof.
  intros L0 C HKT Hsound Hcomplete Htwice.
  apply BDP_of_SBDP.
  exact (jerabek_SBDP_unconditional
    HKT Hsound Hcomplete Htwice).
Qed.

(** * Unconditional named corollaries *)

Lemma KT_logic_complete_jerabek :
  logic_complete_on (@KT_proves nat) KT_frame_class@{Set}.
Proof.
  intros p Hsmall. apply KT_complete.
  intros F Hrefl V w.
  apply (proj1 (@finest_filtration_truth_at_class
    nat F V p p (subformulas_self p) w)).
  apply (Hsmall (@finest_filtered_frame nat F V p)).
  now apply finest_preserves_reflexive.
Qed.

Lemma KTB_logic_complete_jerabek :
  logic_complete_on (@Boxdot.KTB_proves nat) KTB_frame_class@{Set}.
Proof.
  intros p Hsmall. apply CanonicalTB.KTB_finite_complete.
  intros F [_ [Hrefl Hsym]] V w.
  apply (Hsmall F); now split.
Qed.

Lemma S4_logic_complete_jerabek :
  logic_complete_on (@S4_proves nat) S4_frame_class@{Set}.
Proof.
  intros p Hsmall. apply S4_finite_complete.
  intros F [_ [Hrefl Htrans]] V w.
  apply (Hsmall F); now split.
Qed.

Lemma S4Point2_logic_complete_jerabek :
  logic_complete_on (@Boxdot.S4Point2_proves nat)
    S4Point2_frame_class@{Set}.
Proof.
  intros p Hsmall. apply CanonicalPoint2.S4Point2_finite_complete.
  intros F [_ [Hrefl [Htrans Hconv]]] V w.
  apply (Hsmall F); repeat split; assumption.
Qed.

Lemma S4Point3_logic_complete_jerabek :
  logic_complete_on (@Boxdot.S4Point3_proves nat)
    S4Point3_frame_class@{Set}.
Proof.
  intros p Hsmall. apply CanonicalPoint3.S4Point3_finite_complete.
  intros F [_ [Hrefl [Htrans Hconn]]] V w.
  apply (Hsmall F); repeat split; assumption.
Qed.

Lemma S5_logic_complete_jerabek :
  logic_complete_on (@S5_proves nat) S5_frame_class@{Set}.
Proof.
  intros p Hsmall. apply S5_complete.
  intros F [Hrefl Heuclidean] V w.
  assert (Htrans : frame_transitive F).
  { now apply frame_reflexive_right_euclidean_transitive. }
  assert (Hsym : frame_symmetric F).
  { now apply frame_reflexive_right_euclidean_symmetric. }
  apply (proj1 (@finest_tc_filtration_truth_at_class
    nat F V p Htrans p (subformulas_self p) w)).
  apply (Hsmall (@finest_tc_filtered_frame nat F V p)).
  now apply finest_tc_preserves_equivalence.
Qed.

Theorem KT_BDP_unconditional : BoxdotProperty (@KT_proves nat).
Proof.
  eapply jerabek_BDP_unconditional.
  - exact KT_logic_extends_KT.
  - exact KT_logic_sound.
  - exact KT_logic_complete_jerabek.
  - exact KT_frameclass_jerabek_poly.
Qed.

Definition boxdot_conjecture_unconditional := KT_BDP_unconditional.

Theorem KTB_BDP_unconditional :
  BoxdotProperty (@Boxdot.KTB_proves nat).
Proof.
  eapply jerabek_BDP_unconditional.
  - exact KTB_logic_extends_KT.
  - exact KTB_logic_sound.
  - exact KTB_logic_complete_jerabek.
  - exact KTB_frameclass_jerabek_poly.
Qed.

Theorem S4_BDP_unconditional : BoxdotProperty (@S4_proves nat).
Proof.
  eapply jerabek_BDP_unconditional.
  - exact S4_logic_extends_KT.
  - exact S4_logic_sound.
  - exact S4_logic_complete_jerabek.
  - exact S4_frameclass_jerabek_poly.
Qed.

Theorem S4Point2_BDP_unconditional :
  BoxdotProperty (@Boxdot.S4Point2_proves nat).
Proof.
  eapply jerabek_BDP_unconditional.
  - exact S4Point2_logic_extends_KT.
  - exact S4Point2_logic_sound.
  - exact S4Point2_logic_complete_jerabek.
  - exact S4Point2_frameclass_jerabek_poly.
Qed.

Theorem S4Point3_BDP_unconditional :
  BoxdotProperty (@Boxdot.S4Point3_proves nat).
Proof.
  eapply jerabek_BDP_unconditional.
  - exact S4Point3_logic_extends_KT.
  - exact S4Point3_logic_sound.
  - exact S4Point3_logic_complete_jerabek.
  - exact S4Point3_frameclass_jerabek_poly.
Qed.

Theorem S5_BDP_unconditional : BoxdotProperty (@S5_proves nat).
Proof.
  eapply jerabek_BDP_unconditional.
  - exact S5_logic_extends_KT.
  - exact S5_logic_sound.
  - exact S5_logic_complete_jerabek.
  - exact S5_frameclass_jerabek_poly.
Qed.
