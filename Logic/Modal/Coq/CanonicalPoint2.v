(**
  Canonical and finite completeness for K4.2 and S4.2.

  This module ports the complete theorem surfaces of the pinned Foundation
  files [Modal/Kripke/Logic/K4Point2.lean] and
  [Modal/Kripke/Logic/S4Point2.lean].  K4Point2 uses Four together with the
  binary WeakPoint2 schema; S4Point2 uses T, Four, and Point2.  The latter
  schema and the S4Point2 names already occur in [Boxdot] and are reused.

  The canonical WeakPoint2 argument needs to turn extensional equality of
  maximal theories into equality of canonical worlds.  Lean validates that
  step through its built-in quotient/propositional extensionality principles;
  Coq exposes the corresponding boundary explicitly through functional and
  propositional extensionality.  No local axiom is declared.
*)

From Stdlib Require Import
  Logic.Classical_Prop Logic.ClassicalDescription
  Logic.FunctionalExtensionality Logic.PropExtensionality
  Logic.ProofIrrelevance Lists.List.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence WeakCorrespondence Root
  Filtration FiltrationExtensions NormalHilbert CanonicalK CanonicalExtensions
  CanonicalDB5 CanonicalCombinations Boxdot.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Schemata and proof systems *)

Definition schema_WeakPoint2 : modal_axiom_schema :=
  fun AtomType p =>
    exists q r : formula AtomType, p = WeakPoint2 q r.

Definition K4Point2_schema : modal_axiom_schema :=
  schema_union schema_Four schema_WeakPoint2.

Definition K4Point2_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves K4Point2_schema AtomType.

Lemma schema_WeakPoint2_substitution_closed :
  schema_substitution_closed schema_WeakPoint2.
Proof.
  intros A B sigma p [q [r ->]].
  exists (substitute sigma q), (substitute sigma r). reflexivity.
Qed.

Lemma K4Point2_schema_substitution_closed :
  schema_substitution_closed K4Point2_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_Four_substitution_closed.
  - exact schema_WeakPoint2_substitution_closed.
Qed.

Lemma schema_Point2_substitution_closed :
  schema_substitution_closed schema_Point2.
Proof.
  intros A B sigma p [q ->].
  exists (substitute sigma q). reflexivity.
Qed.

Lemma S4Point2_schema_substitution_closed :
  schema_substitution_closed S4Point2_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact schema_T_substitution_closed.
    + exact schema_Four_substitution_closed.
  - exact schema_Point2_substitution_closed.
Qed.

(** * Frame classes, soundness, and consistency *)

Definition K4Point2_frame_class (F : frame) : Prop :=
  frame_transitive F /\ frame_piecewise_convergent F.

Definition S4Point2_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ S4Point2_frame_class F.

Lemma schema_WeakPoint2_valid_on_piecewise_convergent :
  forall F,
    frame_piecewise_convergent F ->
    schema_valid_on_frame schema_WeakPoint2 F.
Proof.
  intros F HC AtomType p [q [r ->]].
  now apply valid_WeakPoint2_of_piecewise_convergent.
Qed.

Theorem K4Point2_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_transitive F -> frame_piecewise_convergent F ->
    K4Point2_proves p -> valid F p.
Proof.
  intros AtomType F p HT HC Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_Four_valid_on_transitive.
  - now apply schema_WeakPoint2_valid_on_piecewise_convergent.
Qed.

Theorem S4Point2_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F ->
    frame_piecewise_strongly_convergent F ->
    S4Point2_proves p -> valid F p.
Proof.
  intros AtomType F p HR HT HC Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply schema_Point2_valid_on_piecewise_strongly_convergent.
Qed.

Theorem K4Point2_is_consistent :
  forall AtomType, ~ @K4Point2_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := K4Point2_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_Four_valid_on_transitive.
      exact reflexive_singleton_transitive.
    + apply schema_WeakPoint2_valid_on_piecewise_convergent.
      intros [] [] [] _ _ _.
      exists tt. split; constructor.
Qed.

Theorem S4Point2_is_consistent :
  forall AtomType, ~ @S4Point2_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := S4Point2_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_T_valid_on_reflexive.
        exact reflexive_singleton_reflexive.
      * apply schema_Four_valid_on_transitive.
        exact reflexive_singleton_transitive.
    + apply schema_Point2_valid_on_piecewise_strongly_convergent.
      intros [] [] [] _ _. exists tt. split; constructor.
Qed.

(** * Small propositional proof combinators *)

Lemma normal_proves_of_valid_on_all_frames :
  forall Ax (p : formula nat),
    valid_on_all_frames p -> normal_proves Ax p.
Proof.
  intros Ax p Hvalid. apply K_proves_normal. now apply K_complete.
Qed.

Lemma normal_proves_box_and_intro :
  forall Ax (p q : formula nat),
    normal_proves Ax
      (Imp (Box p) (Imp (Box q) (Box (And p q)))).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hp Hq u Rwu.
  apply (proj2 (@satisfies_and nat F V u p q)). auto.
Qed.

Lemma normal_proves_and_intro :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p (Imp q (And p q))).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hp Hq.
  now apply (proj2 (@satisfies_and nat F V w p q)).
Qed.

Lemma normal_proves_or_neg_right :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp (Or p q) (Imp (Neg q) p)).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hor Hnq.
  destruct (proj1 (@satisfies_or nat F V w p q) Hor) as [Hp | Hq].
  - exact Hp.
  - exfalso. exact (Hnq Hq).
Qed.

Lemma normal_proves_partition_mp :
  forall Ax (a1 b1 a2 b2 p q : formula nat),
    normal_proves Ax
      (Imp (Imp a1 (Imp b1 (Imp p q)))
        (Imp (Imp a2 (Imp b2 p))
          (Imp (And a1 a2) (Imp (And b1 b2) q)))).
Proof.
  intros Ax a1 b1 a2 b2 p q.
  apply normal_proves_of_valid_on_all_frames.
  intros F V w Hpq Hp Ha Hb.
  destruct (proj1 (@satisfies_and nat F V w a1 a2) Ha) as [Ha1 Ha2].
  destruct (proj1 (@satisfies_and nat F V w b1 b2) Hb) as [Hb1 Hb2].
  exact (Hpq Ha1 Hb1 (Hp Ha2 Hb2)).
Qed.

(** * Canonical-theory support lemmas *)

Lemma normal_mct_box_top :
  forall Ax (M : normal_maximal_consistent_theory Ax),
    normal_mct_mem M (Box (@Top nat)).
Proof.
  intros Ax M. apply normal_mct_derivable_mem.
  apply ND_theorem. apply Np_nec.
  unfold Top, Neg. apply normal_proves_identity.
Qed.

Lemma normal_mct_box_and :
  forall Ax (M : normal_maximal_consistent_theory Ax) p q,
    normal_mct_mem M (Box p) ->
    normal_mct_mem M (Box q) ->
    normal_mct_mem M (Box (And p q)).
Proof.
  intros Ax M p q Hp Hq. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - eapply ND_mp.
    + apply ND_theorem. apply normal_proves_box_and_intro.
    + apply ND_assumption. exact Hp.
  - apply ND_assumption. exact Hq.
Qed.

(** Every finite derivation from the union of two unboxed canonical
    theories can be summarized by one boxed formula from each side. *)
Lemma normal_derives_two_unbox_partition :
  forall Ax (M N : normal_maximal_consistent_theory Ax) r,
    normal_derives Ax
      (fun p => normal_mct_mem M (Box p) \/ normal_mct_mem N (Box p)) r ->
    exists a b,
      normal_mct_mem M (Box a) /\
      normal_mct_mem N (Box b) /\
      normal_proves Ax (Imp a (Imp b r)).
Proof.
  intros Ax M N r Hder.
  induction Hder as
    [r [Hr | Hr] | r Hr | p q Hpq IHpq Hp IHp].
  - exists r, (@Top nat). repeat split.
    + exact Hr.
    + apply normal_mct_box_top.
    + exact (Np_imply_K r (@Top nat)).
  - exists (@Top nat), r. repeat split.
    + apply normal_mct_box_top.
    + exact Hr.
    + apply normal_proves_imply_intro. apply normal_proves_identity.
  - exists (@Top nat), (@Top nat). repeat split.
    + apply normal_mct_box_top.
    + apply normal_mct_box_top.
    + apply normal_proves_imply_intro.
      now apply normal_proves_imply_intro.
  - destruct IHpq as [a1 [b1 [Ha1 [Hb1 Himp1]]]].
    destruct IHp as [a2 [b2 [Ha2 [Hb2 Himp2]]]].
    exists (And a1 a2), (And b1 b2). repeat split.
    + now apply normal_mct_box_and.
    + now apply normal_mct_box_and.
    + eapply Np_mp.
      * eapply Np_mp.
        -- apply normal_proves_partition_mp.
        -- exact Himp1.
      * exact Himp2.
Qed.

Lemma normal_mct_extensional :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    (forall p, normal_mct_mem M p <-> normal_mct_mem N p) -> M = N.
Proof.
  intros Ax [MC HC HD] [NC IC ID] Hext. simpl in Hext.
  assert (HCarr : MC = NC).
  {
    apply functional_extensionality. intro p.
    apply propositional_extensionality. apply Hext.
  }
  subst NC. f_equal; apply proof_irrelevance.
Qed.

Lemma normal_mct_separator :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    M <> N -> exists p,
      normal_mct_mem M p /\ normal_mct_mem N (Neg p).
Proof.
  intros Ax M N Hneq.
  destruct (classic (exists p,
    normal_mct_mem M p /\ ~ normal_mct_mem N p))
    as [[p [HM HnotN]] | Hnone].
  - exists p; split; [exact HM |].
    now apply (proj2 (@normal_mct_neg_iff Ax N p)).
  - exfalso. apply Hneq. apply normal_mct_extensional. intro p; split.
    + intro HM. apply NNPP. intro HnotN.
      apply Hnone. now exists p.
    + intro HN. destruct (@normal_mct_complete Ax M p) as [HM | HnegM].
      * exact HM.
      * exfalso. apply (@normal_mct_not_both Ax N p HN).
        apply NNPP. intro HnotNegN.
        apply Hnone. exists (Neg p). split; assumption.
Qed.

Lemma normal_canonical_predecessor_dia_mem :
  forall Ax (M N : normal_maximal_consistent_theory Ax) p,
    @normal_canonical_relation Ax M N ->
    normal_mct_mem N p -> normal_mct_mem M (Dia p).
Proof.
  intros Ax M N p HMN Hp.
  change (normal_mct_mem M (Neg (Box (Neg p)))).
  apply (proj2 (@normal_mct_neg_iff Ax M (Box (Neg p)))).
  intro Hboxneg.
  exact (@normal_mct_not_both Ax N p Hp (HMN (Neg p) Hboxneg)).
Qed.

Lemma normal_canonical_successor_of_dia :
  forall Ax (M : normal_maximal_consistent_theory Ax) p,
    normal_mct_mem M (Dia p) ->
    exists N : normal_maximal_consistent_theory Ax,
      @normal_canonical_relation Ax M N /\ normal_mct_mem N p.
Proof.
  intros Ax M p Hdia.
  change (normal_mct_mem M (Neg (Box (Neg p)))) in Hdia.
  destruct (@normal_canonical_successor_of_neg_box Ax M (Neg p) Hdia)
    as [N [HMN Hnnp]].
  exists N; split; [exact HMN |].
  apply normal_mct_derivable_mem. eapply ND_mp.
  - apply ND_theorem. apply normal_proves_dne.
  - apply ND_assumption. exact Hnnp.
Qed.

(** * Canonical confluence *)

Theorem normal_canonical_strongly_confluent_of_schema_Point2 :
  forall Ax,
    schema_included schema_Point2 Ax ->
    frame_piecewise_strongly_convergent (normal_canonical_frame Ax).
Proof.
  intros Ax HPoint M N O HMN HMO.
  pose (Gamma := fun p =>
    normal_mct_mem N (Box p) \/ normal_mct_mem O (Box p)).
  assert (Hconsistent : normal_theory_consistent Ax Gamma).
  {
    intro Hbot.
    destruct (@normal_derives_two_unbox_partition Ax N O Bottom Hbot)
      as [a [b [HboxaN [HboxbO Hab]]]].
    assert (HdiaBoxaM : normal_mct_mem M (Dia (Box a))).
    {
      now apply normal_canonical_predecessor_dia_mem with (N := N).
    }
    assert (HboxdiaaM : normal_mct_mem M (Box (Dia a))).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem. apply Np_extra. apply HPoint.
        exists a. reflexivity.
      - apply ND_assumption. exact HdiaBoxaM.
    }
    pose proof (HMO (Dia a) HboxdiaaM) as HdiaaO.
    destruct (@normal_canonical_successor_of_dia Ax O a HdiaaO)
      as [P [HOP HaP]].
    pose proof (HOP b HboxbO) as HbP.
    apply (@normal_mct_consistent Ax P).
    eapply ND_mp.
    - eapply ND_mp.
      + apply ND_theorem. exact Hab.
      + apply ND_assumption. exact HaP.
    - apply ND_assumption. exact HbP.
  }
  destruct (normal_lindenbaum_extension Hconsistent) as [P Hinclude].
  exists P; split.
  - intros p Hbox. apply Hinclude. now left.
  - intros p Hbox. apply Hinclude. now right.
Qed.

Theorem normal_canonical_piecewise_convergent_of_schema_WeakPoint2 :
  forall Ax,
    schema_included schema_WeakPoint2 Ax ->
    frame_piecewise_convergent (normal_canonical_frame Ax).
Proof.
  intros Ax HWeak M N O HMN HMO Hneq.
  destruct (@normal_mct_separator Ax N O Hneq) as [d [HdN HnegdO]].
  pose (Gamma := fun p =>
    normal_mct_mem N (Box p) \/ normal_mct_mem O (Box p)).
  assert (Hconsistent : normal_theory_consistent Ax Gamma).
  {
    intro Hbot.
    destruct (@normal_derives_two_unbox_partition Ax N O Bottom Hbot)
      as [a [b [HboxaN [HboxbO Hab]]]].
    assert (HandN : normal_mct_mem N (And (Box a) d)).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - eapply ND_mp.
        + apply ND_theorem. apply normal_proves_and_intro.
        + apply ND_assumption. exact HboxaN.
      - apply ND_assumption. exact HdN.
    }
    assert (HdiaAndM : normal_mct_mem M (Dia (And (Box a) d))).
    {
      now apply normal_canonical_predecessor_dia_mem with (N := N).
    }
    assert (HboxOrM : normal_mct_mem M (Box (Or (Dia a) d))).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem. apply Np_extra. apply HWeak.
        exists a, d. reflexivity.
      - apply ND_assumption. exact HdiaAndM.
    }
    pose proof (HMO (Or (Dia a) d) HboxOrM) as HorO.
    assert (HdiaaO : normal_mct_mem O (Dia a)).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - eapply ND_mp.
        + apply ND_theorem. apply normal_proves_or_neg_right.
        + apply ND_assumption. exact HorO.
      - apply ND_assumption. exact HnegdO.
    }
    destruct (@normal_canonical_successor_of_dia Ax O a HdiaaO)
      as [P [HOP HaP]].
    pose proof (HOP b HboxbO) as HbP.
    apply (@normal_mct_consistent Ax P).
    eapply ND_mp.
    - eapply ND_mp.
      + apply ND_theorem. exact Hab.
      + apply ND_assumption. exact HaP.
    - apply ND_assumption. exact HbP.
  }
  destruct (normal_lindenbaum_extension Hconsistent) as [P Hinclude].
  exists P; split.
  - intros p Hbox. apply Hinclude. now left.
  - intros p Hbox. apply Hinclude. now right.
Qed.

Theorem normal_canonical_reflexive_of_schema_T :
  forall Ax,
    schema_included schema_T Ax ->
    frame_reflexive (normal_canonical_frame Ax).
Proof.
  intros Ax HT M p Hbox. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. apply HT.
    exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma K4Point2_canonical_frame :
  K4Point2_frame_class (normal_canonical_frame K4Point2_schema).
Proof.
  split.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. now left.
  - apply normal_canonical_piecewise_convergent_of_schema_WeakPoint2.
    intros A p Hp. now right.
Qed.

Lemma S4Point2_canonical_frame :
  S4Point2_frame_class (normal_canonical_frame S4Point2_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    intros A p Hp. left. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. left. now right.
  - apply normal_canonical_strongly_confluent_of_schema_Point2.
    intros A p Hp. now right.
Qed.

(** * Canonical completeness *)

Theorem K4Point2_complete :
  forall p : formula nat,
    normal_valid_on_class K4Point2_frame_class p -> K4Point2_proves p.
Proof.
  unfold K4Point2_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := K4Point2_schema) (C := K4Point2_frame_class)).
  - exact (@K4Point2_is_consistent nat).
  - exact K4Point2_canonical_frame.
Qed.

Theorem S4Point2_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point2_frame_class p -> S4Point2_proves p.
Proof.
  unfold S4Point2_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4Point2_schema) (C := S4Point2_frame_class)).
  - exact (@S4Point2_is_consistent nat).
  - exact S4Point2_canonical_frame.
Qed.

Theorem K4Point2_sound_complete :
  forall p : formula nat,
    K4Point2_proves p <->
    normal_valid_on_class K4Point2_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HT HC]. now apply K4Point2_proves_sound_on_frame.
  - apply K4Point2_complete.
Qed.

Theorem S4Point2_sound_complete :
  forall p : formula nat,
    S4Point2_proves p <->
    normal_valid_on_class S4Point2_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HR [HT HC]]. now apply S4Point2_proves_sound_on_frame.
  - apply S4Point2_complete.
Qed.

(** * Finite-frame completeness for S4Point2 *)

(** Root generation turns local strong confluence into global convergence.
    Global convergence is exactly what is needed to preserve local strong
    confluence through the finest transitive-closure filtration. *)
Lemma finest_tc_preserves_piecewise_strongly_convergent :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F) target,
    frame_strongly_convergent F ->
    frame_piecewise_strongly_convergent
      (@finest_tc_filtered_frame AtomType F V target).
Proof.
  intros AtomType F V target HC X Y Z _ _.
  destruct (HC (@representative AtomType F V target Y)
               (@representative AtomType F V target Z))
    as [u [Hyu Hzu]].
  exists (@profile_class AtomType F V target u); split.
  - apply positive_closure_single.
    exists (@representative AtomType F V target Y), u.
    repeat split.
    + symmetry. apply representative_spec.
    + exact Hyu.
  - apply positive_closure_single.
    exists (@representative AtomType F V target Z), u.
    repeat split.
    + symmetry. apply representative_spec.
    + exact Hzu.
Qed.

Theorem S4Point2_finite_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point2_finite_frame_class p ->
    S4Point2_proves p.
Proof.
  intros p Hfinite. apply S4Point2_complete.
  intros F [HR [HT HC]] V r.
  set (G := point_generated_frame F r).
  set (VG := point_generated_valuation V r).
  assert (HGreflexive : frame_reflexive G).
  { unfold G. now apply point_generated_reflexive. }
  assert (HGtransitive : frame_transitive G).
  { unfold G. now apply point_generated_transitive. }
  assert (HGconvergent : frame_strongly_convergent G).
  {
    unfold G.
    now apply point_generated_strongly_convergent.
  }
  pose (Q := @finest_tc_filtered_frame nat G VG p).
  pose (VQ := @finest_tc_filtered_valuation nat G VG p).
  assert (HQfinite : finite_frame Q).
  { unfold Q. apply finest_tc_filtered_frame_finite. }
  assert (HQreflexive : frame_reflexive Q).
  { unfold Q. now apply finest_tc_preserves_reflexive. }
  assert (HQtransitive : frame_transitive Q).
  { unfold Q. apply finest_tc_is_transitive. }
  assert (HQconvergent : frame_piecewise_strongly_convergent Q).
  {
    unfold Q.
    now apply finest_tc_preserves_piecewise_strongly_convergent.
  }
  assert (HsatQ : satisfies Q VQ
    (@profile_class nat G VG p (point_generated_root F r)) p).
  {
    apply (Hfinite Q). repeat split; assumption.
  }
  apply (proj1 (@point_generated_truth_at_root nat F V r HT p)).
  apply (proj1 (@finest_tc_filtration_truth_at_class
    nat G VG p HGtransitive p (subformulas_self p)
    (point_generated_root F r))).
  exact HsatQ.
Qed.

Theorem S4Point2_finite_sound :
  forall p : formula nat,
    S4Point2_proves p ->
    normal_valid_on_class S4Point2_finite_frame_class p.
Proof.
  intros p Hp F [_ [HR [HT HC]]].
  now apply S4Point2_proves_sound_on_frame.
Qed.

Theorem S4Point2_finite_sound_complete :
  forall p : formula nat,
    S4Point2_proves p <->
    normal_valid_on_class S4Point2_finite_frame_class p.
Proof.
  intro p; split.
  - apply S4Point2_finite_sound.
  - apply S4Point2_finite_complete.
Qed.

(** * Frame-class and logic inclusions *)

Lemma S4Point2_frame_is_preorder :
  forall F, S4Point2_frame_class F -> frame_preorder_class F.
Proof. intros F [HR [HT _]]. now split. Qed.

Lemma S4Point2_frame_is_K4Point2 :
  forall F, S4Point2_frame_class F -> K4Point2_frame_class F.
Proof.
  intros F [_ [HT HC]]. split; [exact HT |].
  now apply piecewise_strongly_convergent_convergent.
Qed.

Lemma K4_weaker_than_K4Point2 :
  forall (AtomType : Type) (p : formula AtomType),
    K4_proves p -> K4Point2_proves p.
Proof.
  intros AtomType p Hp. unfold K4_proves, K4Point2_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma S4_weaker_than_S4Point2 :
  forall (AtomType : Type) (p : formula AtomType),
    S4_proves p -> S4Point2_proves p.
Proof.
  intros AtomType p Hp. unfold S4_proves, S4Point2_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma KT_weaker_than_S4Point2 :
  forall (AtomType : Type) (p : formula AtomType),
    KT_proves p -> S4Point2_proves p.
Proof.
  intros AtomType p Hp. apply S4_weaker_than_S4Point2.
  now apply KT_weaker_than_S4.
Qed.

Lemma K4Point2_weaker_than_S4Point2 :
  forall p : formula nat, K4Point2_proves p -> S4Point2_proves p.
Proof.
  intros p Hp. apply S4Point2_complete.
  intros F HF.
  destruct (S4Point2_frame_is_K4Point2 HF) as [HT HC].
  now apply K4Point2_proves_sound_on_frame.
Qed.

(** * Separating frames *)

Lemma two_fan_frame_transitive : frame_transitive two_fan_frame.
Proof. intros x y z Hx _. exact Hx. Qed.

Lemma two_fan_frame_not_piecewise_convergent :
  ~ frame_piecewise_convergent two_fan_frame.
Proof.
  intro HC.
  assert (Hneq : DB0 <> DB1) by discriminate.
  destruct (HC DB0 DB0 DB1 eq_refl eq_refl Hneq)
    as [u [_ Hbad]].
  discriminate.
Qed.

Definition point2_fork_frame : frame :=
  {| World := three_world;
     Rel := fun x y => x = W0 \/ x = y |}.

Lemma point2_fork_reflexive : frame_reflexive point2_fork_frame.
Proof. intro x. now right. Qed.

Lemma point2_fork_transitive : frame_transitive point2_fork_frame.
Proof.
  intros x y z [Hx | Hxy] Hyz.
  - now left.
  - subst y. exact Hyz.
Qed.

Lemma point2_fork_not_piecewise_strongly_convergent :
  ~ frame_piecewise_strongly_convergent point2_fork_frame.
Proof.
  intro HC.
  destruct (HC W0 W1 W2 (or_introl eq_refl) (or_introl eq_refl))
    as [u [H1u H2u]].
  destruct H1u as [Hbad | H1u]; [discriminate |].
  destruct H2u as [Hbad | H2u]; [discriminate |].
  subst u. discriminate.
Qed.

Lemma one_way_frame_transitive : frame_transitive one_way_frame.
Proof.
  intros x y z [_ Hy] [Hy0 _]. subst y. discriminate.
Qed.

Lemma one_way_frame_piecewise_convergent :
  frame_piecewise_convergent one_way_frame.
Proof.
  intros x y z [_ Hy] [_ Hz] Hneq.
  exfalso. apply Hneq. congruence.
Qed.

Lemma one_way_frame_not_piecewise_strongly_convergent :
  ~ frame_piecewise_strongly_convergent one_way_frame.
Proof.
  intro HC.
  destruct (HC DB0 DB1 DB1 (conj eq_refl eq_refl)
    (conj eq_refl eq_refl)) as [u [[Hbad _] _]].
  discriminate.
Qed.

(** * Strict inclusions *)

Theorem K4_strictly_weaker_K4Point2 :
  normal_strictly_weaker K4_proves K4Point2_proves.
Proof.
  split.
  - apply K4_weaker_than_K4Point2.
  - exists (WeakPoint2 (Atom 0) (Atom 1)); split.
    + apply Np_extra. right. exists (Atom 0), (Atom 1). reflexivity.
    + intro HK4.
      pose proof (K4_proves_sound_on_transitive_frame
        two_fan_frame_transitive HK4) as Hvalid.
      apply two_fan_frame_not_piecewise_convergent.
      now apply (proj1 (valid_WeakPoint2_atoms_iff_piecewise_convergent
        two_fan_frame)).
Qed.

Theorem S4_strictly_weaker_S4Point2 :
  normal_strictly_weaker S4_proves S4Point2_proves.
Proof.
  split.
  - apply S4_weaker_than_S4Point2.
  - exists (Point2 (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HS4.
      pose proof (S4_proves_sound_on_preorder_frame
        point2_fork_reflexive point2_fork_transitive HS4) as Hvalid.
      apply point2_fork_not_piecewise_strongly_convergent.
      now apply (proj1 (valid_Point2_iff_strong_confluence point2_fork_frame)).
Qed.

Theorem K4Point2_strictly_weaker_S4Point2 :
  normal_strictly_weaker K4Point2_proves S4Point2_proves.
Proof.
  split.
  - apply K4Point2_weaker_than_S4Point2.
  - exists (Point2 (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HK4Point2.
      pose proof (K4Point2_proves_sound_on_frame one_way_frame_transitive
        one_way_frame_piecewise_convergent HK4Point2) as Hvalid.
      apply one_way_frame_not_piecewise_strongly_convergent.
      now apply (proj1 (valid_Point2_iff_strong_confluence one_way_frame)).
Qed.

Theorem KT_strictly_weaker_S4Point2 :
  normal_strictly_weaker KT_proves S4Point2_proves.
Proof.
  destruct KT_strictly_weaker_S4 as [HKT [p [HS4 HnotKT]]].
  split.
  - apply KT_weaker_than_S4Point2.
  - exists p; split.
    + now apply S4_weaker_than_S4Point2.
    + exact HnotKT.
Qed.
