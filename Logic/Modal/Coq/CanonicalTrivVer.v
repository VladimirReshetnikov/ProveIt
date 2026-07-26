(**
  Canonical completeness for KTc, Triv, and Ver.

  This module ports the mathematical surface of the pinned Foundation files

    - [Modal/Kripke/Logic/KTc.lean],
    - [Modal/Kripke/Logic/Triv.lean],
    - [Modal/Kripke/Logic/Ver.lean], and
    - their three source-local entailment modules.

  [Boxdot] already gives the repository's definitions of the Tc, Triv, Ver,
  GL.3, and Grz.3 schemata.  They are reused here.  Only the S4.Point4.McK
  combination, which is needed by Triv's strict-inclusion theorem, is added.
  Finite completeness follows the upstream point-generated idea in its
  simplest form: at a chosen world, an equality or isolated frame is modally
  equivalent to the corresponding one-world frame.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  HilbertKSoundness NormalHilbert CanonicalExtensions Filtration
  CanonicalCombinations FrameProperties Loeb Root FrameTransformations
  WeakCorrespondence Boxdot.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The additional schemata *)

Definition KTc_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves schema_Tc AtomType.

Definition schema_DiaT : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = DiaT q.

Definition KTc_prime_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves schema_DiaT AtomType.

Definition schema_Point4 : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Point4 q.

Definition schema_McK : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = McK q.

Definition S4Point4McK_schema : modal_axiom_schema :=
  schema_union
    (schema_union (schema_union schema_T schema_Four) schema_McK)
    schema_Point4.

Definition S4Point4McK_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4Point4McK_schema AtomType.

Lemma schema_Tc_substitution_closed :
  schema_substitution_closed schema_Tc.
Proof.
  intros A B sigma p [q ->]. exists (substitute sigma q). reflexivity.
Qed.

Lemma schema_DiaT_substitution_closed :
  schema_substitution_closed schema_DiaT.
Proof.
  intros A B sigma p [q ->]. exists (substitute sigma q). reflexivity.
Qed.

Lemma schema_Ver_substitution_closed :
  schema_substitution_closed schema_Ver.
Proof.
  intros A B sigma p [q ->]. exists (substitute sigma q). reflexivity.
Qed.

Lemma Triv_schema_substitution_closed :
  schema_substitution_closed Triv_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_T_substitution_closed.
  - exact schema_Tc_substitution_closed.
Qed.

Lemma schema_Point4_substitution_closed :
  schema_substitution_closed schema_Point4.
Proof.
  intros A B sigma p [q ->]. exists (substitute sigma q). reflexivity.
Qed.

Lemma schema_McK_substitution_closed :
  schema_substitution_closed schema_McK.
Proof.
  intros A B sigma p [q ->]. exists (substitute sigma q). reflexivity.
Qed.

Lemma S4Point4McK_schema_substitution_closed :
  schema_substitution_closed S4Point4McK_schema.
Proof.
  repeat apply schema_union_substitution_closed.
  - exact schema_T_substitution_closed.
  - exact schema_Four_substitution_closed.
  - exact schema_McK_substitution_closed.
  - exact schema_Point4_substitution_closed.
Qed.

(** * Frame classes and relational bridges *)

Definition KTc_kripke_frame_class (F : frame) : Prop :=
  frame_coreflexive F.

Definition Triv_kripke_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_coreflexive F.

Definition finite_Triv_kripke_frame_class (F : frame) : Prop :=
  finite_frame F /\ Triv_kripke_frame_class F.

Definition Ver_kripke_frame_class (F : frame) : Prop :=
  frame_isolated F.

Definition finite_Ver_kripke_frame_class (F : frame) : Prop :=
  finite_frame F /\ Ver_kripke_frame_class F.

Definition S4Point4McK_kripke_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\
  frame_sobocinski F /\ frame_mckinsey F.

Lemma Triv_frame_relation_iff_equality :
  forall F,
    Triv_kripke_frame_class F ->
    forall x y : World F, Rel F x y <-> x = y.
Proof.
  intros F [Hrefl Hcore] x y; split.
  - apply Hcore.
  - intros ->. apply Hrefl.
Qed.

Lemma Ver_frame_relation_false :
  forall F,
    Ver_kripke_frame_class F ->
    forall x y : World F, ~ Rel F x y.
Proof. intros F H x y; apply H. Qed.

Lemma Triv_frame_transitive :
  forall F, Triv_kripke_frame_class F -> frame_transitive F.
Proof.
  intros F [_ Hcore] x y z Hxy Hyz.
  apply Hcore in Hxy. now subst y.
Qed.

Lemma Triv_frame_weak_cwf :
  forall F,
    Triv_kripke_frame_class F -> frame_weak_converse_well_founded F.
Proof.
  intros F [_ Hcore] X [x Hx].
  exists x; split; [exact Hx |].
  intros y _ Rxy. now apply Hcore.
Qed.

Lemma Triv_frame_piecewise_strongly_connected :
  forall F,
    Triv_kripke_frame_class F -> frame_piecewise_strongly_connected F.
Proof.
  intros F [Hrefl Hcore] x y z Hxy Hxz.
  apply Hcore in Hxy; apply Hcore in Hxz. subst y; subst z.
  left. apply Hrefl.
Qed.

Lemma Triv_frame_sobocinski :
  forall F, Triv_kripke_frame_class F -> frame_sobocinski F.
Proof.
  intros F [_ Hcore] x y z Hneq Rxy _.
  exfalso. apply Hneq. now apply Hcore.
Qed.

Lemma Triv_frame_mckinsey :
  forall F, Triv_kripke_frame_class F -> frame_mckinsey F.
Proof.
  intros F [Hrefl Hcore] x. exists x; split.
  - apply Hrefl.
  - intros z Rxz. now apply Hcore.
Qed.

Lemma Triv_frame_is_S4Point4McK :
  forall F,
    Triv_kripke_frame_class F -> S4Point4McK_kripke_frame_class F.
Proof.
  intros F Htriv. repeat split.
  - exact (proj1 Htriv).
  - now apply Triv_frame_transitive.
  - now apply Triv_frame_sobocinski.
  - now apply Triv_frame_mckinsey.
Qed.

Lemma finite_Triv_frame_is_GrzPoint3 :
  forall F,
    finite_Triv_kripke_frame_class F ->
    boxdot_finite_GrzPoint3_frame F.
Proof.
  intros F [Hfinite Htriv]. unfold boxdot_finite_GrzPoint3_frame,
    boxdot_finite_Grz_frame. repeat split.
  - exact Hfinite.
  - exact (proj1 Htriv).
  - now apply Triv_frame_transitive.
  - now apply Triv_frame_weak_cwf.
  - now apply Triv_frame_piecewise_strongly_connected.
Qed.

Lemma isolated_frame_transitive :
  forall F, frame_isolated F -> frame_transitive F.
Proof.
  intros F Hiso x y z Hxy. exfalso. exact (Hiso x y Hxy).
Qed.

Lemma isolated_frame_cwf :
  forall F, frame_isolated F -> frame_converse_well_founded F.
Proof.
  intros F Hiso X [x Hx]. exists x; split; [exact Hx |].
  intros y _ Rxy. exact (Hiso x y Rxy).
Qed.

Lemma isolated_frame_piecewise_connected :
  forall F, frame_isolated F -> frame_piecewise_connected F.
Proof.
  intros F Hiso x y z Hxy. exfalso. exact (Hiso x y Hxy).
Qed.

Lemma finite_Ver_frame_is_GLPoint3 :
  forall F,
    finite_Ver_kripke_frame_class F ->
    boxdot_finite_GLPoint3_frame F.
Proof.
  intros F [Hfinite Hiso]. unfold boxdot_finite_GLPoint3_frame,
    boxdot_finite_GL_frame. repeat split.
  - exact Hfinite.
  - now apply isolated_frame_transitive.
  - now apply isolated_frame_cwf.
  - now apply isolated_frame_piecewise_connected.
Qed.

(** * Soundness and consistency *)

Lemma schema_Tc_valid_on_coreflexive :
  forall F,
    frame_coreflexive F -> schema_valid_on_frame schema_Tc F.
Proof.
  intros F Hcore AtomType p [q ->].
  now apply valid_Tc_of_coreflexive.
Qed.

Lemma schema_Ver_valid_on_isolated :
  forall F,
    frame_isolated F -> schema_valid_on_frame schema_Ver F.
Proof.
  intros F Hiso AtomType p [q ->]. now apply valid_Ver_of_isolated.
Qed.

Lemma schema_Point4_valid_on_sobocinski :
  forall F,
    frame_sobocinski F -> schema_valid_on_frame schema_Point4 F.
Proof.
  intros F Hsob AtomType p [q ->]. now apply valid_Point4_of_sobocinski.
Qed.

Lemma schema_McK_valid_on_mckinsey :
  forall F,
    frame_mckinsey F -> schema_valid_on_frame schema_McK F.
Proof.
  intros F Hmck AtomType p [q ->]. now apply valid_McK_of_mckinsey.
Qed.

Theorem KTc_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    KTc_kripke_frame_class F -> KTc_proves p -> valid F p.
Proof.
  intros AtomType F p Hcore Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  now apply schema_Tc_valid_on_coreflexive.
Qed.

Theorem Triv_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    Triv_kripke_frame_class F -> Triv_proves p -> valid F p.
Proof.
  intros AtomType F p [Hrefl Hcore] Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_T_valid_on_reflexive.
  - now apply schema_Tc_valid_on_coreflexive.
Qed.

Theorem Triv_proves_sound_on_finite_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    finite_Triv_kripke_frame_class F -> Triv_proves p -> valid F p.
Proof.
  intros AtomType F p [_ Htriv]. now apply Triv_proves_sound_on_frame.
Qed.

Theorem Ver_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    Ver_kripke_frame_class F -> Ver_proves p -> valid F p.
Proof.
  intros AtomType F p Hiso Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  now apply schema_Ver_valid_on_isolated.
Qed.

Theorem Ver_proves_sound_on_finite_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    finite_Ver_kripke_frame_class F -> Ver_proves p -> valid F p.
Proof.
  intros AtomType F p [_ Hiso]. now apply Ver_proves_sound_on_frame.
Qed.

Theorem S4Point4McK_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    S4Point4McK_kripke_frame_class F ->
    S4Point4McK_proves p -> valid F p.
Proof.
  intros AtomType F p [Hrefl [Htrans [Hsob Hmck]]] Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  unfold S4Point4McK_schema.
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * now apply schema_T_valid_on_reflexive.
      * now apply schema_Four_valid_on_transitive.
    + now apply schema_McK_valid_on_mckinsey.
  - now apply schema_Point4_valid_on_sobocinski.
Qed.

Theorem GLPoint3_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_transitive F -> frame_converse_well_founded F ->
    frame_piecewise_connected F ->
    GLPoint3_proves p -> valid F p.
Proof.
  intros AtomType F p Htrans Hcwf Hpiece Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_L_valid_on_GL_frame.
  - now apply schema_WeakPoint3_valid_on_piecewise_connected.
Qed.

Theorem GrzPoint3_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F ->
    frame_weak_converse_well_founded F ->
    frame_piecewise_strongly_connected F ->
    GrzPoint3_proves p -> valid F p.
Proof.
  intros AtomType F p Hrefl Htrans Hweak Hpiece Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_Grz_valid_on_Grz_frame.
  - now apply schema_Point3_valid_on_piecewise_strongly_connected.
Qed.

Lemma reflexive_singleton_coreflexive :
  frame_coreflexive reflexive_singleton_frame.
Proof. intros [] [] _. reflexivity. Qed.

Lemma irreflexive_singleton_isolated :
  frame_isolated irreflexive_singleton_frame.
Proof. intros [] [] H. exact H. Qed.

Theorem Triv_is_consistent :
  forall AtomType, ~ @Triv_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := Triv_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_T_valid_on_reflexive.
      exact reflexive_singleton_reflexive.
    + apply schema_Tc_valid_on_coreflexive.
      exact reflexive_singleton_coreflexive.
Qed.

Theorem Ver_is_consistent :
  forall AtomType, ~ @Ver_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := schema_Ver) (F := irreflexive_singleton_frame)).
  - now exists tt.
  - apply schema_Ver_valid_on_isolated.
    exact irreflexive_singleton_isolated.
Qed.

Theorem KTc_is_consistent :
  forall AtomType, ~ @KTc_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := schema_Tc) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_Tc_valid_on_coreflexive.
    exact reflexive_singleton_coreflexive.
Qed.

(** * Canonicality and unrestricted completeness *)

(** Inclusion between maximal consistent theories is equality.  Coq's
    record presentation makes the extensional principles used here explicit;
    the corresponding identification is implicit in Foundation's set-based
    canonical worlds. *)
Lemma normal_mct_eq_of_included :
  forall Ax (M N : normal_maximal_consistent_theory Ax),
    (forall p, normal_mct_mem M p -> normal_mct_mem N p) -> M = N.
Proof.
  intros Ax M N Hinclude.
  assert (Hmem : forall p,
      normal_mct_mem M p <-> normal_mct_mem N p).
  {
    intro p; split; [apply Hinclude |].
    intro HNp.
    destruct (@normal_mct_complete Ax M p) as [HMp | HMneg].
    - exact HMp.
    - exfalso. exact (@normal_mct_not_both Ax N p HNp
        (Hinclude (Neg p) HMneg)).
  }
  destruct M as [MC Mconsistent Mcomplete].
  destruct N as [NC Nconsistent Ncomplete].
  simpl in Hmem.
  assert (Hcarrier : MC = NC).
  {
    apply functional_extensionality; intro p.
    apply propositional_extensionality. apply Hmem.
  }
  subst NC.
  assert (Hconsistent : Mconsistent = Nconsistent) by apply proof_irrelevance.
  subst Nconsistent.
  assert (Hcomplete : Mcomplete = Ncomplete) by apply proof_irrelevance.
  now subst Ncomplete.
Qed.

Lemma KTc_canonical_frame_coreflexive :
  frame_coreflexive (normal_canonical_frame schema_Tc).
Proof.
  intros M N HMN. apply normal_mct_eq_of_included.
  intros p Hp. apply HMN with (p := p).
  apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. exists p. reflexivity.
  - apply ND_assumption. exact Hp.
Qed.

Theorem KTc_canonical :
  KTc_kripke_frame_class (normal_canonical_frame schema_Tc).
Proof. exact KTc_canonical_frame_coreflexive. Qed.

Lemma Triv_canonical_frame_reflexive :
  frame_reflexive (normal_canonical_frame Triv_schema).
Proof.
  intros M p Hbox. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. left. exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma Triv_canonical_frame_coreflexive :
  frame_coreflexive (normal_canonical_frame Triv_schema).
Proof.
  intros M N HMN. apply normal_mct_eq_of_included.
  intros p Hp. apply HMN with (p := p).
  apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. right. exists p. reflexivity.
  - apply ND_assumption. exact Hp.
Qed.

Theorem Triv_canonical :
  Triv_kripke_frame_class (normal_canonical_frame Triv_schema).
Proof.
  split.
  - exact Triv_canonical_frame_reflexive.
  - exact Triv_canonical_frame_coreflexive.
Qed.

Lemma Ver_canonical_frame_isolated :
  frame_isolated (normal_canonical_frame schema_Ver).
Proof.
  intros M N HMN.
  apply (@normal_mct_bottom_absent schema_Ver N).
  apply HMN with (p := Bottom).
  apply normal_mct_derivable_mem.
  apply ND_theorem. apply Np_extra. exists Bottom. reflexivity.
Qed.

Theorem Ver_canonical :
  Ver_kripke_frame_class (normal_canonical_frame schema_Ver).
Proof. exact Ver_canonical_frame_isolated. Qed.

Theorem KTc_complete :
  forall p : formula nat,
    normal_valid_on_class KTc_kripke_frame_class p -> KTc_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_Tc) (C := KTc_kripke_frame_class)).
  - exact (@KTc_is_consistent nat).
  - exact KTc_canonical.
Qed.

Theorem Triv_complete :
  forall p : formula nat,
    normal_valid_on_class Triv_kripke_frame_class p -> Triv_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := Triv_schema) (C := Triv_kripke_frame_class)).
  - exact (@Triv_is_consistent nat).
  - exact Triv_canonical.
Qed.

Theorem Ver_complete :
  forall p : formula nat,
    normal_valid_on_class Ver_kripke_frame_class p -> Ver_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_Ver) (C := Ver_kripke_frame_class)).
  - exact (@Ver_is_consistent nat).
  - exact Ver_canonical.
Qed.

Theorem KTc_sound_complete :
  forall p : formula nat,
    KTc_proves p <-> normal_valid_on_class KTc_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F Hcore. now apply KTc_proves_sound_on_frame.
  - apply KTc_complete.
Qed.

Theorem Triv_sound_complete :
  forall p : formula nat,
    Triv_proves p <-> normal_valid_on_class Triv_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F Htriv. now apply Triv_proves_sound_on_frame.
  - apply Triv_complete.
Qed.

Theorem Ver_sound_complete :
  forall p : formula nat,
    Ver_proves p <-> normal_valid_on_class Ver_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F Hiso. now apply Ver_proves_sound_on_frame.
  - apply Ver_complete.
Qed.

(** This is the dependency that [Boxdot] deliberately left explicit before
    the Triv canonical model was available. *)
Theorem boxdot_Triv_complete_checked : boxdot_Triv_complete.
Proof. exact Triv_complete. Qed.

Theorem Ver_boxdot_proves_to_Triv_unconditional :
  forall p : formula nat,
    Ver_proves (boxdot_translate p) -> Triv_proves p.
Proof.
  exact (Ver_boxdot_proves_to_Triv boxdot_Triv_complete_checked).
Qed.

Theorem Ver_boxdot_iff_Triv_unconditional :
  forall p : formula nat,
    Ver_proves (boxdot_translate p) <-> Triv_proves p.
Proof.
  exact (Ver_boxdot_iff_Triv boxdot_Triv_complete_checked).
Qed.

Definition iff_boxdotTranslated_Ver_Triv'_unconditional :=
  Ver_boxdot_iff_Triv_unconditional.
Definition iff_boxdotTranslated_Ver_Triv_unconditional :=
  Ver_boxdot_iff_Triv_unconditional.

(** * One-world reductions and finite completeness *)

Lemma reflexive_singleton_finite :
  finite_frame reflexive_singleton_frame.
Proof. exists [tt]. intros []; now left. Qed.

Lemma irreflexive_singleton_finite :
  finite_frame irreflexive_singleton_frame.
Proof. exists [tt]. intros []; now left. Qed.

Lemma Triv_truth_at_world_iff_reflexive_singleton :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (w : World F) (p : formula AtomType),
    Triv_kripke_frame_class F ->
    satisfies F V w p <->
    satisfies reflexive_singleton_frame (fun a _ => V a w) tt p.
Proof.
  intros AtomType F V w p [Hrefl Hcore].
  induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - reflexivity.
  - tauto.
  - rewrite IHp, IHq. reflexivity.
  - split.
    + intros Hbox [] _. apply (proj1 IHp). apply Hbox. apply Hrefl.
    + intros Hbox y Rwy. apply Hcore in Rwy. subst y.
      apply (proj2 IHp). apply Hbox with (u := tt). constructor.
Qed.

Lemma Ver_truth_at_world_iff_irreflexive_singleton :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (w : World F) (p : formula AtomType),
    Ver_kripke_frame_class F ->
    satisfies F V w p <->
    satisfies irreflexive_singleton_frame (fun a _ => V a w) tt p.
Proof.
  intros AtomType F V w p Hiso.
  induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - reflexivity.
  - tauto.
  - rewrite IHp, IHq. reflexivity.
  - split.
    + intros _ [] Hfalse. contradiction.
    + intros _ y Rwy. exfalso. exact (Hiso w y Rwy).
Qed.

Theorem Triv_finite_complete :
  forall p : formula nat,
    normal_valid_on_class finite_Triv_kripke_frame_class p ->
    Triv_proves p.
Proof.
  intros p Hfinite. apply Triv_complete.
  intros F Htriv V w.
  apply (proj2 (Triv_truth_at_world_iff_reflexive_singleton
    V w p Htriv)).
  apply (Hfinite reflexive_singleton_frame).
  - split.
    + exact reflexive_singleton_finite.
    + split.
      * exact reflexive_singleton_reflexive.
      * exact reflexive_singleton_coreflexive.
Qed.

Theorem Ver_finite_complete :
  forall p : formula nat,
    normal_valid_on_class finite_Ver_kripke_frame_class p ->
    Ver_proves p.
Proof.
  intros p Hfinite. apply Ver_complete.
  intros F Hiso V w.
  apply (proj2 (Ver_truth_at_world_iff_irreflexive_singleton
    V w p Hiso)).
  apply (Hfinite irreflexive_singleton_frame).
  - split.
    + exact irreflexive_singleton_finite.
    + exact irreflexive_singleton_isolated.
Qed.

Theorem Triv_finite_sound_complete :
  forall p : formula nat,
    Triv_proves p <->
    normal_valid_on_class finite_Triv_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply Triv_proves_sound_on_finite_frame.
  - apply Triv_finite_complete.
Qed.

Theorem Ver_finite_sound_complete :
  forall p : formula nat,
    Ver_proves p <->
    normal_valid_on_class finite_Ver_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply Ver_proves_sound_on_finite_frame.
  - apply Ver_finite_complete.
Qed.

(** * Entailment consequences imported by the source logic modules *)

Lemma normal_proves_imp_trans_poly :
  forall Ax (AtomType : Type) (p q r : formula AtomType),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp q r) ->
    normal_proves Ax (Imp p r).
Proof.
  intros Ax AtomType p q r Hpq Hqr.
  eapply Np_mp.
  - eapply Np_mp.
    + apply Np_imply_S.
    + eapply Np_mp; [apply Np_imply_K | exact Hqr].
  - exact Hpq.
Qed.

Lemma normal_proves_reaxiomatize :
  forall Ax Ay,
    (forall (AtomType : Type) (p : formula AtomType),
      Ax AtomType p -> @normal_proves Ay AtomType p) ->
    forall (AtomType : Type) (p : formula AtomType),
      @normal_proves Ax AtomType p -> @normal_proves Ay AtomType p.
Proof.
  intros Ax Ay Haxioms AtomType p Hp. induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - now apply Haxioms.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

(** The complete theorem surface of [Modal/Entailment/KTc.lean].  The first
    two consequences are literally Tc at [box p] and [diamond p].  The two
    directions between Tc and DiaT use only the calculus's classical
    contraposition axiom and its derived double-negation rules. *)
Theorem KTc_proves_Four :
  forall (AtomType : Type) (p : formula AtomType),
    KTc_proves (Four p).
Proof.
  intros AtomType p. unfold Four.
  apply Np_extra. exists (Box p). reflexivity.
Qed.

Theorem KTc_proves_Five :
  forall (AtomType : Type) (p : formula AtomType),
    KTc_proves (Five p).
Proof.
  intros AtomType p. unfold Five.
  apply Np_extra. exists (Dia p). reflexivity.
Qed.

Theorem KTc_proves_DiaT :
  forall (AtomType : Type) (p : formula AtomType),
    KTc_proves (DiaT p).
Proof.
  intros AtomType p.
  assert (Htc : KTc_proves (Tc (Neg p))).
  { apply Np_extra. exists (Neg p). reflexivity. }
  assert (Hdni : KTc_proves
    (Imp (Box (Neg p)) (Neg (Neg (Box (Neg p)))))).
  { apply K_proves_normal. apply K_proves_dni. }
  assert (Hprem : KTc_proves
    (Imp (Neg p) (Neg (Neg (Box (Neg p)))))).
  { eapply normal_proves_imp_trans_poly;
      [exact Htc | exact Hdni]. }
  eapply Np_mp.
  - exact (Np_elim_contra (Dia p) p).
  - exact Hprem.
Qed.

Theorem KTc_prime_proves_Tc :
  forall (AtomType : Type) (p : formula AtomType),
    KTc_prime_proves (Tc p).
Proof.
  intros AtomType p.
  assert (HdiaT : KTc_prime_proves (DiaT (Neg p))).
  { apply Np_extra. exists (Neg p). reflexivity. }
  assert (Hfirst : KTc_prime_proves
    (Imp p (Box (Neg (Neg p))))).
  { eapply Np_mp.
    - exact (Np_elim_contra p (Box (Neg (Neg p)))).
    - exact HdiaT. }
  assert (Hbox_dne : KTc_prime_proves
    (Imp (Box (Neg (Neg p))) (Box p))).
  { apply K_proves_normal.
    apply K_proves_box_regularity.
    apply K_proves_dne. }
  eapply normal_proves_imp_trans_poly;
    [exact Hfirst | exact Hbox_dne].
Qed.

Theorem Triv_proves_Grz :
  forall (AtomType : Type) (p : formula AtomType),
    Triv_proves (Grz p).
Proof.
  intros AtomType p. unfold Grz.
  pose (a := Box (Imp p (Box p))).
  assert (Htc : Triv_proves (Imp p (Box p))).
  { apply Np_extra. right. exists p. reflexivity. }
  assert (Ha : Triv_proves a).
  { unfold a. now apply Np_nec. }
  assert (Htaut : K_proves (Imp a (Imp (Imp a p) p))).
  {
    apply (proj1 (K_derives_empty_iff
      (Imp a (Imp (Imp a p) p)))).
    apply K_derives_deduction.
    apply K_derives_deduction.
    eapply Kd_mp.
    - apply Kd_assumption. now left.
    - apply Kd_assumption. right. now left.
  }
  assert (Htail : Triv_proves (Imp (Imp a p) p)).
  { eapply Np_mp; [apply K_proves_normal; exact Htaut | exact Ha]. }
  eapply normal_proves_imp_trans_poly; [|exact Htail].
  apply Np_extra. left. exists (Imp a p). reflexivity.
Qed.

Theorem Ver_proves_bot_of_dia :
  forall (AtomType : Type) (p : formula AtomType),
    Ver_proves (Imp (Dia p) Bottom).
Proof.
  intros AtomType p. unfold Dia, Neg.
  eapply Np_mp.
  - apply K_proves_normal. apply K_proves_dni.
  - apply Np_extra. exists (Imp p Bottom). reflexivity.
Qed.

Theorem Ver_proves_bot_of_dia' :
  forall (AtomType : Type) (p : formula AtomType),
    Ver_proves (Dia p) -> Ver_proves (@Bottom AtomType).
Proof.
  intros AtomType p Hdia.
  eapply Np_mp; [apply Ver_proves_bot_of_dia | exact Hdia].
Qed.

Theorem Ver_proves_Tc :
  forall (AtomType : Type) (p : formula AtomType),
    Ver_proves (Tc p).
Proof.
  intros AtomType p. unfold Tc.
  eapply Np_mp.
  - apply Np_imply_K.
  - apply Np_extra. exists p. reflexivity.
Qed.

Theorem Ver_proves_L :
  forall (AtomType : Type) (p : formula AtomType),
    Ver_proves (L p).
Proof.
  intros AtomType p. unfold L, Loeb.
  eapply Np_mp.
  - apply Np_imply_K.
  - apply Np_extra. exists p. reflexivity.
Qed.

(** * Logical inclusions *)

Lemma isolated_frame_coreflexive :
  forall F, frame_isolated F -> frame_coreflexive F.
Proof.
  intros F Hiso x y Rxy. exfalso. exact (Hiso x y Rxy).
Qed.

Lemma coreflexive_frame_symmetric :
  forall F, frame_coreflexive F -> frame_symmetric F.
Proof.
  intros F Hcore x y Rxy. pose proof Rxy as Ryx.
  apply Hcore in Rxy. now subst y.
Qed.

Lemma coreflexive_frame_transitive :
  forall F, frame_coreflexive F -> frame_transitive F.
Proof.
  intros F Hcore x y z Rxy Ryz.
  apply Hcore in Rxy. now subst y.
Qed.

Lemma KTc_frame_is_KB4 :
  forall F,
    KTc_kripke_frame_class F -> KB4_frame_class F.
Proof.
  intros F Hcore; split.
  - now apply coreflexive_frame_symmetric.
  - now apply coreflexive_frame_transitive.
Qed.

Theorem KB4_weaker_than_KTc :
  forall p : formula nat, KB4_proves p -> KTc_proves p.
Proof.
  intros p Hp. apply KTc_complete.
  intros F Hcore.
  apply KB4_proves_sound_on_frame.
  - now apply coreflexive_frame_symmetric.
  - now apply coreflexive_frame_transitive.
  - exact Hp.
Qed.

Theorem KTc_weaker_than_Triv :
  forall (AtomType : Type) (p : formula AtomType),
    KTc_proves p -> Triv_proves p.
Proof.
  intros AtomType p. apply normal_proves_weaken.
  intros A q Hq. now right.
Qed.

Theorem KTc_weaker_than_Ver :
  forall (AtomType : Type) (p : formula AtomType),
    KTc_proves p -> Ver_proves p.
Proof.
  intros AtomType p.
  apply normal_proves_reaxiomatize.
  intros A q [r ->]. apply Ver_proves_Tc.
Qed.

Theorem GrzPoint3_weaker_than_Triv :
  forall p : formula nat, GrzPoint3_proves p -> Triv_proves p.
Proof.
  intros p Hp. apply Triv_complete.
  intros F Htriv.
  apply GrzPoint3_proves_sound_on_frame.
  - exact (proj1 Htriv).
  - now apply Triv_frame_transitive.
  - now apply Triv_frame_weak_cwf.
  - now apply Triv_frame_piecewise_strongly_connected.
  - exact Hp.
Qed.

Theorem S4Point4McK_weaker_than_Triv :
  forall p : formula nat, S4Point4McK_proves p -> Triv_proves p.
Proof.
  intros p Hp. apply Triv_complete.
  intros F Htriv.
  apply S4Point4McK_proves_sound_on_frame.
  - now apply Triv_frame_is_S4Point4McK.
  - exact Hp.
Qed.

Theorem GLPoint3_weaker_than_Ver :
  forall p : formula nat, GLPoint3_proves p -> Ver_proves p.
Proof.
  intros p Hp. apply Ver_complete.
  intros F Hiso.
  apply GLPoint3_proves_sound_on_frame.
  - now apply isolated_frame_transitive.
  - now apply isolated_frame_cwf.
  - now apply isolated_frame_piecewise_connected.
  - exact Hp.
Qed.

(** * Two-world counterframes *)

Inductive trivver_two_world : Type := TV0 | TV1.

Lemma trivver_true : True.
Proof. constructor. Qed.

Definition trivver_all_relation (_ _ : trivver_two_world) : Prop := True.

Definition trivver_all_frame : frame :=
  {| World := trivver_two_world; Rel := trivver_all_relation |}.

Lemma trivver_all_symmetric : frame_symmetric trivver_all_frame.
Proof. intros [] [] _; exact trivver_true. Qed.

Lemma trivver_all_transitive : frame_transitive trivver_all_frame.
Proof. intros [] [] [] _ _; exact trivver_true. Qed.

Definition trivver_preorder_relation
    (x y : trivver_two_world) : Prop :=
  match x, y with
  | TV1, TV0 => False
  | _, _ => True
  end.

Definition trivver_preorder_frame : frame :=
  {| World := trivver_two_world; Rel := trivver_preorder_relation |}.

Lemma trivver_two_world_finite :
  finite_frame trivver_preorder_frame.
Proof.
  exists [TV0; TV1]. intros []; simpl; auto.
Qed.

Lemma trivver_preorder_reflexive :
  frame_reflexive trivver_preorder_frame.
Proof. intros []; exact trivver_true. Qed.

Lemma trivver_preorder_transitive :
  frame_transitive trivver_preorder_frame.
Proof. intros [] [] [] Hxy Hyz; simpl in *; tauto. Qed.

Lemma trivver_preorder_weak_cwf :
  frame_weak_converse_well_founded trivver_preorder_frame.
Proof.
  intros X [x Hx]. destruct (classic (X TV1)) as [H1 | Hnot1].
  - exists TV1; split; [exact H1 |].
    intros [] Hy R; simpl in R; [contradiction | reflexivity].
  - assert (H0 : X TV0).
    { destruct x; [exact Hx | contradiction]. }
    exists TV0; split; [exact H0 |].
    intros [] Hy R; [reflexivity | contradiction].
Qed.

Lemma trivver_preorder_piecewise_strongly_connected :
  frame_piecewise_strongly_connected trivver_preorder_frame.
Proof. intros [] [] [] Hxy Hxz; simpl in *; tauto. Qed.

Lemma trivver_preorder_sobocinski :
  frame_sobocinski trivver_preorder_frame.
Proof.
  intros [] [] [] Hneq Rxy Rxz; simpl in *; try contradiction;
    exact trivver_true.
Qed.

Lemma trivver_preorder_mckinsey :
  frame_mckinsey trivver_preorder_frame.
Proof.
  intros x. exists TV1; split.
  - destruct x; exact trivver_true.
  - intros []; simpl; intros H; [contradiction | reflexivity].
Qed.

Definition trivver_strict_relation
    (x y : trivver_two_world) : Prop :=
  match x, y with
  | TV0, TV1 => True
  | _, _ => False
  end.

Definition trivver_strict_frame : frame :=
  {| World := trivver_two_world; Rel := trivver_strict_relation |}.

Lemma trivver_strict_finite : finite_frame trivver_strict_frame.
Proof. exists [TV0; TV1]. intros []; simpl; auto. Qed.

Lemma trivver_strict_transitive : frame_transitive trivver_strict_frame.
Proof. intros [] [] [] Hxy Hyz; simpl in *; tauto. Qed.

Lemma trivver_strict_irreflexive : frame_irreflexive trivver_strict_frame.
Proof. intros []; simpl; tauto. Qed.

Lemma trivver_strict_cwf :
  frame_converse_well_founded trivver_strict_frame.
Proof.
  intros X [x Hx]. destruct (classic (X TV1)) as [H1 | Hnot1].
  - exists TV1; split; [exact H1 |].
    intros [] Hy R; simpl in R; contradiction.
  - assert (H0 : X TV0).
    { destruct x; [exact Hx | contradiction]. }
    exists TV0; split; [exact H0 |].
    intros [] Hy R; simpl in R; [contradiction | exact (Hnot1 Hy)].
Qed.

Lemma trivver_strict_piecewise_connected :
  frame_piecewise_connected trivver_strict_frame.
Proof. intros [] [] [] Hxy Hxz; simpl in *; tauto. Qed.

(** * Strict logical inclusions *)

Theorem KB4_strictly_weaker_KTc :
  normal_strictly_weaker KB4_proves KTc_proves.
Proof.
  split.
  - exact KB4_weaker_than_KTc.
  - exists (Tc (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HKB4.
      pose proof (KB4_proves_sound_on_frame trivver_all_symmetric
        trivver_all_transitive HKB4) as Hvalid.
      specialize (Hvalid
        (fun _ w => w = TV0) TV0 eq_refl TV1 trivver_true).
      discriminate.
Qed.

Theorem KTc_strictly_weaker_Triv :
  normal_strictly_weaker KTc_proves Triv_proves.
Proof.
  split.
  - exact (@KTc_weaker_than_Triv nat).
  - exists (T (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HKTc.
      pose proof (KTc_proves_sound_on_frame
        (F := irreflexive_singleton_frame)
        (p := T (Atom 0))
        (fun x y Rxy => False_rect _ Rxy) HKTc) as Hvalid.
      specialize (Hvalid (fun _ _ => False) tt).
      apply Hvalid. intros [] R. contradiction.
Qed.

Theorem KTc_strictly_weaker_Ver :
  normal_strictly_weaker KTc_proves Ver_proves.
Proof.
  split.
  - exact (@KTc_weaker_than_Ver nat).
  - exists (Ver Bottom); split.
    + apply Np_extra. exists Bottom. reflexivity.
    + intro HKTc.
      pose proof (KTc_proves_sound_on_frame
        (F := reflexive_singleton_frame)
        (p := Ver Bottom) reflexive_singleton_coreflexive HKTc) as Hvalid.
      exact (Hvalid (fun _ _ => False) tt tt trivver_true).
Qed.

Theorem GrzPoint3_strictly_weaker_Triv :
  normal_strictly_weaker GrzPoint3_proves Triv_proves.
Proof.
  split.
  - exact GrzPoint3_weaker_than_Triv.
  - exists (Tc (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HGrz3.
      assert (Hframe :
        boxdot_finite_GrzPoint3_frame trivver_preorder_frame).
      {
        unfold boxdot_finite_GrzPoint3_frame,
          boxdot_finite_Grz_frame. repeat split.
        - exact trivver_two_world_finite.
        - exact trivver_preorder_reflexive.
        - exact trivver_preorder_transitive.
        - exact trivver_preorder_weak_cwf.
        - exact trivver_preorder_piecewise_strongly_connected.
      }
      pose proof (GrzPoint3_proves_sound_on_finite_frame
        (p := Tc (Atom 0)) (F := trivver_preorder_frame)
        Hframe HGrz3) as Hvalid.
      specialize (Hvalid (fun _ w => w = TV0) TV0 eq_refl TV1
        trivver_true).
      discriminate.
Qed.

Theorem S4Point4McK_strictly_weaker_Triv :
  normal_strictly_weaker S4Point4McK_proves Triv_proves.
Proof.
  split.
  - exact S4Point4McK_weaker_than_Triv.
  - exists (Tc (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HS4.
      assert (Hframe :
        S4Point4McK_kripke_frame_class trivver_preorder_frame).
      {
        repeat split.
        - exact trivver_preorder_reflexive.
        - exact trivver_preorder_transitive.
        - exact trivver_preorder_sobocinski.
        - exact trivver_preorder_mckinsey.
      }
      pose proof (S4Point4McK_proves_sound_on_frame
        (F := trivver_preorder_frame) (p := Tc (Atom 0))
        Hframe HS4) as Hsound.
      specialize (Hsound (fun _ w => w = TV0) TV0 eq_refl TV1
        trivver_true).
      discriminate.
Qed.

Theorem GLPoint3_strictly_weaker_Ver :
  normal_strictly_weaker GLPoint3_proves Ver_proves.
Proof.
  split.
  - exact GLPoint3_weaker_than_Ver.
  - exists (Ver Bottom); split.
    + apply Np_extra. exists Bottom. reflexivity.
    + intro HGL3.
      assert (Hframe : boxdot_finite_GLPoint3_frame trivver_strict_frame).
      {
        unfold boxdot_finite_GLPoint3_frame,
          boxdot_finite_GL_frame. repeat split.
        - exact trivver_strict_finite.
        - exact trivver_strict_transitive.
        - exact trivver_strict_cwf.
        - exact trivver_strict_piecewise_connected.
      }
      pose proof (GLPoint3_proves_sound_on_finite_frame
        (p := Ver Bottom) (F := trivver_strict_frame)
        Hframe HGL3) as Hvalid.
      exact (Hvalid (fun _ _ => False) TV0 TV1 trivver_true).
Qed.
