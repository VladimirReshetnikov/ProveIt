(** Finite completeness for Int, KC, and LC via the existing modal
    filtration theorems.

    A modal preorder with valuation [V] becomes a propositional Kripke model
    by interpreting atom [a] at [w] as modal truth of [Box (Atom a)] at [w].
    This valuation is hereditary, and a direct induction identifies forcing
    of [p] with modal truth of its Gödel translation under the original [V].
    Consequently the already checked finite completeness theorems for S4,
    S4.2, and S4.3 supply all three propositional finite completeness results
    without duplicating filtration. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  Syntax Kripke Correspondence FrameProperties Filtration LogicInfrastructure
  NormalHilbert Boxdot CanonicalExtensions StructuralFrames
  CanonicalPoint2 CanonicalPoint3 GodelTranslation
  PropositionalFormula PropositionalHilbert PropositionalKripke
  PropositionalKripkeCanonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pkripke_frame_finite (F : pkripke_frame) : Prop :=
  exists cover : list (pkripke_world F), forall w, List.In w cover.

Definition pkripke_finite_strongly_convergent (F : pkripke_frame) : Prop :=
  pkripke_frame_finite F /\ pkripke_frame_strongly_convergent F.

Definition pkripke_finite_strongly_connected (F : pkripke_frame) : Prop :=
  pkripke_frame_finite F /\ pkripke_frame_strongly_connected F.

Definition pkripke_frame_antisymmetric (F : pkripke_frame) : Prop :=
  forall x y, pkripke_access F x y -> pkripke_access F y x -> x = y.

Definition pkripke_finite_partial_order (F : pkripke_frame) : Prop :=
  pkripke_frame_finite F /\ pkripke_frame_antisymmetric F.

Definition pkripke_finite_partial_order_convergent
    (F : pkripke_frame) : Prop :=
  pkripke_frame_finite F /\ pkripke_frame_antisymmetric F /\
  pkripke_frame_strongly_convergent F.

Definition pkripke_finite_partial_order_connected
    (F : pkripke_frame) : Prop :=
  pkripke_frame_finite F /\ pkripke_frame_antisymmetric F /\
  pkripke_frame_strongly_connected F.

(** Quotient a preorder by mutual accessibility.  [StructuralFrames]
    represents quotient classes extensionally, so no choice of canonical
    representatives enters the construction. *)
Definition pkripke_modal_frame (F : pkripke_frame) : frame :=
  forcing_modal_frame (pkripke_access F).

Arguments pkripke_modal_frame F : clear implicits.

Definition pkripke_skeleton_frame (F : pkripke_frame) : pkripke_frame :=
  {| pkripke_world := cluster (pkripke_modal_frame F);
     pkripke_access := cluster_rel (pkripke_modal_frame F);
     pkripke_access_refl :=
       @skeleton_reflexive (pkripke_modal_frame F)
         (pkripke_access_refl F);
     pkripke_access_trans :=
       @skeleton_transitive (pkripke_modal_frame F)
         (pkripke_access_trans F) |}.

Arguments pkripke_skeleton_frame F : clear implicits.

Definition pkripke_skeleton_valuation {AtomType : Type}
    (M : pkripke_model AtomType) :
    pkripke_valuation AtomType
      (pkripke_skeleton_frame (pkripke_model_frame M)).
Proof.
  set (F := pkripke_modal_frame (pkripke_model_frame M)).
  refine (@Build_pkripke_valuation AtomType
    (pkripke_skeleton_frame (pkripke_model_frame M))
    (fun a C => exists x, cluster_member C x /\
      pkripke_forces M x (PAtom a)) _).
  intros a C D HCD [x [Hx Hxatom]].
  destruct (cluster_has_representative C) as [c ->].
  destruct (cluster_has_representative D) as [d ->].
  assert (Rcd : pkripke_access (pkripke_model_frame M) c d).
  { exact (proj1 (@cluster_rel_of_representatives_iff
      (pkripke_modal_frame (pkripke_model_frame M))
      (pkripke_access_trans (pkripke_model_frame M)) c d) HCD). }
  exists d. split; [apply cluster_equiv_refl |].
  eapply pkripke_forces_persistent; [| exact Hxatom].
  destruct Hx as [-> | [_ Hxc]].
  - exact Rcd.
  - eapply pkripke_access_trans; eauto.
Defined.

Definition pkripke_skeleton_model {AtomType : Type}
    (M : pkripke_model AtomType) : pkripke_model AtomType :=
  {| pkripke_model_frame :=
       pkripke_skeleton_frame (pkripke_model_frame M);
     pkripke_model_valuation := pkripke_skeleton_valuation M |}.

Arguments pkripke_skeleton_model {AtomType} M.

Theorem pkripke_skeleton_forces_iff :
  forall (AtomType : Type) (M : pkripke_model AtomType)
      (p : pformula AtomType) x,
    pkripke_forces (pkripke_skeleton_model M)
      (cluster_of (pkripke_modal_frame (pkripke_model_frame M)) x) p <->
    pkripke_forces M x p.
Proof.
  intros AtomType M p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro x.
  - change ((exists y,
      cluster_member
        (cluster_of (pkripke_modal_frame (pkripke_model_frame M)) x) y /\
      pkripke_forces M y (PAtom a)) <->
      pkripke_forces M x (PAtom a)).
    split.
    + intros [y [Hy Hay]].
      eapply pkripke_forces_persistent; [| exact Hay].
      destruct Hy as [-> | [_ Hyx]].
      * apply pkripke_access_refl.
      * exact Hyx.
    + intro Hax. exists x. split; [apply cluster_equiv_refl | exact Hax].
  - reflexivity.
  - rewrite pkripke_forces_and, pkripke_forces_and, IHp, IHq.
    reflexivity.
  - rewrite pkripke_forces_or, pkripke_forces_or, IHp, IHq.
    reflexivity.
  - rewrite pkripke_forces_imp, pkripke_forces_imp. split.
    + intros H y Rxy Hyp.
      apply (proj1 (IHq y)), H with
        (v := cluster_of
          (pkripke_modal_frame (pkripke_model_frame M)) y).
      * apply (proj2 (@cluster_rel_of_representatives_iff
          (pkripke_modal_frame (pkripke_model_frame M))
          (pkripke_access_trans (pkripke_model_frame M)) x y)).
        exact Rxy.
      * now apply (proj2 (IHp y)).
    + intros H D HxD HpD.
      destruct (cluster_has_representative D) as [y ->].
      apply (proj2 (IHq y)), H with (v := y).
      * apply (proj1 (@cluster_rel_of_representatives_iff
          (pkripke_modal_frame (pkripke_model_frame M))
          (pkripke_access_trans (pkripke_model_frame M)) x y)).
        exact HxD.
      * now apply (proj1 (IHp y)).
Qed.

Lemma pkripke_skeleton_finite :
  forall F, pkripke_frame_finite F ->
    pkripke_frame_finite (pkripke_skeleton_frame F).
Proof.
  intros F HF. exact (@skeleton_finite (pkripke_modal_frame F)
    (pkripke_access_trans F) HF).
Qed.

Lemma pkripke_skeleton_antisymmetric :
  forall F, pkripke_frame_antisymmetric (pkripke_skeleton_frame F).
Proof.
  intro F. exact (@skeleton_antisymmetric (pkripke_modal_frame F)
    (pkripke_access_trans F)).
Qed.

Lemma pkripke_skeleton_strongly_convergent :
  forall F, pkripke_frame_strongly_convergent F ->
    pkripke_frame_strongly_convergent (pkripke_skeleton_frame F).
Proof.
  intros F HC C D E HCD HCE.
  destruct (cluster_has_representative C) as [x ->].
  destruct (cluster_has_representative D) as [y ->].
  destruct (cluster_has_representative E) as [z ->].
  apply (proj1 (@cluster_rel_of_representatives_iff
    (pkripke_modal_frame F)
    (pkripke_access_trans F) x y)) in HCD.
  apply (proj1 (@cluster_rel_of_representatives_iff
    (pkripke_modal_frame F)
    (pkripke_access_trans F) x z)) in HCE.
  destruct (HC x y z HCD HCE) as [u [Hyu Hzu]].
  exists (cluster_of (pkripke_modal_frame F) u). split.
  - now apply (proj2 (@cluster_rel_of_representatives_iff
      (pkripke_modal_frame F)
      (pkripke_access_trans F) y u)).
  - now apply (proj2 (@cluster_rel_of_representatives_iff
      (pkripke_modal_frame F)
      (pkripke_access_trans F) z u)).
Qed.

Lemma pkripke_skeleton_strongly_connected :
  forall F, pkripke_frame_strongly_connected F ->
    pkripke_frame_strongly_connected (pkripke_skeleton_frame F).
Proof.
  intros F HC C D E HCD HCE.
  destruct (cluster_has_representative C) as [x ->].
  destruct (cluster_has_representative D) as [y ->].
  destruct (cluster_has_representative E) as [z ->].
  apply (proj1 (@cluster_rel_of_representatives_iff
    (pkripke_modal_frame F)
    (pkripke_access_trans F) x y)) in HCD.
  apply (proj1 (@cluster_rel_of_representatives_iff
    (pkripke_modal_frame F)
    (pkripke_access_trans F) x z)) in HCE.
  destruct (HC x y z HCD HCE) as [Hyz | Hzy].
  - left. now apply (proj2 (@cluster_rel_of_representatives_iff
      (pkripke_modal_frame F)
      (pkripke_access_trans F) y z)).
  - right. now apply (proj2 (@cluster_rel_of_representatives_iff
      (pkripke_modal_frame F)
      (pkripke_access_trans F) z y)).
Qed.

Definition modal_preorder_pkripke_frame (F : frame)
    (HR : frame_reflexive F) (HT : frame_transitive F) : pkripke_frame :=
  {| pkripke_world := World F;
     pkripke_access := Rel F;
     pkripke_access_refl := HR;
     pkripke_access_trans := HT |}.

Arguments modal_preorder_pkripke_frame F HR HT : clear implicits.

Definition modal_boxed_pkripke_valuation {AtomType : Type} (F : frame)
    (HR : frame_reflexive F) (HT : frame_transitive F)
    (V : valuation AtomType F) :
    pkripke_valuation AtomType (modal_preorder_pkripke_frame F HR HT).
Proof.
  refine (@Build_pkripke_valuation AtomType
    (modal_preorder_pkripke_frame F HR HT)
    (fun a w => satisfies F V w (Box (Atom a))) _).
  intros a x y Rxy Hx z Ryz. apply Hx with (u := z).
  exact (HT x y z Rxy Ryz).
Defined.

Arguments modal_boxed_pkripke_valuation {AtomType} F HR HT V.

Definition modal_boxed_pkripke_model {AtomType : Type} (F : frame)
    (HR : frame_reflexive F) (HT : frame_transitive F)
    (V : valuation AtomType F) : pkripke_model AtomType :=
  {| pkripke_model_frame := modal_preorder_pkripke_frame F HR HT;
     pkripke_model_valuation :=
       modal_boxed_pkripke_valuation F HR HT V |}.

Arguments modal_boxed_pkripke_model {AtomType} F HR HT V.

Theorem modal_boxed_pkripke_forces_iff_godel :
  forall (AtomType : Type) (F : frame)
      (HR : frame_reflexive F) (HT : frame_transitive F)
      (V : valuation AtomType F) (p : pformula AtomType) w,
    pkripke_forces (modal_boxed_pkripke_model F HR HT V) w p <->
    satisfies F V w (godel_translate p).
Proof.
  intros AtomType F HR HT V p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro w.
  - reflexivity.
  - reflexivity.
  - change (pkripke_forces (modal_boxed_pkripke_model F HR HT V) w
      (PAnd p q) <->
      satisfies F V w (And (godel_translate p) (godel_translate q))).
    rewrite pkripke_forces_and, satisfies_and, IHp, IHq. tauto.
  - change (pkripke_forces (modal_boxed_pkripke_model F HR HT V) w
      (POr p q) <->
      satisfies F V w (Or (godel_translate p) (godel_translate q))).
    rewrite pkripke_forces_or, satisfies_or, IHp, IHq. tauto.
  - change (pkripke_forces (modal_boxed_pkripke_model F HR HT V) w
      (PImp p q) <->
      satisfies F V w (Box (Imp (godel_translate p) (godel_translate q)))).
    rewrite pkripke_forces_imp. cbn [satisfies]. split.
    + intros H v Rwv Hvp. apply (proj1 (IHq v)).
      apply (H v Rwv). now apply (proj2 (IHp v)).
    + intros H v Rwv Hvp. apply (proj2 (IHq v)).
      apply (H v Rwv). now apply (proj1 (IHp v)).
Qed.

Theorem pkripke_forces_iff_forcing_modal_godel :
  forall (AtomType : Type) (M : pkripke_model AtomType)
      (p : pformula AtomType) w,
    pkripke_forces M w p <->
    satisfies
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) AtomType
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) w
      (godel_translate p).
Proof.
  intros AtomType M p w.
  exact (godel_translate_forcing_iff_modal_satisfies
    (pkripke_access_refl (pkripke_model_frame M))
    (pkripke_access_trans (pkripke_model_frame M))
    (pkripke_generic_int_forcing M) p w).
Qed.

Lemma modal_finite_to_pkripke_finite :
  forall F HR HT,
    finite_frame F ->
    pkripke_frame_finite (modal_preorder_pkripke_frame F HR HT).
Proof. intros F HR HT [cover Hcover]. now exists cover. Qed.

Lemma godel_valid_on_finite_S4_of_pkripke :
  forall p : pformula nat,
    pkripke_frame_class_valid pkripke_frame_finite p ->
    normal_valid_on_class S4_finite_frame_class (godel_translate p).
Proof.
  intros p Hfinite F [HF [HR HT]] V w.
  apply (proj1 (@modal_boxed_pkripke_forces_iff_godel
    nat F HR HT V p w)).
  exact (Hfinite (modal_preorder_pkripke_frame F HR HT)
    (modal_finite_to_pkripke_finite HR HT HF)
    (modal_boxed_pkripke_valuation F HR HT V) w).
Qed.

Lemma godel_valid_on_finite_S4Point2_of_pkripke :
  forall p : pformula nat,
    pkripke_frame_class_valid pkripke_finite_strongly_convergent p ->
    normal_valid_on_class S4Point2_finite_frame_class (godel_translate p).
Proof.
  intros p Hfinite F [HF [HR [HT HC]]] V w.
  apply (proj1 (@modal_boxed_pkripke_forces_iff_godel
    nat F HR HT V p w)).
  exact (Hfinite (modal_preorder_pkripke_frame F HR HT)
    (conj (modal_finite_to_pkripke_finite HR HT HF) HC)
    (modal_boxed_pkripke_valuation F HR HT V) w).
Qed.

Lemma godel_valid_on_finite_S4Point3_of_pkripke :
  forall p : pformula nat,
    pkripke_frame_class_valid pkripke_finite_strongly_connected p ->
    normal_valid_on_class S4Point3_finite_frame_class (godel_translate p).
Proof.
  intros p Hfinite F [HF [HR [HT HC]]] V w.
  apply (proj1 (@modal_boxed_pkripke_forces_iff_godel
    nat F HR HT V p w)).
  exact (Hfinite (modal_preorder_pkripke_frame F HR HT)
    (conj (modal_finite_to_pkripke_finite HR HT HF) HC)
    (modal_boxed_pkripke_valuation F HR HT V) w).
Qed.

Lemma pkripke_forces_of_godel_S4 :
  forall p : pformula nat, S4_proves (godel_translate p) ->
    forall (M : pkripke_model nat) w, pkripke_forces M w p.
Proof.
  intros p Hp M w.
  apply (proj2 (@pkripke_forces_iff_forcing_modal_godel nat M p w)).
  exact (@S4_proves_sound_on_preorder_frame nat
    (forcing_modal_frame
      (pkripke_access (pkripke_model_frame M)))
    (godel_translate p)
    (pkripke_access_refl (pkripke_model_frame M))
    (pkripke_access_trans (pkripke_model_frame M)) Hp
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M))) w).
Qed.

Lemma pkripke_forces_of_godel_S4Point2 :
  forall p : pformula nat, S4Point2_proves (godel_translate p) ->
    forall (M : pkripke_model nat),
    pkripke_frame_strongly_convergent (pkripke_model_frame M) ->
    forall w, pkripke_forces M w p.
Proof.
  intros p Hp M HC w.
  apply (proj2 (@pkripke_forces_iff_forcing_modal_godel nat M p w)).
  exact (@S4Point2_proves_sound_on_frame nat
    (forcing_modal_frame
      (pkripke_access (pkripke_model_frame M)))
    (godel_translate p)
    (pkripke_access_refl (pkripke_model_frame M))
    (pkripke_access_trans (pkripke_model_frame M)) HC Hp
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M))) w).
Qed.

Lemma pkripke_forces_of_godel_S4Point3 :
  forall p : pformula nat, S4Point3_proves (godel_translate p) ->
    forall (M : pkripke_model nat),
    pkripke_frame_strongly_connected (pkripke_model_frame M) ->
    forall w, pkripke_forces M w p.
Proof.
  intros p Hp M HC w.
  apply (proj2 (@pkripke_forces_iff_forcing_modal_godel nat M p w)).
  exact (@S4Point3_proves_sound_on_frame nat
    (forcing_modal_frame
      (pkripke_access (pkripke_model_frame M)))
    (godel_translate p)
    (pkripke_access_refl (pkripke_model_frame M))
    (pkripke_access_trans (pkripke_model_frame M)) HC Hp
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M))) w).
Qed.

Theorem ph_hilbert_int_pkripke_finite_complete :
  pkripke_complete (ph_hilbert_int nat) pkripke_frame_finite.
Proof.
  intros p Hfinite.
  pose proof (S4_finite_complete
    (godel_valid_on_finite_S4_of_pkripke Hfinite)) as HS4.
  apply ph_hilbert_int_pkripke_complete. intros F _ V w.
  exact (@pkripke_forces_of_godel_S4 p HS4
    {| pkripke_model_frame := F; pkripke_model_valuation := V |} w).
Qed.

Theorem ph_hilbert_kc_pkripke_finite_complete :
  pkripke_complete (ph_hilbert_kc nat)
    pkripke_finite_strongly_convergent.
Proof.
  intros p Hfinite.
  pose proof (S4Point2_finite_complete
    (godel_valid_on_finite_S4Point2_of_pkripke Hfinite)) as HS4Point2.
  apply ph_hilbert_kc_pkripke_complete. intros F HF V w.
  exact (@pkripke_forces_of_godel_S4Point2 p HS4Point2
    {| pkripke_model_frame := F; pkripke_model_valuation := V |} HF w).
Qed.

Theorem ph_hilbert_lc_pkripke_finite_complete :
  pkripke_complete (ph_hilbert_lc nat)
    pkripke_finite_strongly_connected.
Proof.
  intros p Hfinite.
  pose proof (S4Point3_finite_complete
    (godel_valid_on_finite_S4Point3_of_pkripke Hfinite)) as HS4Point3.
  apply ph_hilbert_lc_pkripke_complete. intros F HF V w.
  exact (@pkripke_forces_of_godel_S4Point3 p HS4Point3
    {| pkripke_model_frame := F; pkripke_model_valuation := V |} HF w).
Qed.

(** The source's intuitionistic frames are finite partial orders.  The
    following stronger completeness interfaces accept validity only on that
    smaller class; the skeleton truth lemma reduces them to the generalized
    finite-preorder theorems above. *)
Theorem ph_hilbert_int_pkripke_finite_partial_order_complete :
  pkripke_complete (ph_hilbert_int nat) pkripke_finite_partial_order.
Proof.
  intros p Hpartial. apply ph_hilbert_int_pkripke_finite_complete.
  intros F HF V w.
  set (M := {| pkripke_model_frame := F;
    pkripke_model_valuation := V |}).
  apply (proj1 (@pkripke_skeleton_forces_iff nat M p w)).
  apply (Hpartial (pkripke_skeleton_frame F)).
  - split.
    + now apply pkripke_skeleton_finite.
    + apply pkripke_skeleton_antisymmetric.
Qed.

Theorem ph_hilbert_kc_pkripke_finite_partial_order_complete :
  pkripke_complete (ph_hilbert_kc nat)
    pkripke_finite_partial_order_convergent.
Proof.
  intros p Hpartial. apply ph_hilbert_kc_pkripke_finite_complete.
  intros F [HF HC] V w.
  set (M := {| pkripke_model_frame := F;
    pkripke_model_valuation := V |}).
  apply (proj1 (@pkripke_skeleton_forces_iff nat M p w)).
  apply (Hpartial (pkripke_skeleton_frame F)).
  - repeat split.
    + now apply pkripke_skeleton_finite.
    + apply pkripke_skeleton_antisymmetric.
    + now apply pkripke_skeleton_strongly_convergent.
Qed.

Theorem ph_hilbert_lc_pkripke_finite_partial_order_complete :
  pkripke_complete (ph_hilbert_lc nat)
    pkripke_finite_partial_order_connected.
Proof.
  intros p Hpartial. apply ph_hilbert_lc_pkripke_finite_complete.
  intros F [HF HC] V w.
  set (M := {| pkripke_model_frame := F;
    pkripke_model_valuation := V |}).
  apply (proj1 (@pkripke_skeleton_forces_iff nat M p w)).
  apply (Hpartial (pkripke_skeleton_frame F)).
  - repeat split.
    + now apply pkripke_skeleton_finite.
    + apply pkripke_skeleton_antisymmetric.
    + now apply pkripke_skeleton_strongly_connected.
Qed.
