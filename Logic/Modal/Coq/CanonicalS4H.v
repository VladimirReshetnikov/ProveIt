(**
  Canonical completeness for S4H.

  This module ports the mathematically proved surface of the pinned
  Foundation files [Modal/Kripke/AxiomH.lean] and
  [Modal/Kripke/Logic/S4H.lean].  A frame is detour-free when every
  composable pair [x R u R y] has its middle point equal to one endpoint.
  The semantic correspondence for H is provided by
  [CorrespondenceExtensions]; here we add the Hilbert schema, its generic
  canonical-frame theorem, and the resulting S4H metatheory.

  The canonical proof follows Foundation's separating-formula argument.
  If a purported detour has distinct middle point [U], maximal-consistent-
  theory separators give formulas true at each endpoint and false at [U].
  Their disjunction, together with H, is propagated along the two edges and
  forced at [U], a contradiction.

  The pinned Foundation declaration of finite S4H completeness is proved
  with [sorry].  No finite-completeness theorem is asserted below.  We do
  prove the sound finite-frame inclusion into finite Grz frames, which is
  independent of that missing result, and use ordinary canonical
  completeness for the strict comparison with Grz.
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  Root Filtration NormalHilbert CanonicalExtensions CanonicalPoint2
  CanonicalCombinations Boxdot CanonicalPoint4.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The H schema and S4H *)

Definition schema_H : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = H q.

Definition S4H_schema : modal_axiom_schema :=
  schema_union S4_schema schema_H.

Definition S4H_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4H_schema AtomType.

Lemma schema_H_substitution_closed :
  schema_substitution_closed schema_H.
Proof.
  intros A B sigma p [q ->].
  exists (substitute sigma q). reflexivity.
Qed.

Lemma S4H_schema_substitution_closed :
  schema_substitution_closed S4H_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact schema_T_substitution_closed.
    + exact schema_Four_substitution_closed.
  - exact schema_H_substitution_closed.
Qed.

Lemma schema_T_included_S4H : schema_included schema_T S4H_schema.
Proof. intros AtomType p Hp; now left; left. Qed.

Lemma schema_Four_included_S4H :
  schema_included schema_Four S4H_schema.
Proof. intros AtomType p Hp; now left; right. Qed.

Lemma schema_H_included_S4H : schema_included schema_H S4H_schema.
Proof. intros AtomType p Hp; now right. Qed.

Definition S4H_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\ frame_detour_free F.

Definition S4H_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ S4H_frame_class F.

(** * Relational facts from AxiomH *)

(** Direct point generation is Foundation's root restriction [F | r]. *)
Lemma point_generated_detour_free :
  forall (F : frame) (r : World F),
    frame_detour_free F ->
    frame_detour_free (point_generated_frame F r).
Proof.
  intros F r Hdet [x hx] [u hu] [y hy] Rxu Ruy; simpl in *.
  destruct (Hdet x u y Rxu Ruy) as [Hux | Huy].
  - left. subst u. apply point_generated_sig_eq.
  - right. subst y. apply point_generated_sig_eq.
Qed.

Lemma s4h_reflexive_singleton_detour_free :
  frame_detour_free reflexive_singleton_frame.
Proof.
  intros [] [] [] _ _. now left.
Qed.

(** Detour-freeness is stronger than the maximal-element condition used by
    Grz.  The proof is classical only in deciding whether the chosen point
    has a distinct successor in the given nonempty subset. *)
Theorem detour_free_weak_converse_well_founded :
  forall F : frame,
    frame_detour_free F -> frame_weak_converse_well_founded F.
Proof.
  intros F Hdet X [x Hx].
  destruct (classic (exists y,
    X y /\ Rel F x y /\ x <> y))
    as [[y [Hy [Rxy Hxy]]] | Hterminal].
  - exists y; split; [exact Hy |].
    intros z Hz Ryz.
    destruct (Hdet x y z Rxy Ryz) as [Hyx | Hyz].
    + exfalso. apply Hxy. now symmetry.
    + exact Hyz.
  - exists x; split; [exact Hx |].
    intros y Hy Rxy. apply NNPP. intro Hxy.
    apply Hterminal. exists y. repeat split; assumption.
Qed.

(** * Soundness and consistency *)

Lemma schema_H_valid_on_detour_free :
  forall F,
    frame_detour_free F -> schema_valid_on_frame schema_H F.
Proof.
  intros F Hdet AtomType p [q ->].
  now apply valid_H_of_detour_free.
Qed.

Theorem schema_H_normal_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_detour_free F ->
    normal_proves schema_H p -> valid F p.
Proof.
  intros AtomType F p HD Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  now apply schema_H_valid_on_detour_free.
Qed.

Theorem schema_H_is_consistent :
  forall AtomType, ~ @normal_proves schema_H AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := schema_H) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_H_valid_on_detour_free.
    exact s4h_reflexive_singleton_detour_free.
Qed.

Theorem S4H_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F -> frame_detour_free F ->
    S4H_proves p -> valid F p.
Proof.
  intros AtomType F p HR HT HD Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply schema_H_valid_on_detour_free.
Qed.

Theorem S4H_is_consistent :
  forall AtomType, ~ @S4H_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := S4H_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_T_valid_on_reflexive.
        exact reflexive_singleton_reflexive.
      * apply schema_Four_valid_on_transitive.
        exact reflexive_singleton_transitive.
    + apply schema_H_valid_on_detour_free.
      exact s4h_reflexive_singleton_detour_free.
Qed.

(** * Small propositional lemmas for the canonical proof *)

Lemma normal_proves_s4h_or_left :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p (Or p q)).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hp.
  apply (proj2 (@satisfies_or nat F V w p q)). now left.
Qed.

Lemma normal_proves_s4h_or_right :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp q (Or p q)).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hq.
  apply (proj2 (@satisfies_or nat F V w p q)). now right.
Qed.

Lemma normal_proves_s4h_neg_or :
  forall Ax (p q : formula nat),
    normal_proves Ax
      (Imp (Neg p) (Imp (Neg q) (Neg (Or p q)))).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hnegp Hnegq Hor.
  destruct (proj1 (@satisfies_or nat F V w p q) Hor) as [Hp | Hq].
  - exact (Hnegp Hp).
  - exact (Hnegq Hq).
Qed.

(** * Generic canonicality of H *)

(** Every normal extension containing all substitution instances of H has a
    detour-free canonical frame. *)
Theorem normal_canonical_detour_free_of_schema_H :
  forall Ax,
    schema_included schema_H Ax ->
    frame_detour_free (normal_canonical_frame Ax).
Proof.
  intros Ax HH X U Y RXU RUY.
  destruct (classic (U = X \/ U = Y)) as [Hendpoint | Hproper].
  - exact Hendpoint.
  - exfalso.
    assert (HXU : X <> U).
    { intro HXU. apply Hproper. left. now symmetry. }
    assert (HYU : Y <> U).
    { intro HYU. apply Hproper. right. now symmetry. }
    destruct (@normal_mct_separator Ax X U HXU)
      as [phi [HphiX HnegphiU]].
    destruct (@normal_mct_separator Ax Y U HYU)
      as [psi [HpsiY HnegpsiU]].
    set (d := Or phi psi).
    assert (HdX : normal_mct_mem X d).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem. apply normal_proves_s4h_or_left.
      - apply ND_assumption. exact HphiX.
    }
    assert (HdY : normal_mct_mem Y d).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem. apply normal_proves_s4h_or_right.
      - apply ND_assumption. exact HpsiY.
    }
    assert (HnegdU : normal_mct_mem U (Neg d)).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - eapply ND_mp.
        + apply ND_theorem. apply normal_proves_s4h_neg_or.
        + apply ND_assumption. exact HnegphiU.
      - apply ND_assumption. exact HnegpsiU.
    }
    assert (HHX : normal_mct_mem X (H d)).
    {
      apply normal_mct_derivable_mem. apply ND_theorem. apply Np_extra.
      apply HH. exists d. reflexivity.
    }
    change (normal_mct_mem X
      (Imp d (Box (Imp (Dia d) d)))) in HHX.
    assert (HboxlocalX : normal_mct_mem X (Box (Imp (Dia d) d))).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_assumption. exact HHX.
      - apply ND_assumption. exact HdX.
    }
    pose proof (RXU (Imp (Dia d) d) HboxlocalX) as HlocalU.
    assert (HdiadU : normal_mct_mem U (Dia d)).
    {
      now apply normal_canonical_predecessor_dia_mem with (N := Y).
    }
    assert (HdU : normal_mct_mem U d).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_assumption. exact HlocalU.
      - apply ND_assumption. exact HdiadU.
    }
    exact (@normal_mct_not_both Ax U d HdU HnegdU).
Qed.

(** * S4H canonicality and ordinary completeness *)

Lemma S4H_canonical_frame :
  S4H_frame_class (normal_canonical_frame S4H_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    exact schema_T_included_S4H.
  - apply normal_canonical_transitive_of_schema_Four.
    exact schema_Four_included_S4H.
  - apply normal_canonical_detour_free_of_schema_H.
    exact schema_H_included_S4H.
Qed.

Theorem S4H_complete :
  forall p : formula nat,
    normal_valid_on_class S4H_frame_class p -> S4H_proves p.
Proof.
  unfold S4H_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4H_schema) (C := S4H_frame_class)).
  - exact (@S4H_is_consistent nat).
  - exact S4H_canonical_frame.
Qed.

Theorem S4H_sound_complete :
  forall p : formula nat,
    S4H_proves p <-> normal_valid_on_class S4H_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HR [HT HD]].
    now apply S4H_proves_sound_on_frame.
  - apply S4H_complete.
Qed.

(** * The proved finite-frame inclusion, and the upstream boundary *)

Lemma S4H_frame_is_Grz_frame :
  forall F,
    S4H_frame_class F -> boxdot_Grz_frame F.
Proof.
  intros F [HR [HT HD]]. repeat split; try assumption.
  now apply detour_free_weak_converse_well_founded.
Qed.

Theorem finite_S4H_frame_is_finite_Grz_frame :
  forall F,
    S4H_finite_frame_class F -> boxdot_finite_Grz_frame F.
Proof.
  intros F [Hfinite HS4H]. split; [exact Hfinite |].
  now apply S4H_frame_is_Grz_frame.
Qed.

(** The pinned [S4H.lean] next declares finite S4H completeness with
    [by sorry].  This port intentionally stops at the sound frame-class
    inclusion above; in particular, it exposes no finite S4H completeness
    theorem or assumption. *)

(** * Grz is strictly weaker than S4H *)

Theorem Grz_weaker_than_S4H :
  forall p : formula nat, Grz_proves p -> S4H_proves p.
Proof.
  intros p HGrz. apply S4H_complete.
  intros F [HR [HT HD]].
  apply Grz_proves_sound_on_reflexive_transitive_weak_cwf_frame.
  - exact HR.
  - exact HT.
  - now apply detour_free_weak_converse_well_founded.
  - exact HGrz.
Qed.

(** Foundation's strictness witness is the reflexive order on [Fin 3].
    [CanonicalPoint4] already supplies the isomorphic chain
    [P40 <= P41 <= P42], which we reuse read-only here. *)
Lemma s4h_three_chain_weak_converse_well_founded :
  frame_weak_converse_well_founded point4_three_chain_frame.
Proof.
  intros X [x Hx].
  destruct (classic (X P42)) as [H2 | Hn2].
  - exists P42; split; [exact H2 |].
    intros y Hy R2y. destruct y; inversion R2y; reflexivity.
  - destruct (classic (X P41)) as [H1 | Hn1].
    + exists P41; split; [exact H1 |].
      intros y Hy R1y. destruct y; inversion R1y.
      * reflexivity.
      * exfalso. now apply Hn2.
    + assert (H0 : X P40).
      { destruct x; assumption || contradiction. }
      exists P40; split; [exact H0 |].
      intros y Hy _. destruct y.
      * reflexivity.
      * exfalso. now apply Hn1.
      * exfalso. now apply Hn2.
Qed.

Lemma s4h_three_chain_finite_Grz_frame :
  boxdot_finite_Grz_frame point4_three_chain_frame.
Proof.
  split.
  - exact point4_three_chain_finite.
  - repeat split.
    + exact point4_three_chain_reflexive.
    + exact point4_three_chain_transitive.
    + exact s4h_three_chain_weak_converse_well_founded.
Qed.

Lemma s4h_three_chain_not_detour_free :
  ~ frame_detour_free point4_three_chain_frame.
Proof.
  intro Hdet.
  destruct (Hdet P40 P41 P42 point4_R01 point4_R12) as [H | H];
    discriminate.
Qed.

Definition s4h_three_chain_valuation :
  valuation nat point4_three_chain_frame :=
  fun _ w => w <> P41.

Lemma s4h_three_chain_falsifies_H_at_root :
  ~ satisfies point4_three_chain_frame s4h_three_chain_valuation
      P40 (H (Atom 0)).
Proof.
  intro Hroot.
  assert (Hp0 : satisfies point4_three_chain_frame
    s4h_three_chain_valuation P40 (Atom 0)).
  { simpl. discriminate. }
  pose proof (Hroot Hp0 P41 point4_R01) as Hmiddle.
  assert (Hdia : satisfies point4_three_chain_frame
    s4h_three_chain_valuation P41 (Dia (Atom 0))).
  {
    apply satisfies_dia_intro. exists P42; split.
    - exact point4_R12.
    - simpl. discriminate.
  }
  exact ((Hmiddle Hdia) eq_refl).
Qed.

Lemma s4h_three_chain_not_valid_H :
  ~ valid point4_three_chain_frame (H (Atom 0)).
Proof.
  intro Hvalid. apply s4h_three_chain_falsifies_H_at_root.
  exact (Hvalid s4h_three_chain_valuation P40).
Qed.

Theorem Grz_strictly_weaker_S4H :
  normal_strictly_weaker Grz_proves S4H_proves.
Proof.
  split.
  - exact Grz_weaker_than_S4H.
  - exists (H (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HGrz.
      pose proof
        (Grz_proves_sound_on_reflexive_transitive_weak_cwf_frame
          point4_three_chain_reflexive point4_three_chain_transitive
          s4h_three_chain_weak_converse_well_founded HGrz) as Hvalid.
      exact (s4h_three_chain_not_valid_H Hvalid).
Qed.
