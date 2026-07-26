(**
  Canonical completeness for K4McK and S4McK.

  This module ports the complete theorem surfaces of the pinned Foundation
  files [Modal/Kripke/Logic/K4McK.lean] and
  [Modal/Kripke/Logic/S4McK.lean], together with the mathematically proved
  canonical-frame theorem from [Modal/Kripke/AxiomMcK.lean].

  The central construction follows Foundation's special-successor argument.
  Given a canonical world [X], extend the unboxed part of [X]'s boxed theory
  by every switch formula [diamond p -> box p].  A finite derivation from
  this seed can be summarized by one boxed formula at [X] and one formula
  which K4McK proves possible.  This makes the whole seed consistent.  Its
  Lindenbaum extension is a successor of [X], and either it is terminal or
  any one of its successors is terminal.

  All auxiliary names carry a [base_mck] prefix so that this base module can
  coexist with the independently ported S4.Point4.McK development.
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  HilbertKSoundness NormalHilbert CanonicalExtensions CanonicalPoint2
  CanonicalCombinations Modality LogicInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Schemata, calculi, and frame classes *)

Definition McK_axiom_schema : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = McK q.

Definition K4McK_schema : modal_axiom_schema :=
  schema_union schema_Four McK_axiom_schema.

Definition S4McK_schema : modal_axiom_schema :=
  schema_union S4_schema McK_axiom_schema.

Definition K4McK_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves K4McK_schema AtomType.

Definition S4McK_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4McK_schema AtomType.

Lemma McK_axiom_schema_substitution_closed :
  schema_substitution_closed McK_axiom_schema.
Proof.
  intros A B sigma p [q ->].
  exists (substitute sigma q). reflexivity.
Qed.

Lemma K4McK_schema_substitution_closed :
  schema_substitution_closed K4McK_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_Four_substitution_closed.
  - exact McK_axiom_schema_substitution_closed.
Qed.

Lemma S4McK_schema_substitution_closed :
  schema_substitution_closed S4McK_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact schema_T_substitution_closed.
    + exact schema_Four_substitution_closed.
  - exact McK_axiom_schema_substitution_closed.
Qed.

Definition K4McK_frame_class (F : frame) : Prop :=
  frame_transitive F /\ frame_mckinsey F.

Definition S4McK_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\ frame_mckinsey F.

(** * Soundness and consistency *)

Lemma McK_axiom_schema_valid_on_mckinsey :
  forall F,
    frame_mckinsey F -> schema_valid_on_frame McK_axiom_schema F.
Proof.
  intros F HM AtomType p [q ->].
  now apply valid_McK_of_mckinsey.
Qed.

Theorem K4McK_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_transitive F -> frame_mckinsey F ->
    K4McK_proves p -> valid F p.
Proof.
  intros AtomType F p HT HM Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_Four_valid_on_transitive.
  - now apply McK_axiom_schema_valid_on_mckinsey.
Qed.

Theorem S4McK_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F -> frame_mckinsey F ->
    S4McK_proves p -> valid F p.
Proof.
  intros AtomType F p HR HT HM Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply McK_axiom_schema_valid_on_mckinsey.
Qed.

Lemma base_mck_reflexive_singleton_mckinsey :
  frame_mckinsey reflexive_singleton_frame.
Proof.
  intros []. exists tt; split.
  - constructor.
  - intros []; reflexivity.
Qed.

Theorem K4McK_is_consistent :
  forall AtomType, ~ @K4McK_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := K4McK_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_Four_valid_on_transitive.
      exact reflexive_singleton_transitive.
    + apply McK_axiom_schema_valid_on_mckinsey.
      exact base_mck_reflexive_singleton_mckinsey.
Qed.

Theorem S4McK_is_consistent :
  forall AtomType, ~ @S4McK_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := S4McK_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_T_valid_on_reflexive.
        exact reflexive_singleton_reflexive.
      * apply schema_Four_valid_on_transitive.
        exact reflexive_singleton_transitive.
    + apply McK_axiom_schema_valid_on_mckinsey.
      exact base_mck_reflexive_singleton_mckinsey.
Qed.

(** * K4McK proof combinators *)

Definition base_mck_switch (p : formula nat) : formula nat :=
  Imp (Dia p) (Box p).

(** Foundation first proves in pure K that McK is equivalent to the
    possibility of its switch formula.  We expose both directions as well
    as the packaged biconditional; the forward direction is the one used by
    the special-successor construction below. *)
Lemma normal_proves_base_mck_axiom_to_switch_possible :
  forall Ax (p : formula nat),
    normal_proves Ax (Imp (McK p) (Dia (base_mck_switch p))).
Proof.
  intros Ax p. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hmck.
  destruct (classic (satisfies F V w (Box (Dia p))))
    as [Hboxdia | Hnotboxdia].
  - destruct (@satisfies_dia_elim nat F V w (Box p) (Hmck Hboxdia))
      as [y [Rwy Hboxp]].
    apply satisfies_dia_intro. exists y; split; [exact Rwy |].
    unfold base_mck_switch. intros _. exact Hboxp.
  - apply satisfies_dia_intro. apply NNPP. intro Hnone.
    apply Hnotboxdia. intros y Rwy. apply NNPP. intro Hnotdia.
    apply Hnone. exists y; split; [exact Rwy |].
    unfold base_mck_switch. intro Hdia. exfalso. exact (Hnotdia Hdia).
Qed.

Lemma normal_proves_base_mck_switch_possible_to_axiom :
  forall Ax (p : formula nat),
    normal_proves Ax (Imp (Dia (base_mck_switch p)) (McK p)).
Proof.
  intros Ax p. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hswitch Hboxdia.
  destruct (satisfies_dia_elim Hswitch) as [y [Rwy HswitchY]].
  apply satisfies_dia_intro. exists y; split; [exact Rwy |].
  unfold base_mck_switch in HswitchY.
  exact (HswitchY (Hboxdia y Rwy)).
Qed.

Theorem normal_proves_base_mck_axiom_switch_iff :
  forall Ax (p : formula nat),
    normal_proves Ax (Iff (McK p) (Dia (base_mck_switch p))).
Proof.
  intros Ax p. apply normal_proves_iff_intro_modality.
  - apply normal_proves_base_mck_axiom_to_switch_possible.
  - apply normal_proves_base_mck_switch_possible_to_axiom.
Qed.

Lemma normal_proves_base_mck_switch_possible :
  forall Ax,
    schema_included McK_axiom_schema Ax ->
    forall p : formula nat,
      normal_proves Ax (Dia (base_mck_switch p)).
Proof.
  intros Ax HMcK p.
  eapply (Np_mp (p := McK p)).
  - apply normal_proves_base_mck_axiom_to_switch_possible.
  - apply Np_extra. apply HMcK. exists p. reflexivity.
Qed.

(** The two K-valid ways of commuting one possible and one necessary
    conjunct.  The following elimination corollaries match Foundation's
    theorem-level conveniences. *)
Lemma normal_proves_base_mck_dia_box_to_dia_and :
  forall Ax (p q : formula nat),
    normal_proves Ax
      (Imp (And (Dia p) (Box q)) (Dia (And p q))).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hand.
  destruct (proj1 (@satisfies_and nat F V w (Dia p) (Box q)) Hand)
    as [Hdiap Hboxq].
  destruct (satisfies_dia_elim Hdiap) as [y [Rwy Hpy]].
  apply satisfies_dia_intro. exists y; split; [exact Rwy |].
  apply (proj2 (@satisfies_and nat F V y p q)).
  split; [exact Hpy | now apply Hboxq].
Qed.

Lemma normal_proves_base_mck_dia_box_and_box_dia :
  forall Ax (p q : formula nat),
    normal_proves Ax
      (Imp (Dia (Box p))
        (Imp (Box (Dia q)) (Dia (And (Box p) (Dia q))))).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w HdiaBoxp HboxDiaq.
  destruct (satisfies_dia_elim HdiaBoxp) as [y [Rwy Hboxp]].
  apply satisfies_dia_intro. exists y; split; [exact Rwy |].
  apply (proj2 (@satisfies_and nat F V y (Box p) (Dia q))).
  split; [exact Hboxp | now apply HboxDiaq].
Qed.

Lemma normal_proves_base_mck_box_dia_to_dia_and :
  forall Ax (p q : formula nat),
    normal_proves Ax
      (Imp (And (Box p) (Dia q)) (Dia (And p q))).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hand.
  destruct (proj1 (@satisfies_and nat F V w (Box p) (Dia q)) Hand)
    as [Hboxp Hdiaq].
  destruct (satisfies_dia_elim Hdiaq) as [y [Rwy Hqy]].
  apply satisfies_dia_intro. exists y; split; [exact Rwy |].
  apply (proj2 (@satisfies_and nat F V y p q)).
  split; [now apply Hboxp | exact Hqy].
Qed.

Corollary normal_proves_base_mck_dia_box_elim :
  forall Ax (p q : formula nat),
    normal_proves Ax (And (Dia p) (Box q)) ->
    normal_proves Ax (Dia (And p q)).
Proof.
  intros Ax p q Hand. eapply Np_mp.
  - apply normal_proves_base_mck_dia_box_to_dia_and.
  - exact Hand.
Qed.

Corollary normal_proves_base_mck_box_dia_elim :
  forall Ax (p q : formula nat),
    normal_proves Ax (And (Box p) (Dia q)) ->
    normal_proves Ax (Dia (And p q)).
Proof.
  intros Ax p q Hand. eapply Np_mp.
  - apply normal_proves_base_mck_box_dia_to_dia_and.
  - exact Hand.
Qed.

Lemma normal_proves_base_mck_dia_collapse_of_Four :
  forall Ax,
    schema_included schema_Four Ax ->
    forall p : formula nat,
      normal_proves Ax (Imp (Dia (Dia p)) (Dia p)).
Proof.
  intros Ax HFour p.
  eapply (Np_mp (p := Four (Neg p))).
  - apply normal_proves_of_valid_on_all_frames.
    intros F V w Hfour Hdiadia.
    apply satisfies_dia_intro. apply NNPP. intro Hnone.
    assert (Hboxneg : satisfies F V w (Box (Neg p))).
    {
      intros y Rwy Hpy. apply Hnone. exists y; auto.
    }
    pose proof (Hfour Hboxneg) as Hboxboxneg.
    destruct (satisfies_dia_elim Hdiadia) as [y [Rwy Hdiay]].
    destruct (satisfies_dia_elim Hdiay) as [z [Ryz Hpz]].
    exact (Hboxboxneg y Rwy z Ryz Hpz).
  - apply Np_extra. apply HFour. exists (Neg p). reflexivity.
Qed.

(** Theoremwise possibilities can be combined in K4McK. *)
Lemma normal_proves_base_mck_jointly_possible :
  forall Ax,
    schema_included schema_Four Ax ->
    schema_included McK_axiom_schema Ax ->
    forall p q : formula nat,
      normal_proves Ax (Dia p) ->
      normal_proves Ax (Dia q) ->
      normal_proves Ax (Dia (And p q)).
Proof.
  intros Ax HFour HMcK p q Hp Hq.
  assert (HdiaBoxp : normal_proves Ax (Dia (Box p))).
  {
    eapply Np_mp.
    - apply Np_extra. apply HMcK. exists p. reflexivity.
    - now apply Np_nec.
  }
  assert (Houter : normal_proves Ax (Dia (And (Box p) (Dia q)))).
  {
    eapply Np_mp.
    - eapply Np_mp.
      + apply normal_proves_base_mck_dia_box_and_box_dia.
      + exact HdiaBoxp.
    - now apply Np_nec.
  }
  assert (HdiaDia : normal_proves Ax (Dia (Dia (And p q)))).
  {
    eapply Np_mp.
    - apply normal_proves_dia_regularity_modality.
      apply normal_proves_base_mck_box_dia_to_dia_and.
    - exact Houter.
  }
  eapply Np_mp.
  - now apply normal_proves_base_mck_dia_collapse_of_Four.
  - exact HdiaDia.
Qed.

(** The binary combination theorem iterates over every nonempty list.  The
    singleton case retains [logic_list_conj]'s trailing top, just as
    Foundation's [List.conj] does. *)
Lemma normal_proves_base_mck_nonempty_list_jointly_possible :
  forall Ax,
    schema_included schema_Four Ax ->
    schema_included McK_axiom_schema Ax ->
    forall Gamma : list (formula nat),
      Gamma <> nil ->
      (forall p, In p Gamma -> normal_proves Ax (Dia p)) ->
      normal_proves Ax (Dia (logic_list_conj Gamma)).
Proof.
  intros Ax HFour HMcK Gamma.
  induction Gamma as [|p Gamma IH]; intros Hnonempty Hall.
  - contradiction.
  - destruct Gamma as [|q Gamma].
    + change (normal_proves Ax (Dia (And p Top))).
      eapply Np_mp.
      * apply normal_proves_dia_regularity_modality.
        apply normal_proves_of_valid_on_all_frames.
        intros F V w Hp.
        apply (proj2 (@satisfies_and nat F V w p Top)).
        split; [exact Hp | apply satisfies_top].
      * apply Hall. now left.
    + change (normal_proves Ax
        (Dia (And p (logic_list_conj (q :: Gamma))))).
      apply normal_proves_base_mck_jointly_possible;
        [exact HFour | exact HMcK | |].
      * apply Hall. now left.
      * apply IH.
        -- discriminate.
        -- intros r Hr. apply Hall. now right.
Qed.

Definition base_mck_switch_conjunction (Gamma : list (formula nat))
    : formula nat :=
  logic_list_conj (map base_mck_switch Gamma).

Definition base_mck_switch_finset_conjunction
    (Gamma : list (formula nat)) : formula nat :=
  logic_list_conj2 (map base_mck_switch Gamma).

Lemma normal_proves_base_mck_switch_list_conjunction_possible :
  forall Ax,
    schema_included schema_Four Ax ->
    schema_included McK_axiom_schema Ax ->
    forall Gamma : list (formula nat),
      Gamma <> nil ->
      normal_proves Ax (Dia (base_mck_switch_conjunction Gamma)).
Proof.
  intros Ax HFour HMcK Gamma Hnonempty.
  unfold base_mck_switch_conjunction.
  apply normal_proves_base_mck_nonempty_list_jointly_possible;
    [exact HFour | exact HMcK | |].
  - intro Hmap. destruct Gamma as [|p Gamma].
    + contradiction.
    + discriminate.
  - intros q Hq. apply in_map_iff in Hq.
    destruct Hq as [p [<- _]].
    now apply normal_proves_base_mck_switch_possible.
Qed.

(** Lean's [Finset] is represented throughout this port by an extensional
    list.  Accordingly [image] is [map]; the conclusion holds for every
    enumeration, so order and repetitions do not affect the theorem. *)
Corollary normal_proves_base_mck_switch_finset_conjunction_possible :
  forall Ax,
    schema_included schema_Four Ax ->
    schema_included McK_axiom_schema Ax ->
    forall Gamma : list (formula nat),
      Gamma <> nil ->
      normal_proves Ax
        (Dia (base_mck_switch_finset_conjunction Gamma)).
Proof.
  intros Ax HFour HMcK Gamma Hnonempty.
  unfold base_mck_switch_finset_conjunction.
  eapply Np_mp.
  - apply normal_proves_dia_regularity_modality.
    apply (@logic_list_conj_to_conj2 nat (@normal_proves Ax nat)).
    constructor.
    + intros p Htaut. apply normal_proves_of_valid_on_all_frames.
      now apply classical_tautology_valid.
    + intros p q; apply Np_mp.
  - exact (normal_proves_base_mck_switch_list_conjunction_possible
      HFour HMcK Hnonempty).
Qed.

(** * The special canonical successor *)

Definition base_mck_seed_theory Ax
    (X : normal_maximal_consistent_theory Ax) : theory nat :=
  fun p => normal_mct_mem X (Box p) \/
    exists q : formula nat, p = base_mck_switch q.

(** Any finite derivation from the seed has one boxed source summary and one
    theoremwise-possible switch summary. *)
Lemma normal_derives_base_mck_seed_partition :
  forall Ax,
    schema_included schema_Four Ax ->
    schema_included McK_axiom_schema Ax ->
    forall (X : normal_maximal_consistent_theory Ax) r,
      normal_derives Ax (base_mck_seed_theory X) r ->
      exists a b,
        normal_mct_mem X (Box a) /\
        normal_proves Ax (Dia b) /\
        normal_proves Ax (Imp a (Imp b r)).
Proof.
  intros Ax HFour HMcK X r Hder.
  induction Hder as [r Hr | r Hr | p q Hpq IHpq Hp IHp].
  - destruct Hr as [Hr | [q ->]].
    + exists r, (base_mck_switch (@Top nat)). repeat split.
      * exact Hr.
      * now apply normal_proves_base_mck_switch_possible.
      * exact (Np_imply_K r (base_mck_switch (@Top nat))).
    + exists (@Top nat), (base_mck_switch q). repeat split.
      * apply normal_mct_box_top.
      * now apply normal_proves_base_mck_switch_possible.
      * apply normal_proves_imply_intro. apply normal_proves_identity.
  - exists (@Top nat), (base_mck_switch (@Top nat)). repeat split.
    + apply normal_mct_box_top.
    + now apply normal_proves_base_mck_switch_possible.
    + apply normal_proves_imply_intro.
      now apply normal_proves_imply_intro.
  - destruct IHpq as [a1 [b1 [Ha1 [Hb1 Himp1]]]].
    destruct IHp as [a2 [b2 [Ha2 [Hb2 Himp2]]]].
    exists (And a1 a2), (And b1 b2). repeat split.
    + now apply normal_mct_box_and.
    + now apply normal_proves_base_mck_jointly_possible.
    + eapply Np_mp.
      * eapply Np_mp.
        -- apply normal_proves_partition_mp.
        -- exact Himp1.
      * exact Himp2.
Qed.

Lemma base_mck_seed_theory_consistent :
  forall Ax,
    schema_included schema_Four Ax ->
    schema_included McK_axiom_schema Ax ->
    forall X : normal_maximal_consistent_theory Ax,
      normal_theory_consistent Ax (base_mck_seed_theory X).
Proof.
  intros Ax HFour HMcK X Hbottom.
  destruct (@normal_derives_base_mck_seed_partition
    Ax HFour HMcK X Bottom Hbottom)
    as [a [b [Hboxa [Hdiab Himp]]]].
  assert (Hboxnegb : normal_mct_mem X (Box (Neg b))).
  {
    apply normal_mct_derivable_mem. eapply ND_mp.
    - apply ND_theorem.
      exact (normal_proves_box_regularity_modality Himp).
    - apply ND_assumption. exact Hboxa.
  }
  assert (HdiabX : normal_mct_mem X (Dia b)).
  {
    apply normal_mct_derivable_mem. apply ND_theorem. exact Hdiab.
  }
  exact (@normal_mct_not_both Ax X (Box (Neg b)) Hboxnegb HdiabX).
Qed.

(** The generic canonical McKinsey theorem proved by Foundation. *)
Theorem normal_canonical_mckinsey_of_K4McK_schemas :
  forall Ax,
    schema_included schema_Four Ax ->
    schema_included McK_axiom_schema Ax ->
    frame_mckinsey (normal_canonical_frame Ax).
Proof.
  intros Ax HFour HMcK X.
  pose proof (@base_mck_seed_theory_consistent Ax HFour HMcK X)
    as Hconsistent.
  destruct (normal_lindenbaum_extension Hconsistent) as [Y Hinclude].
  assert (RXY : @normal_canonical_relation Ax X Y).
  {
    intros p Hboxp. apply Hinclude. now left.
  }
  assert (HswitchY : forall p,
    normal_mct_mem Y (base_mck_switch p)).
  {
    intro p. apply Hinclude. right. now exists p.
  }
  pose proof (@normal_canonical_transitive_of_schema_Four Ax HFour)
    as Htrans.
  destruct (classic (exists Z, @normal_canonical_relation Ax Y Z))
    as [[Z RYZ] | Hterminal].
  - exists Z; split.
    + exact (Htrans X Y Z RXY RYZ).
    + intros U RZU. apply NNPP. intro Hneq.
      destruct (@normal_mct_separator Ax Z U Hneq)
        as [p [HpZ HnegpU]].
      assert (HdiapY : normal_mct_mem Y (Dia p)).
      {
        now apply normal_canonical_predecessor_dia_mem with (N := Z).
      }
      assert (HboxpY : normal_mct_mem Y (Box p)).
      {
        apply normal_mct_derivable_mem. eapply ND_mp.
        - apply ND_assumption. exact (HswitchY p).
        - apply ND_assumption. exact HdiapY.
      }
      pose proof (Htrans Y Z U RYZ RZU p HboxpY) as HpU.
      exact (@normal_mct_not_both Ax U p HpU HnegpU).
  - exists Y; split; [exact RXY |].
    intros Z RYZ. exfalso. apply Hterminal. now exists Z.
Qed.

(** Source-facing form of the same result: any normal extension containing
    all K4McK instances has a McKinsey canonical frame. *)
Corollary normal_canonical_mckinsey_of_schema_K4McK :
  forall Ax,
    schema_included K4McK_schema Ax ->
    frame_mckinsey (normal_canonical_frame Ax).
Proof.
  intros Ax HK4McK.
  apply normal_canonical_mckinsey_of_K4McK_schemas.
  - intros A p Hp. apply HK4McK. now left.
  - intros A p Hp. apply HK4McK. now right.
Qed.

(** * Canonicality and completeness *)

Lemma K4McK_canonical_frame :
  K4McK_frame_class (normal_canonical_frame K4McK_schema).
Proof.
  split.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. now left.
  - apply normal_canonical_mckinsey_of_K4McK_schemas.
    + intros A p Hp. now left.
    + intros A p Hp. now right.
Qed.

Lemma S4McK_canonical_frame :
  S4McK_frame_class (normal_canonical_frame S4McK_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    intros A p Hp. left. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. left. now right.
  - apply normal_canonical_mckinsey_of_K4McK_schemas.
    + intros A p Hp. left. now right.
    + intros A p Hp. now right.
Qed.

Theorem K4McK_complete :
  forall p : formula nat,
    normal_valid_on_class K4McK_frame_class p -> K4McK_proves p.
Proof.
  unfold K4McK_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := K4McK_schema) (C := K4McK_frame_class)).
  - exact (@K4McK_is_consistent nat).
  - exact K4McK_canonical_frame.
Qed.

Theorem S4McK_complete :
  forall p : formula nat,
    normal_valid_on_class S4McK_frame_class p -> S4McK_proves p.
Proof.
  unfold S4McK_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4McK_schema) (C := S4McK_frame_class)).
  - exact (@S4McK_is_consistent nat).
  - exact S4McK_canonical_frame.
Qed.

Theorem K4McK_sound_complete :
  forall p : formula nat,
    K4McK_proves p <-> normal_valid_on_class K4McK_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HT HM]. now apply K4McK_proves_sound_on_frame.
  - apply K4McK_complete.
Qed.

Theorem S4McK_sound_complete :
  forall p : formula nat,
    S4McK_proves p <-> normal_valid_on_class S4McK_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HR [HT HM]]. now apply S4McK_proves_sound_on_frame.
  - apply S4McK_complete.
Qed.

(** * Logic inclusions *)

Lemma K_weaker_than_K4McK :
  forall (AtomType : Type) (p : formula AtomType),
    K_normal_proves p -> K4McK_proves p.
Proof. intros AtomType p Hp. now apply K_weaker_than_normal. Qed.

Lemma K4_weaker_than_K4McK :
  forall (AtomType : Type) (p : formula AtomType),
    K4_proves p -> K4McK_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q Hq. now left.
Qed.

Lemma S4_weaker_than_S4McK :
  forall (AtomType : Type) (p : formula AtomType),
    S4_proves p -> S4McK_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q Hq. now left.
Qed.

Lemma K4McK_weaker_than_S4McK :
  forall (AtomType : Type) (p : formula AtomType),
    K4McK_proves p -> S4McK_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q [HFour | HMcK].
  - left. now right.
  - now right.
Qed.

(** * Explicit strictness witnesses *)

Theorem K4_strictly_weaker_K4McK :
  normal_strictly_weaker K4_proves K4McK_proves.
Proof.
  split.
  - intros p Hp. now apply K4_weaker_than_K4McK.
  - exists (McK (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HK4.
      pose proof (K4_proves_sound_on_transitive_frame
        irreflexive_singleton_transitive HK4) as Hvalid.
      specialize (Hvalid (fun _ _ => False) tt).
      assert (Hboxdia : satisfies irreflexive_singleton_frame
        (fun _ _ => False) tt (Box (Dia (Atom 0)))).
      { intros y Rty. contradiction. }
      destruct (@satisfies_dia_elim nat irreflexive_singleton_frame
        (fun _ _ => False) tt (Box (Atom 0)) (Hvalid Hboxdia))
        as [y [Rty _]].
      contradiction.
Qed.

Definition base_mck_universal_two_frame : frame :=
  {| World := bool; Rel := fun _ _ => True |}.

Lemma base_mck_universal_two_reflexive :
  frame_reflexive base_mck_universal_two_frame.
Proof. intros []; constructor. Qed.

Lemma base_mck_universal_two_transitive :
  frame_transitive base_mck_universal_two_frame.
Proof. intros [] [] [] _ _; constructor. Qed.

Theorem S4_strictly_weaker_S4McK :
  normal_strictly_weaker S4_proves S4McK_proves.
Proof.
  split.
  - intros p Hp. now apply S4_weaker_than_S4McK.
  - exists (McK (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HS4.
      pose proof (S4_proves_sound_on_preorder_frame
        base_mck_universal_two_reflexive
        base_mck_universal_two_transitive HS4) as Hvalid.
      specialize (Hvalid (fun _ w => w = false) false).
      assert (Hboxdia : satisfies base_mck_universal_two_frame
        (fun _ w => w = false) false (Box (Dia (Atom 0)))).
      {
        intros y _. apply satisfies_dia_intro.
        exists false; split; [constructor | reflexivity].
      }
      destruct (@satisfies_dia_elim nat base_mck_universal_two_frame
        (fun _ w => w = false) false (Box (Atom 0)) (Hvalid Hboxdia))
        as [y [_ Hbox]].
      specialize (Hbox true ltac:(constructor)). discriminate.
Qed.

Definition base_mck_terminal_two_frame : frame :=
  {| World := bool; Rel := fun _ y => y = true |}.

Lemma base_mck_terminal_two_transitive :
  frame_transitive base_mck_terminal_two_frame.
Proof. intros x y z _ Hyz. exact Hyz. Qed.

Lemma base_mck_terminal_two_mckinsey :
  frame_mckinsey base_mck_terminal_two_frame.
Proof.
  intro x. exists true; split.
  - reflexivity.
  - intros z Hz. symmetry. exact Hz.
Qed.

Theorem K4McK_strictly_weaker_S4McK :
  normal_strictly_weaker K4McK_proves S4McK_proves.
Proof.
  split.
  - intros p Hp. now apply K4McK_weaker_than_S4McK.
  - exists (T (Atom 0)); split.
    + apply Np_extra. left. left. exists (Atom 0). reflexivity.
    + intro HK4McK.
      pose proof (K4McK_proves_sound_on_frame
        base_mck_terminal_two_transitive
        base_mck_terminal_two_mckinsey HK4McK) as Hvalid.
      specialize (Hvalid (fun _ w => w = true) false).
      assert (Hbox : satisfies base_mck_terminal_two_frame
        (fun _ w => w = true) false (Box (Atom 0))).
      { intros y Hy. exact Hy. }
      pose proof (Hvalid Hbox) as Hbad. discriminate.
Qed.
