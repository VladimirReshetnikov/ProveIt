(**
  The raw Dum, Dum.2, and Dum.3 systems from Foundation's Normal catalogue.

  This file independently ports the exact thirty-nine active commands at
  lines 789--845 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Every raw predicate retains modal K at
  the distinct atoms 0 and 1, with T, Four, and Dum at atom 0.  The point
  systems additionally retain Point2 at atom 0 or Point3 at the distinct
  atoms 0 and 1.  Raw templates enter [normal_hilbert_proves] only through
  same-atom endosubstitution.

  Literal and target-provable source inclusions keep their exact boundaries.
  In particular, the Grz targets derive T, Four, and Dum directly from their
  structural K and Grz capabilities.  The only substantial step is the
  standard pure-K Grz seed used to obtain Four; all support lemmas are Local.
  No semantic theorem, completeness result, classical metaprinciple, choice
  principle, or admission is used.  Every repeated inferred source instance
  is represented by a separately named alias.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertNormal
  HilbertWithRE HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems HilbertNormalTransitiveBaseSystems
  HilbertNormalS4Systems HilbertNormalS4PointSystems
  HilbertNormalHenkinGrzSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_dum_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_dum_S4 : structural_s4_entailment L0;
  structural_dum_Dum : has_Dum L0
}.

Record structural_dumpoint2_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_dumpoint2_Dum : structural_dum_entailment L0;
  structural_dumpoint2_Point2 : has_Point2 L0
}.

Record structural_dumpoint3_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_dumpoint3_Dum : structural_dum_entailment L0;
  structural_dumpoint3_Point3 : has_Point3 L0
}.

(** * Closed syntactic Grz consequences *)

(** Conjunction is the classical encoding [not (p -> not q)].  These
    constructor and projection theorems use only contextual deduction and
    the checked Lukasiewicz basis of K. *)
Local Lemma K_proves_and_intro_imp :
  forall (p q : formula nat),
    K_proves (Imp p (Imp q (And p q))).
Proof.
  intros p q.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp p (Imp q (And p q))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  unfold And, Neg.
  apply K_derives_deduction.
  eapply Kd_mp.
  - eapply Kd_mp.
    + apply Kd_assumption. left; reflexivity.
    + apply Kd_assumption. right; right; left; reflexivity.
  - apply Kd_assumption. right; left; reflexivity.
Qed.

Local Lemma K_proves_and_elim_left_imp :
  forall (p q : formula nat),
    K_proves (Imp (And p q) p).
Proof.
  intros p q.
  apply (proj1 (@K_derives_empty_iff nat (Imp (And p q) p))).
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_theorem. apply K_proves_dne.
  - unfold Neg.
    apply K_derives_deduction.
    eapply Kd_mp.
    + apply Kd_assumption. right; left; reflexivity.
    + apply K_derives_deduction.
      apply K_derives_deduction.
      eapply Kd_mp.
      * apply Kd_assumption. right; right; left; reflexivity.
      * apply Kd_assumption. right; left; reflexivity.
Qed.

Local Lemma K_proves_and_elim_right_imp :
  forall (p q : formula nat),
    K_proves (Imp (And p q) q).
Proof.
  intros p q.
  apply (proj1 (@K_derives_empty_iff nat (Imp (And p q) q))).
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_theorem. apply K_proves_dne.
  - unfold Neg.
    apply K_derives_deduction.
    eapply Kd_mp.
    + apply Kd_assumption. right; left; reflexivity.
    + apply K_derives_deduction.
      apply K_derives_deduction.
      eapply Kd_mp.
      * apply Kd_assumption. right; right; left; reflexivity.
      * apply Kd_assumption. left; reflexivity.
Qed.

(** Peirce's law, needed only for the pure-K Grz seed. *)
Local Lemma K_proves_peirce :
  forall (p q : formula nat),
    K_proves (Imp (Imp (Imp p q) p) p).
Proof.
  intros p q.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp (Imp (Imp p q) p) p))).
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_theorem. apply K_proves_dne.
  - unfold Neg.
    apply K_derives_deduction.
    eapply Kd_mp.
    + apply Kd_assumption. left; reflexivity.
    + eapply Kd_mp.
      * apply Kd_assumption. right; left; reflexivity.
      * apply K_derives_deduction.
        apply K_derives_ex_falso.
        eapply Kd_mp.
        -- apply Kd_assumption. right; left; reflexivity.
        -- apply Kd_assumption. left; reflexivity.
Qed.

(** Foundation [lemma_Grz_1].  For
      [seed = p /\ (Box p -> Box Box p)],
    this pure-K theorem prepares the antecedent of the Grz instance at
    [seed]. *)
Local Lemma K_proves_Grz_seed :
  forall p : formula nat,
    let seed := And p (Imp (Box p) (Box (Box p))) in
    K_proves
      (Imp (Box p)
        (Box (Imp (Box (Imp seed (Box seed))) seed))).
Proof.
  intro p.
  set (seed := And p (Imp (Box p) (Box (Box p)))).
  assert (Hd1 :
    K_proves (Imp (Imp seed (Box p)) (Imp p (Box p)))).
  {
    apply (proj1 (@K_derives_empty_iff nat
      (Imp (Imp seed (Box p)) (Imp p (Box p))))).
    apply K_derives_deduction.
    apply K_derives_deduction.
    eapply Kd_mp.
    - apply Kd_theorem. apply K_proves_peirce.
    - apply K_derives_deduction.
      eapply Kd_mp.
      + apply Kd_assumption. right; right; left; reflexivity.
      + eapply Kd_mp.
        * eapply Kd_mp.
          -- apply Kd_theorem. apply K_proves_and_intro_imp.
          -- apply Kd_assumption. right; left; reflexivity.
        * apply Kd_assumption. left; reflexivity.
  }
  assert (Hseed_to_p : K_proves (Imp seed p)).
  {
    unfold seed.
    apply K_proves_and_elim_left_imp.
  }
  assert (Hboxseed_to_boxp :
    K_proves (Imp (Box seed) (Box p))).
  { exact (K_proves_box_regularity Hseed_to_p). }
  assert (Hd2 :
    K_proves
      (Imp (Imp seed (Box seed)) (Imp seed (Box p)))).
  {
    apply (proj1 (@K_derives_empty_iff nat
      (Imp (Imp seed (Box seed)) (Imp seed (Box p))))).
    apply K_derives_deduction.
    apply K_derives_deduction.
    eapply Kd_mp.
    - apply Kd_theorem. exact Hboxseed_to_boxp.
    - eapply Kd_mp.
      + apply Kd_assumption. right; left; reflexivity.
      + apply Kd_assumption. left; reflexivity.
  }
  assert (Hstep :
    K_proves
      (Imp (Imp seed (Box seed)) (Imp p (Box p)))).
  { exact (K_proves_imp_trans Hd2 Hd1). }
  assert (Hboxed_step :
    K_proves
      (Imp (Box (Imp seed (Box seed)))
        (Box (Imp p (Box p))))).
  { exact (K_proves_box_regularity Hstep). }
  assert (Hfour_component :
    K_proves
      (Imp (Box (Imp seed (Box seed)))
        (Imp (Box p) (Box (Box p))))).
  { exact (K_proves_imp_trans Hboxed_step (Kp_modal_K p (Box p))). }
  assert (Hunboxed :
    K_proves
      (Imp p
        (Imp (Box (Imp seed (Box seed))) seed))).
  {
    apply (proj1 (@K_derives_empty_iff nat
      (Imp p (Imp (Box (Imp seed (Box seed))) seed)))).
    apply K_derives_deduction.
    apply K_derives_deduction.
    unfold seed.
    eapply Kd_mp.
    - eapply Kd_mp.
      + apply Kd_theorem. apply K_proves_and_intro_imp.
      + apply Kd_assumption. right; left; reflexivity.
    - eapply Kd_mp.
      + apply Kd_theorem. exact Hfour_component.
      + apply Kd_assumption. left; reflexivity.
  }
  exact (K_proves_box_regularity Hunboxed).
Qed.

(** Every source-facing structural K fragment contains the closed K
    calculus. *)
Local Lemma structural_K_contains_K_proves :
  forall (L0 : modal_logic_set nat),
    structural_k_entailment L0 ->
    logic_subset (@K_proves nat) L0.
Proof.
  intros L0 HK p Hp; induction Hp.
  - exact (lukasiewicz_imply_K
      (structural_k_lukasiewicz HK) p q).
  - exact (lukasiewicz_imply_S
      (structural_k_lukasiewicz HK) p q r).
  - exact (lukasiewicz_elim_contra
      (structural_k_lukasiewicz HK) p q).
  - exact (has_K_axiom (structural_k_K HK) p q).
  - exact (lukasiewicz_mp
      (structural_k_lukasiewicz HK) IHHp1 IHHp2).
  - exact (structural_k_necessitation HK IHHp).
Qed.

Local Lemma structural_K_imp_trans :
  forall (L0 : modal_logic_set nat),
    structural_k_entailment L0 ->
    forall p q r,
      L0 (Imp p q) -> L0 (Imp q r) -> L0 (Imp p r).
Proof.
  intros L0 HK p q r Hpq Hqr.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  eapply lukasiewicz_mp; [exact HLuk | | exact Hpq].
  eapply lukasiewicz_mp; [exact HLuk | |].
  - exact (lukasiewicz_imply_S HLuk p q r).
  - eapply lukasiewicz_mp; [exact HLuk | | exact Hqr].
    exact (lukasiewicz_imply_K HLuk (Imp q r) p).
Qed.

Local Lemma structural_K_under_mp :
  forall (L0 : modal_logic_set nat),
    structural_k_entailment L0 ->
    forall a p q,
      L0 (Imp a (Imp p q)) -> L0 (Imp a p) -> L0 (Imp a q).
Proof.
  intros L0 HK a p q Hpq Hp.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  eapply lukasiewicz_mp; [exact HLuk | | exact Hp].
  eapply lukasiewicz_mp; [exact HLuk | | exact Hpq].
  exact (lukasiewicz_imply_S HLuk a p q).
Qed.

Local Lemma structural_Grz_T_and_Four :
  forall (L0 : modal_logic_set nat),
    structural_grz_entailment L0 ->
    forall p,
      L0 (Imp (Box p)
        (And p (Imp (Box p) (Box (Box p))))).
Proof.
  intros L0 HGrz p.
  set (seed := And p (Imp (Box p) (Box (Box p)))).
  pose proof (structural_grz_K HGrz) as HK.
  assert (Hseed :
    L0 (Imp (Box p)
      (Box (Imp (Box (Imp seed (Box seed))) seed)))).
  {
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_Grz_seed.
  }
  assert (Hgrz :
    L0 (Imp (Box (Imp (Box (Imp seed (Box seed))) seed)) seed)).
  {
    change (L0 (Grz seed)).
    exact (has_Grz_axiom (structural_grz_Grz HGrz) seed).
  }
  change (L0 (Imp (Box p) seed)).
  exact (structural_K_imp_trans HK Hseed Hgrz).
Qed.

Local Lemma structural_Grz_has_T :
  forall (L0 : modal_logic_set nat),
    structural_grz_entailment L0 -> has_T L0.
Proof.
  intros L0 HGrz; constructor; intro p.
  pose proof (structural_grz_K HGrz) as HK.
  pose proof (structural_Grz_T_and_Four HGrz p) as Hboth.
  assert (Hproject :
    L0 (Imp (And p (Imp (Box p) (Box (Box p)))) p)).
  {
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_and_elim_left_imp.
  }
  unfold T.
  exact (structural_K_imp_trans HK Hboth Hproject).
Qed.

Local Lemma structural_Grz_has_Four :
  forall (L0 : modal_logic_set nat),
    structural_grz_entailment L0 -> has_Four L0.
Proof.
  intros L0 HGrz; constructor; intro p.
  pose proof (structural_grz_K HGrz) as HK.
  pose proof (structural_Grz_T_and_Four HGrz p) as Hboth.
  assert (Hproject :
    L0 (Imp (And p (Imp (Box p) (Box (Box p))))
      (Imp (Box p) (Box (Box p))))).
  {
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_and_elim_right_imp.
  }
  unfold Four.
  pose proof (structural_K_imp_trans HK Hboth Hproject) as Hnested.
  apply (structural_K_under_mp HK Hnested).
  apply (structural_K_contains_K_proves (L0 := L0) HK).
  apply K_proves_identity.
Qed.

Local Lemma structural_Grz_has_Dum :
  forall (L0 : modal_logic_set nat),
    structural_grz_entailment L0 -> has_Dum L0.
Proof.
  intros L0 HGrz; constructor; intro p.
  pose proof (structural_grz_K HGrz) as HK.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  pose proof (has_Grz_axiom (structural_grz_Grz HGrz) p) as Hgrz.
  unfold Grz in Hgrz. unfold Dum.
  eapply structural_K_imp_trans; [exact HK | exact Hgrz |].
  exact (lukasiewicz_imply_K HLuk p (Dia (Box p))).
Qed.

(** * Dum: eleven active source commands *)

(** Source declaration 1/39: [Dum.axioms]. *)
Definition normal_Dum_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = Dum (Atom 0).

(** Source declaration 2/39: [Dum.axioms.HasK]. *)
Definition normal_Dum_axioms_has_K :
  raw_axioms_has_K normal_Dum_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/39: [Dum.axioms.HasT]. *)
Definition normal_Dum_axioms_has_T :
  raw_axioms_has_T normal_Dum_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/39: [Dum.axioms.HasFour]. *)
Definition normal_Dum_axioms_has_Four :
  raw_axioms_has_Four normal_Dum_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 5/39: [Dum.axioms.HasDum]. *)
Definition normal_Dum_axioms_has_Dum :
  raw_axioms_has_Dum normal_Dum_axioms.
Proof.
  refine {| raw_Dum_p := 0;
            raw_Dum_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 6/39: the named logic [Dum]. *)
Definition normal_Dum : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_Dum_axioms.

(** Source declaration 7/39: [Entailment.Dum Modal.Dum]. *)
Lemma normal_Dum_entailment :
  structural_dum_entailment normal_Dum.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- apply normal_hilbert_lukasiewicz.
        -- exact (@normal_hilbert_has_K nat normal_Dum_axioms Nat.eq_dec
            normal_Dum_axioms_has_K).
        -- apply normal_hilbert_has_DiaDuality.
        -- apply normal_hilbert_necessitation.
      * exact (@normal_hilbert_has_Four nat normal_Dum_axioms Nat.eq_dec
          normal_Dum_axioms_has_Four).
    + exact (@normal_hilbert_has_T nat normal_Dum_axioms Nat.eq_dec
        normal_Dum_axioms_has_T).
  - exact (@normal_hilbert_has_Dum nat normal_Dum_axioms Nat.eq_dec
      normal_Dum_axioms_has_Dum).
Qed.

(** Source declaration 8/39: [Modal.S4 <= Modal.Dum], through
    target-provable axioms. *)
Lemma normal_S4_weaker_than_normal_Dum :
  logic_subset normal_S4 normal_Dum.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_S4_axioms in Hax.
  pose proof (structural_dum_S4 normal_Dum_entailment) as HS4.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_k4_K (structural_s4_K4 HS4)))
      (Atom 0) (Atom 1)).
  - exact (has_T_axiom (structural_s4_T HS4) (Atom 0)).
  - exact (has_Four_axiom
      (structural_k4_Four (structural_s4_K4 HS4)) (Atom 0)).
Qed.

(** Source declaration 9/39: the duplicate inferred
    [Modal.S4 <= Modal.Dum] instance. *)
Definition normal_S4_weaker_than_normal_Dum_duplicate :
  logic_subset normal_S4 normal_Dum :=
  normal_S4_weaker_than_normal_Dum.

(** Source declaration 10/39: [Modal.Dum <= Modal.Grz], through
    target-provable axioms. *)
Lemma normal_Dum_weaker_than_normal_Grz :
  logic_subset normal_Dum normal_Grz.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_Dum_axioms in Hax.
  destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_grz_K normal_Grz_entailment))
      (Atom 0) (Atom 1)).
  - exact (has_T_axiom
      (structural_Grz_has_T normal_Grz_entailment) (Atom 0)).
  - exact (has_Four_axiom
      (structural_Grz_has_Four normal_Grz_entailment) (Atom 0)).
  - exact (has_Dum_axiom
      (structural_Grz_has_Dum normal_Grz_entailment) (Atom 0)).
Qed.

(** Source declaration 11/39: the duplicate inferred
    [Modal.Dum <= Modal.Grz] instance. *)
Definition normal_Dum_weaker_than_normal_Grz_duplicate :
  logic_subset normal_Dum normal_Grz :=
  normal_Dum_weaker_than_normal_Grz.

(** * DumPoint2: fourteen active source commands *)

(** Source declaration 12/39: [DumPoint2.axioms]. *)
Definition normal_DumPoint2_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = Dum (Atom 0) \/
    p = Point2 (Atom 0).

(** Source declaration 13/39: [DumPoint2.axioms.HasK]. *)
Definition normal_DumPoint2_axioms_has_K :
  raw_axioms_has_K normal_DumPoint2_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 14/39: [DumPoint2.axioms.HasT]. *)
Definition normal_DumPoint2_axioms_has_T :
  raw_axioms_has_T normal_DumPoint2_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 15/39: [DumPoint2.axioms.HasFour]. *)
Definition normal_DumPoint2_axioms_has_Four :
  raw_axioms_has_Four normal_DumPoint2_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 16/39: [DumPoint2.axioms.HasDum]. *)
Definition normal_DumPoint2_axioms_has_Dum :
  raw_axioms_has_Dum normal_DumPoint2_axioms.
Proof.
  refine {| raw_Dum_p := 0;
            raw_Dum_mem := _ |}.
  right; right; right; left; reflexivity.
Defined.

(** Source declaration 17/39: [DumPoint2.axioms.HasPoint2]. *)
Definition normal_DumPoint2_axioms_has_Point2 :
  raw_axioms_has_Point2 normal_DumPoint2_axioms.
Proof.
  refine {| raw_Point2_p := 0;
            raw_Point2_mem := _ |}.
  right; right; right; right; reflexivity.
Defined.

(** Source declaration 18/39: the named logic [DumPoint2]. *)
Definition normal_DumPoint2 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_DumPoint2_axioms.

(** Source declaration 19/39:
    [Entailment.DumPoint2 Modal.DumPoint2]. *)
Lemma normal_DumPoint2_entailment :
  structural_dumpoint2_entailment normal_DumPoint2.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- constructor.
           ++ apply normal_hilbert_lukasiewicz.
           ++ exact (@normal_hilbert_has_K nat normal_DumPoint2_axioms
                Nat.eq_dec normal_DumPoint2_axioms_has_K).
           ++ apply normal_hilbert_has_DiaDuality.
           ++ apply normal_hilbert_necessitation.
        -- exact (@normal_hilbert_has_Four nat normal_DumPoint2_axioms
             Nat.eq_dec normal_DumPoint2_axioms_has_Four).
      * exact (@normal_hilbert_has_T nat normal_DumPoint2_axioms
          Nat.eq_dec normal_DumPoint2_axioms_has_T).
    + exact (@normal_hilbert_has_Dum nat normal_DumPoint2_axioms
        Nat.eq_dec normal_DumPoint2_axioms_has_Dum).
  - exact (@normal_hilbert_has_Point2 nat normal_DumPoint2_axioms
      Nat.eq_dec normal_DumPoint2_axioms_has_Point2).
Qed.

(** Source declaration 20/39: [Modal.Dum <= Modal.DumPoint2], by literal
    raw-axiom inclusion. *)
Lemma normal_Dum_weaker_than_normal_DumPoint2 :
  logic_subset normal_Dum normal_DumPoint2.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_Dum_axioms in Hax.
  unfold normal_DumPoint2_axioms.
  destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
  - right; right; right; left; reflexivity.
Qed.

(** Source declaration 21/39: the duplicate inferred
    [Modal.Dum <= Modal.DumPoint2] instance. *)
Definition normal_Dum_weaker_than_normal_DumPoint2_duplicate :
  logic_subset normal_Dum normal_DumPoint2 :=
  normal_Dum_weaker_than_normal_DumPoint2.

(** Source declaration 22/39: [Modal.S4Point2 <= Modal.DumPoint2], by
    literal raw-axiom inclusion. *)
Lemma normal_S4Point2_weaker_than_normal_DumPoint2 :
  logic_subset normal_S4Point2 normal_DumPoint2.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_S4Point2_axioms in Hax.
  unfold normal_DumPoint2_axioms.
  destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
  - right; right; right; right; reflexivity.
Qed.

(** Source declaration 23/39: the duplicate inferred
    [Modal.S4Point2 <= Modal.DumPoint2] instance. *)
Definition normal_S4Point2_weaker_than_normal_DumPoint2_duplicate :
  logic_subset normal_S4Point2 normal_DumPoint2 :=
  normal_S4Point2_weaker_than_normal_DumPoint2.

(** Source declaration 24/39:
    [Modal.DumPoint2 <= Modal.GrzPoint2], through target-provable axioms. *)
Lemma normal_DumPoint2_weaker_than_normal_GrzPoint2 :
  logic_subset normal_DumPoint2 normal_GrzPoint2.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_DumPoint2_axioms in Hax.
  pose proof
    (structural_grzpoint2_Grz normal_GrzPoint2_entailment) as HGrz.
  destruct Hax as [Hax | [Hax | [Hax | [Hax | Hax]]]]; subst p.
  - exact (has_K_axiom (structural_k_K (structural_grz_K HGrz))
      (Atom 0) (Atom 1)).
  - exact (has_T_axiom (structural_Grz_has_T HGrz) (Atom 0)).
  - exact (has_Four_axiom (structural_Grz_has_Four HGrz) (Atom 0)).
  - exact (has_Dum_axiom (structural_Grz_has_Dum HGrz) (Atom 0)).
  - exact (has_Point2_axiom
      (structural_grzpoint2_Point2 normal_GrzPoint2_entailment)
      (Atom 0)).
Qed.

(** Source declaration 25/39: the duplicate inferred
    [Modal.DumPoint2 <= Modal.GrzPoint2] instance. *)
Definition normal_DumPoint2_weaker_than_normal_GrzPoint2_duplicate :
  logic_subset normal_DumPoint2 normal_GrzPoint2 :=
  normal_DumPoint2_weaker_than_normal_GrzPoint2.

(** * DumPoint3: fourteen active source commands *)

(** Source declaration 26/39: [DumPoint3.axioms]. *)
Definition normal_DumPoint3_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = Dum (Atom 0) \/
    p = Point3 (Atom 0) (Atom 1).

(** Source declaration 27/39: [DumPoint3.axioms.HasK]. *)
Definition normal_DumPoint3_axioms_has_K :
  raw_axioms_has_K normal_DumPoint3_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 28/39: [DumPoint3.axioms.HasT]. *)
Definition normal_DumPoint3_axioms_has_T :
  raw_axioms_has_T normal_DumPoint3_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 29/39: [DumPoint3.axioms.HasFour]. *)
Definition normal_DumPoint3_axioms_has_Four :
  raw_axioms_has_Four normal_DumPoint3_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 30/39: [DumPoint3.axioms.HasDum]. *)
Definition normal_DumPoint3_axioms_has_Dum :
  raw_axioms_has_Dum normal_DumPoint3_axioms.
Proof.
  refine {| raw_Dum_p := 0;
            raw_Dum_mem := _ |}.
  right; right; right; left; reflexivity.
Defined.

(** Source declaration 31/39: [DumPoint3.axioms.HasPoint3]. *)
Definition normal_DumPoint3_axioms_has_Point3 :
  raw_axioms_has_Point3 normal_DumPoint3_axioms.
Proof.
  refine {| raw_Point3_p := 0;
            raw_Point3_q := 1;
            raw_Point3_ne := _;
            raw_Point3_mem := _ |}.
  - discriminate.
  - right; right; right; right; reflexivity.
Defined.

(** Source declaration 32/39: the named logic [DumPoint3]. *)
Definition normal_DumPoint3 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_DumPoint3_axioms.

(** Source declaration 33/39:
    [Entailment.DumPoint3 Modal.DumPoint3]. *)
Lemma normal_DumPoint3_entailment :
  structural_dumpoint3_entailment normal_DumPoint3.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- constructor.
           ++ apply normal_hilbert_lukasiewicz.
           ++ exact (@normal_hilbert_has_K nat normal_DumPoint3_axioms
                Nat.eq_dec normal_DumPoint3_axioms_has_K).
           ++ apply normal_hilbert_has_DiaDuality.
           ++ apply normal_hilbert_necessitation.
        -- exact (@normal_hilbert_has_Four nat normal_DumPoint3_axioms
             Nat.eq_dec normal_DumPoint3_axioms_has_Four).
      * exact (@normal_hilbert_has_T nat normal_DumPoint3_axioms
          Nat.eq_dec normal_DumPoint3_axioms_has_T).
    + exact (@normal_hilbert_has_Dum nat normal_DumPoint3_axioms
        Nat.eq_dec normal_DumPoint3_axioms_has_Dum).
  - exact (@normal_hilbert_has_Point3 nat normal_DumPoint3_axioms
      Nat.eq_dec normal_DumPoint3_axioms_has_Point3).
Qed.

(** Source declaration 34/39: [Modal.Dum <= Modal.DumPoint3], by literal
    raw-axiom inclusion. *)
Lemma normal_Dum_weaker_than_normal_DumPoint3 :
  logic_subset normal_Dum normal_DumPoint3.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_Dum_axioms in Hax.
  unfold normal_DumPoint3_axioms.
  destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
  - right; right; right; left; reflexivity.
Qed.

(** Source declaration 35/39: the duplicate inferred
    [Modal.Dum <= Modal.DumPoint3] instance. *)
Definition normal_Dum_weaker_than_normal_DumPoint3_duplicate :
  logic_subset normal_Dum normal_DumPoint3 :=
  normal_Dum_weaker_than_normal_DumPoint3.

(** Source declaration 36/39: [Modal.S4Point3 <= Modal.DumPoint3], through
    target-provable axioms exactly as in the source. *)
Lemma normal_S4Point3_weaker_than_normal_DumPoint3 :
  logic_subset normal_S4Point3 normal_DumPoint3.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_S4Point3_axioms in Hax.
  pose proof
    (structural_dumpoint3_Dum normal_DumPoint3_entailment) as HDum.
  pose proof (structural_dum_S4 HDum) as HS4.
  destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_k4_K (structural_s4_K4 HS4)))
      (Atom 0) (Atom 1)).
  - exact (has_T_axiom (structural_s4_T HS4) (Atom 0)).
  - exact (has_Four_axiom
      (structural_k4_Four (structural_s4_K4 HS4)) (Atom 0)).
  - exact (has_Point3_axiom
      (structural_dumpoint3_Point3 normal_DumPoint3_entailment)
      (Atom 0) (Atom 1)).
Qed.

(** Source declaration 37/39: the duplicate inferred
    [Modal.S4Point3 <= Modal.DumPoint3] instance. *)
Definition normal_S4Point3_weaker_than_normal_DumPoint3_duplicate :
  logic_subset normal_S4Point3 normal_DumPoint3 :=
  normal_S4Point3_weaker_than_normal_DumPoint3.

(** Source declaration 38/39:
    [Modal.DumPoint3 <= Modal.GrzPoint3], through target-provable axioms. *)
Lemma normal_DumPoint3_weaker_than_normal_GrzPoint3 :
  logic_subset normal_DumPoint3 normal_GrzPoint3.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_DumPoint3_axioms in Hax.
  pose proof
    (structural_grzpoint3_Grz normal_GrzPoint3_entailment) as HGrz.
  destruct Hax as [Hax | [Hax | [Hax | [Hax | Hax]]]]; subst p.
  - exact (has_K_axiom (structural_k_K (structural_grz_K HGrz))
      (Atom 0) (Atom 1)).
  - exact (has_T_axiom (structural_Grz_has_T HGrz) (Atom 0)).
  - exact (has_Four_axiom (structural_Grz_has_Four HGrz) (Atom 0)).
  - exact (has_Dum_axiom (structural_Grz_has_Dum HGrz) (Atom 0)).
  - exact (has_Point3_axiom
      (structural_grzpoint3_Point3 normal_GrzPoint3_entailment)
      (Atom 0) (Atom 1)).
Qed.

(** Source declaration 39/39: the duplicate inferred
    [Modal.DumPoint3 <= Modal.GrzPoint3] instance. *)
Definition normal_DumPoint3_weaker_than_normal_GrzPoint3_duplicate :
  logic_subset normal_DumPoint3 normal_GrzPoint3 :=
  normal_DumPoint3_weaker_than_normal_GrzPoint3.
