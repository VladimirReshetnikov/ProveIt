(**
  The raw K4Z, K4Point2Z, and K4Point3Z systems from Foundation's Normal
  catalogue.

  This file independently ports the exact thirty-six active commands at
  lines 685--738 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Every raw predicate retains modal K at
  the distinct atoms 0 and 1, together with Four and Z at atom 0.  The two
  point systems additionally retain WeakPoint2 or WeakPoint3 at atoms 0 and
  1.  Templates enter [normal_hilbert_proves] only through same-atom
  endosubstitution.

  Literal source inclusions remain literal raw-axiom inclusions.  The source
  inclusions stated through provable axioms use the corresponding target
  entailment capabilities.  For the GL targets, Four and Z are derived
  directly from the structural K and Loeb capabilities.  No semantics,
  completeness theorem, classical metaprinciple, or choice principle is
  involved.

  The repeated instance commands are retained as separately named aliases.
  In particular, source line 715 repeats
  [K4Point2 <= K4Point2Z], although line 714 has just established
  [K4Z <= K4Point2Z].  Declaration 21 below records that repeated target
  literally rather than silently repairing the apparent upstream typo.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertWithRE HilbertNormal HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems
  HilbertNormalTransitiveBaseSystems HilbertNormalK4PointSystems
  HilbertNormalGLSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the three source entailment classes *)

Record structural_k4z_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4z_K : structural_k_entailment L0;
  structural_k4z_Four : has_Four L0;
  structural_k4z_Z : has_Z L0
}.

Record structural_k4point2z_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4point2z_K4Z : structural_k4z_entailment L0;
  structural_k4point2z_WeakPoint2 : has_WeakPoint2 L0
}.

Record structural_k4point3z_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4point3z_K4Z : structural_k4z_entailment L0;
  structural_k4point3z_WeakPoint3 : has_WeakPoint3 L0
}.

(** * Closed propositional tools for the direct GL derivations *)

(** The conjunction constructor in [Syntax] is the classical encoding
    [not (p -> not q)].  These three small K proofs use only the contextual
    deduction theorem and the checked Lukasiewicz basis. *)
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

(** Pointwise conjunction introduction under a shared antecedent. *)
Local Lemma K_proves_imp_and_intro :
  forall (a p q : formula nat),
    K_proves
      (Imp (Imp a p)
        (Imp (Imp a q) (Imp a (And p q)))).
Proof.
  intros a p q.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp (Imp a p) (Imp (Imp a q) (Imp a (And p q)))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - eapply Kd_mp.
    + apply Kd_theorem. apply K_proves_and_intro_imp.
    + eapply Kd_mp.
      * apply Kd_assumption. right; right; left; reflexivity.
      * apply Kd_assumption. left; reflexivity.
  - eapply Kd_mp.
    + apply Kd_assumption. right; left; reflexivity.
    + apply Kd_assumption. left; reflexivity.
Qed.

(** The precise propositional composition used in the standard proof that
    Loeb's axiom entails Four. *)
Local Lemma K_proves_nested_compose :
  forall (a b c d : formula nat),
    K_proves
      (Imp (Imp a (Imp b c))
        (Imp (Imp d b) (Imp a (Imp d c)))).
Proof.
  intros a b c d.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp (Imp a (Imp b c))
      (Imp (Imp d b) (Imp a (Imp d c)))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - eapply Kd_mp.
    + apply Kd_assumption. right; right; right; left; reflexivity.
    + apply Kd_assumption. right; left; reflexivity.
  - eapply Kd_mp.
    + apply Kd_assumption. right; right; left; reflexivity.
    + apply Kd_assumption. left; reflexivity.
Qed.

(** The first step of the customary boxdot proof of Four. *)
Local Lemma K_proves_boxdot_drop :
  forall p : formula nat,
    K_proves (Imp p (Imp (Boxdot (Box p)) (Boxdot p))).
Proof.
  intro p.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp p (Imp (Boxdot (Box p)) (Boxdot p))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  unfold Boxdot.
  eapply Kd_mp.
  - eapply Kd_mp.
    + apply Kd_theorem. apply K_proves_and_intro_imp.
    + apply Kd_assumption. right; left; reflexivity.
  - eapply Kd_mp.
    + apply Kd_theorem. apply K_proves_and_elim_left_imp.
    + apply Kd_assumption. left; reflexivity.
Qed.

(** Every structural K fragment contains the closed K calculus. *)
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

Local Lemma structural_GL_box_regularity :
  forall (L0 : modal_logic_set nat),
    structural_gl_entailment L0 ->
    forall p q, L0 (Imp p q) -> L0 (Imp (Box p) (Box q)).
Proof.
  intros L0 HGL p q Hpq.
  eapply lukasiewicz_mp.
  - exact (structural_k_lukasiewicz (structural_gl_K HGL)).
  - exact (has_K_axiom
      (structural_k_K (structural_gl_K HGL)) p q).
  - exact (structural_k_necessitation (structural_gl_K HGL) Hpq).
Qed.

Local Lemma structural_GL_imp_trans :
  forall (L0 : modal_logic_set nat),
    structural_gl_entailment L0 ->
    forall p q r,
      L0 (Imp p q) -> L0 (Imp q r) -> L0 (Imp p r).
Proof.
  intros L0 HGL p q r Hpq Hqr.
  pose proof (structural_k_lukasiewicz (structural_gl_K HGL)) as HLuk.
  eapply lukasiewicz_mp; [exact HLuk | | exact Hpq].
  eapply lukasiewicz_mp; [exact HLuk | |].
  - exact (lukasiewicz_imply_S HLuk p q r).
  - eapply lukasiewicz_mp; [exact HLuk | | exact Hqr].
    exact (lukasiewicz_imply_K HLuk (Imp q r) p).
Qed.

(** Direct, globally closed derivation of Foundation [GL.axiomFour]. *)
Local Lemma structural_GL_has_Four :
  forall (L0 : modal_logic_set nat),
    structural_gl_entailment L0 -> has_Four L0.
Proof.
  intros L0 HGL; constructor; intro p.
  pose proof (structural_gl_K HGL) as HK.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  pose proof
    (structural_K_contains_K_proves
      (L0 := L0) HK (K_proves_boxdot_drop p)) as Hdrop.
  assert (Hleft : L0 (Imp (Box (Boxdot p)) (Box p))).
  {
    apply (structural_GL_box_regularity HGL).
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    change (K_proves (Imp (And p (Box p)) p)).
    apply K_proves_and_elim_left_imp.
  }
  assert (Hright : L0 (Imp (Box (Boxdot p)) (Box (Box p)))).
  {
    apply (structural_GL_box_regularity HGL).
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    change (K_proves (Imp (And p (Box p)) (Box p))).
    apply K_proves_and_elim_right_imp.
  }
  assert (Hdistribute :
    L0 (Imp (Box (Boxdot p)) (Boxdot (Box p)))).
  {
    eapply lukasiewicz_mp; [exact HLuk | | exact Hright].
    eapply lukasiewicz_mp; [exact HLuk | | exact Hleft].
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    change (K_proves
      (Imp (Imp (Box (Boxdot p)) (Box p))
        (Imp (Imp (Box (Boxdot p)) (Box (Box p)))
          (Imp (Box (Boxdot p)) (And (Box p) (Box (Box p))))))).
    apply K_proves_imp_and_intro.
  }
  assert (Hbridge :
    L0 (Imp p (Imp (Box (Boxdot p)) (Boxdot p)))).
  {
    eapply lukasiewicz_mp; [exact HLuk | | exact Hdistribute].
    eapply lukasiewicz_mp; [exact HLuk | | exact Hdrop].
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_nested_compose.
  }
  assert (Hboxed :
    L0 (Imp (Box p)
      (Box (Imp (Box (Boxdot p)) (Boxdot p))))).
  { exact (structural_GL_box_regularity HGL Hbridge). }
  assert (Hloeb :
    L0 (Imp (Box (Imp (Box (Boxdot p)) (Boxdot p)))
      (Box (Boxdot p)))).
  { exact (has_L_axiom (structural_gl_L HGL) (Boxdot p)). }
  assert (Hto_boxdot : L0 (Imp (Box p) (Box (Boxdot p)))).
  { exact (structural_GL_imp_trans HGL Hboxed Hloeb). }
  assert (Helim : L0 (Imp (Box (Boxdot p)) (Box (Box p)))).
  {
    apply (structural_GL_box_regularity HGL).
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    change (K_proves (Imp (And p (Box p)) (Box p))).
    apply K_proves_and_elim_right_imp.
  }
  exact (structural_GL_imp_trans HGL Hto_boxdot Helim).
Qed.

(** Direct, globally closed derivation of Foundation [GL.axiomZ]. *)
Local Lemma structural_GL_has_Z :
  forall (L0 : modal_logic_set nat),
    structural_gl_entailment L0 -> has_Z L0.
Proof.
  intros L0 HGL; constructor; intro p.
  unfold Z.
  pose proof (structural_k_lukasiewicz (structural_gl_K HGL)) as HLuk.
  pose proof (has_L_axiom (structural_gl_L HGL) p) as HL.
  eapply lukasiewicz_mp; [exact HLuk | | exact HL].
  eapply lukasiewicz_mp; [exact HLuk | |].
  - exact (lukasiewicz_imply_S HLuk
      (Box (Imp (Box p) p)) (Box p)
      (Imp (Dia (Box p)) (Box p))).
  - eapply lukasiewicz_mp; [exact HLuk | |].
    + exact (lukasiewicz_imply_K HLuk
        (Imp (Box p) (Imp (Dia (Box p)) (Box p)))
        (Box (Imp (Box p) p))).
    + exact (lukasiewicz_imply_K HLuk (Box p) (Dia (Box p))).
Qed.

(** * K4Z: ten active source commands *)

(** Source declaration 1/36: [K4Z.axioms]. *)
Definition normal_K4Z_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = Z (Atom 0).

(** Source declaration 2/36: [K4Z.axioms.HasK]. *)
Definition normal_K4Z_axioms_has_K :
  raw_axioms_has_K normal_K4Z_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/36: [K4Z.axioms.HasFour]. *)
Definition normal_K4Z_axioms_has_Four :
  raw_axioms_has_Four normal_K4Z_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/36: [K4Z.axioms.HasZ]. *)
Definition normal_K4Z_axioms_has_Z :
  raw_axioms_has_Z normal_K4Z_axioms.
Proof.
  refine {| raw_Z_p := 0;
            raw_Z_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 5/36: the named logic [K4Z]. *)
Definition normal_K4Z : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4Z_axioms.

(** Source declaration 6/36: [Entailment.K4Z Modal.K4Z]. *)
Lemma normal_K4Z_entailment :
  structural_k4z_entailment normal_K4Z.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_K4Z_axioms Nat.eq_dec
        normal_K4Z_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_Four nat normal_K4Z_axioms Nat.eq_dec
      normal_K4Z_axioms_has_Four).
  - exact (@normal_hilbert_has_Z nat normal_K4Z_axioms Nat.eq_dec
      normal_K4Z_axioms_has_Z).
Qed.

(** Source declaration 7/36: [Modal.K4 <= Modal.K4Z], by literal raw-axiom
    inclusion. *)
Lemma normal_K4_weaker_than_normal_K4Z :
  logic_subset normal_K4 normal_K4Z.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_K4_axioms in Hax.
  unfold normal_K4Z_axioms.
  destruct Hax as [Hax | Hax]; subst p.
  - left; reflexivity.
  - right; left; reflexivity.
Qed.

(** Source declaration 8/36: the duplicate inferred
    [Modal.K4 <= Modal.K4Z] instance. *)
Definition normal_K4_weaker_than_normal_K4Z_duplicate :
  logic_subset normal_K4 normal_K4Z :=
  normal_K4_weaker_than_normal_K4Z.

(** Source declaration 9/36: [Modal.K4Z <= Modal.GL], using target-provable
    raw axioms exactly as in the source. *)
Lemma normal_K4Z_weaker_than_normal_GL :
  logic_subset normal_K4Z normal_GL.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4Z_axioms in Hax.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_gl_K normal_GL_entailment))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom
      (structural_GL_has_Four normal_GL_entailment) (Atom 0)).
  - exact (has_Z_axiom
      (structural_GL_has_Z normal_GL_entailment) (Atom 0)).
Qed.

(** Source declaration 10/36: the duplicate inferred
    [Modal.K4Z <= Modal.GL] instance. *)
Definition normal_K4Z_weaker_than_normal_GL_duplicate :
  logic_subset normal_K4Z normal_GL :=
  normal_K4Z_weaker_than_normal_GL.

(** * K4Point2Z: thirteen active source commands *)

(** Source declaration 11/36: [K4Point2Z.axioms]. *)
Definition normal_K4Point2Z_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = Z (Atom 0) \/
    p = WeakPoint2 (Atom 0) (Atom 1).

(** Source declaration 12/36: [K4Point2Z.axioms.HasK]. *)
Definition normal_K4Point2Z_axioms_has_K :
  raw_axioms_has_K normal_K4Point2Z_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 13/36: [K4Point2Z.axioms.HasFour]. *)
Definition normal_K4Point2Z_axioms_has_Four :
  raw_axioms_has_Four normal_K4Point2Z_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 14/36: [K4Point2Z.axioms.HasZ]. *)
Definition normal_K4Point2Z_axioms_has_Z :
  raw_axioms_has_Z normal_K4Point2Z_axioms.
Proof.
  refine {| raw_Z_p := 0;
            raw_Z_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 15/36: [K4Point2Z.axioms.HasWeakPoint2]. *)
Definition normal_K4Point2Z_axioms_has_WeakPoint2 :
  raw_axioms_has_WeakPoint2 normal_K4Point2Z_axioms.
Proof.
  refine {| raw_WeakPoint2_p := 0;
            raw_WeakPoint2_q := 1;
            raw_WeakPoint2_ne := _;
            raw_WeakPoint2_mem := _ |}.
  - discriminate.
  - right; right; right; reflexivity.
Defined.

(** Source declaration 16/36: the named logic [K4Point2Z]. *)
Definition normal_K4Point2Z : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4Point2Z_axioms.

(** Source declaration 17/36:
    [Entailment.K4Point2Z Modal.K4Point2Z]. *)
Lemma normal_K4Point2Z_entailment :
  structural_k4point2z_entailment normal_K4Point2Z.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_K4Point2Z_axioms
          Nat.eq_dec normal_K4Point2Z_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Four nat normal_K4Point2Z_axioms
        Nat.eq_dec normal_K4Point2Z_axioms_has_Four).
    + exact (@normal_hilbert_has_Z nat normal_K4Point2Z_axioms Nat.eq_dec
        normal_K4Point2Z_axioms_has_Z).
  - exact (@normal_hilbert_has_WeakPoint2 nat normal_K4Point2Z_axioms
      Nat.eq_dec normal_K4Point2Z_axioms_has_WeakPoint2).
Qed.

(** Source declaration 18/36: [Modal.K4Point2 <= Modal.K4Point2Z], by
    literal raw-axiom inclusion. *)
Lemma normal_K4Point2_weaker_than_normal_K4Point2Z :
  logic_subset normal_K4Point2 normal_K4Point2Z.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_K4Point2_axioms in Hax.
  unfold normal_K4Point2Z_axioms.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; right; reflexivity.
Qed.

(** Source declaration 19/36: the duplicate inferred
    [Modal.K4Point2 <= Modal.K4Point2Z] instance. *)
Definition normal_K4Point2_weaker_than_normal_K4Point2Z_duplicate :
  logic_subset normal_K4Point2 normal_K4Point2Z :=
  normal_K4Point2_weaker_than_normal_K4Point2Z.

(** Source declaration 20/36: [Modal.K4Z <= Modal.K4Point2Z], by literal
    raw-axiom inclusion. *)
Lemma normal_K4Z_weaker_than_normal_K4Point2Z :
  logic_subset normal_K4Z normal_K4Point2Z.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_K4Z_axioms in Hax.
  unfold normal_K4Point2Z_axioms.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
Qed.

(** Source declaration 21/36: source line 715 literally repeats the inferred
    [Modal.K4Point2 <= Modal.K4Point2Z] target from lines 711--712.  This is
    intentionally an alias of declaration 18, not of declaration 20. *)
Definition normal_K4Point2_weaker_than_normal_K4Point2Z_repeated :
  logic_subset normal_K4Point2 normal_K4Point2Z :=
  normal_K4Point2_weaker_than_normal_K4Point2Z.

(** Source declaration 22/36:
    [Modal.K4Point2Z <= Modal.GLPoint2], through target-provable axioms. *)
Lemma normal_K4Point2Z_weaker_than_normal_GLPoint2 :
  logic_subset normal_K4Point2Z normal_GLPoint2.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4Point2Z_axioms in Hax.
  pose proof
    (structural_glpoint2_GL normal_GLPoint2_entailment) as HGL.
  destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
  - exact (has_K_axiom (structural_k_K (structural_gl_K HGL))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom (structural_GL_has_Four HGL) (Atom 0)).
  - exact (has_Z_axiom (structural_GL_has_Z HGL) (Atom 0)).
  - exact (has_WeakPoint2_axiom
      (structural_glpoint2_WeakPoint2 normal_GLPoint2_entailment)
      (Atom 0) (Atom 1)).
Qed.

(** Source declaration 23/36: the duplicate inferred
    [Modal.K4Point2Z <= Modal.GLPoint2] instance. *)
Definition normal_K4Point2Z_weaker_than_normal_GLPoint2_duplicate :
  logic_subset normal_K4Point2Z normal_GLPoint2 :=
  normal_K4Point2Z_weaker_than_normal_GLPoint2.

(** * K4Point3Z: thirteen active source commands *)

(** Source declaration 24/36: [K4Point3Z.axioms]. *)
Definition normal_K4Point3Z_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = Z (Atom 0) \/
    p = WeakPoint3 (Atom 0) (Atom 1).

(** Source declaration 25/36: [K4Point3Z.axioms.HasK]. *)
Definition normal_K4Point3Z_axioms_has_K :
  raw_axioms_has_K normal_K4Point3Z_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 26/36: [K4Point3Z.axioms.HasFour]. *)
Definition normal_K4Point3Z_axioms_has_Four :
  raw_axioms_has_Four normal_K4Point3Z_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 27/36: [K4Point3Z.axioms.HasZ]. *)
Definition normal_K4Point3Z_axioms_has_Z :
  raw_axioms_has_Z normal_K4Point3Z_axioms.
Proof.
  refine {| raw_Z_p := 0;
            raw_Z_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 28/36: [K4Point3Z.axioms.HasWeakPoint3]. *)
Definition normal_K4Point3Z_axioms_has_WeakPoint3 :
  raw_axioms_has_WeakPoint3 normal_K4Point3Z_axioms.
Proof.
  refine {| raw_WeakPoint3_p := 0;
            raw_WeakPoint3_q := 1;
            raw_WeakPoint3_ne := _;
            raw_WeakPoint3_mem := _ |}.
  - discriminate.
  - right; right; right; reflexivity.
Defined.

(** Source declaration 29/36: the named logic [K4Point3Z]. *)
Definition normal_K4Point3Z : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4Point3Z_axioms.

(** Source declaration 30/36:
    [Entailment.K4Point3Z Modal.K4Point3Z]. *)
Lemma normal_K4Point3Z_entailment :
  structural_k4point3z_entailment normal_K4Point3Z.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_K4Point3Z_axioms
          Nat.eq_dec normal_K4Point3Z_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Four nat normal_K4Point3Z_axioms
        Nat.eq_dec normal_K4Point3Z_axioms_has_Four).
    + exact (@normal_hilbert_has_Z nat normal_K4Point3Z_axioms Nat.eq_dec
        normal_K4Point3Z_axioms_has_Z).
  - exact (@normal_hilbert_has_WeakPoint3 nat normal_K4Point3Z_axioms
      Nat.eq_dec normal_K4Point3Z_axioms_has_WeakPoint3).
Qed.

(** Source declaration 31/36: [Modal.K4Point3 <= Modal.K4Point3Z], using
    target-provable raw axioms exactly as in the source. *)
Lemma normal_K4Point3_weaker_than_normal_K4Point3Z :
  logic_subset normal_K4Point3 normal_K4Point3Z.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4Point3_axioms in Hax.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom
      (structural_k_K
        (structural_k4z_K
          (structural_k4point3z_K4Z normal_K4Point3Z_entailment)))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom
      (structural_k4z_Four
        (structural_k4point3z_K4Z normal_K4Point3Z_entailment))
      (Atom 0)).
  - exact (has_WeakPoint3_axiom
      (structural_k4point3z_WeakPoint3 normal_K4Point3Z_entailment)
      (Atom 0) (Atom 1)).
Qed.

(** Source declaration 32/36: the duplicate inferred
    [Modal.K4Point3 <= Modal.K4Point3Z] instance. *)
Definition normal_K4Point3_weaker_than_normal_K4Point3Z_duplicate :
  logic_subset normal_K4Point3 normal_K4Point3Z :=
  normal_K4Point3_weaker_than_normal_K4Point3Z.

(** Source declaration 33/36: [Modal.K4Z <= Modal.K4Point3Z], using
    target-provable raw axioms exactly as in the source. *)
Lemma normal_K4Z_weaker_than_normal_K4Point3Z :
  logic_subset normal_K4Z normal_K4Point3Z.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4Z_axioms in Hax.
  pose proof
    (structural_k4point3z_K4Z normal_K4Point3Z_entailment) as Hbase.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom (structural_k_K (structural_k4z_K Hbase))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom (structural_k4z_Four Hbase) (Atom 0)).
  - exact (has_Z_axiom (structural_k4z_Z Hbase) (Atom 0)).
Qed.

(** Source declaration 34/36: the duplicate inferred
    [Modal.K4Z <= Modal.K4Point3Z] instance. *)
Definition normal_K4Z_weaker_than_normal_K4Point3Z_duplicate :
  logic_subset normal_K4Z normal_K4Point3Z :=
  normal_K4Z_weaker_than_normal_K4Point3Z.

(** Source declaration 35/36:
    [Modal.K4Point3Z <= Modal.GLPoint3], through target-provable axioms. *)
Lemma normal_K4Point3Z_weaker_than_normal_GLPoint3 :
  logic_subset normal_K4Point3Z normal_GLPoint3.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4Point3Z_axioms in Hax.
  pose proof
    (structural_glpoint3_GL normal_GLPoint3_entailment) as HGL.
  destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
  - exact (has_K_axiom (structural_k_K (structural_gl_K HGL))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom (structural_GL_has_Four HGL) (Atom 0)).
  - exact (has_Z_axiom (structural_GL_has_Z HGL) (Atom 0)).
  - exact (has_WeakPoint3_axiom
      (structural_glpoint3_WeakPoint3 normal_GLPoint3_entailment)
      (Atom 0) (Atom 1)).
Qed.

(** Source declaration 36/36: the duplicate inferred
    [Modal.K4Point3Z <= Modal.GLPoint3] instance. *)
Definition normal_K4Point3Z_weaker_than_normal_GLPoint3_duplicate :
  logic_subset normal_K4Point3Z normal_GLPoint3 :=
  normal_K4Point3Z_weaker_than_normal_GLPoint3.
