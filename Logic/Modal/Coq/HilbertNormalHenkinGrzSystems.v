(**
  The raw KHen, K4Hen, Grz, Grz.2, and Grz.3 systems from Foundation's
  Normal catalogue.

  This file independently ports the exact twenty-eight active declarations
  at lines 741--786 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Each axiom predicate retains the
  source's natural-numbered templates: modal K at the distinct atoms 0 and
  1, with Henkin, Four, Grzegorczyk, Point2, or Point3 at the indicated
  atoms.  Raw templates enter [normal_hilbert_proves] only through
  same-atom endosubstitution.

  The source inclusion KT <= Grz is the sole derived-axiom boundary in this
  tranche.  Its short syntactic proof boxes the propositional K combinator
  [p -> (Box (p -> Box p) -> p)] and composes the result with Grz.  No
  semantics, soundness, completeness theorem, or nonconstructive principle
  is used here.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertNormal
  HilbertNormalAxiomAdapters HilbertNormalBaseSystems
  HilbertNormalTransitiveBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_k4hen_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4hen_K4 : structural_k4_entailment L0;
  structural_k4hen_Hen : has_Hen L0
}.

Record structural_grz_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_grz_K : structural_k_entailment L0;
  structural_grz_Grz : has_Grz L0
}.

Record structural_grzpoint2_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_grzpoint2_Grz : structural_grz_entailment L0;
  structural_grzpoint2_Point2 : has_Point2 L0
}.

Record structural_grzpoint3_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_grzpoint3_Grz : structural_grz_entailment L0;
  structural_grzpoint3_Point3 : has_Point3 L0
}.

(** * KHen: four active source declarations *)

(** Source declaration 1/28: [KHen.axioms]. *)
Definition normal_KHen_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Hen (Atom 0).

(** Source declaration 2/28: [KHen.axioms.HasK]. *)
Definition normal_KHen_axioms_has_K :
  raw_axioms_has_K normal_KHen_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/28: [KHen.axioms.HasHen]. *)
Definition normal_KHen_axioms_has_Hen :
  raw_axioms_has_Hen normal_KHen_axioms.
Proof.
  refine {| raw_Hen_p := 0;
            raw_Hen_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 4/28: the named logic [KHen]. *)
Definition normal_KHen : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KHen_axioms.

(** * K4Hen: six active source declarations *)

(** Source declaration 5/28: [K4Hen.axioms]. *)
Definition normal_K4Hen_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = Hen (Atom 0).

(** Source declaration 6/28: [K4Hen.axioms.HasK]. *)
Definition normal_K4Hen_axioms_has_K :
  raw_axioms_has_K normal_K4Hen_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 7/28: [K4Hen.axioms.HasFour]. *)
Definition normal_K4Hen_axioms_has_Four :
  raw_axioms_has_Four normal_K4Hen_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 8/28: [K4Hen.axioms.HasHen]. *)
Definition normal_K4Hen_axioms_has_Hen :
  raw_axioms_has_Hen normal_K4Hen_axioms.
Proof.
  refine {| raw_Hen_p := 0;
            raw_Hen_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 9/28: the named logic [K4Hen]. *)
Definition normal_K4Hen : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4Hen_axioms.

(** Source declaration 10/28: [Entailment.K4Hen Modal.K4Hen]. *)
Lemma normal_K4Hen_entailment :
  structural_k4hen_entailment normal_K4Hen.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_K4Hen_axioms Nat.eq_dec
          normal_K4Hen_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Four nat normal_K4Hen_axioms Nat.eq_dec
        normal_K4Hen_axioms_has_Four).
  - exact (@normal_hilbert_has_Hen nat normal_K4Hen_axioms Nat.eq_dec
      normal_K4Hen_axioms_has_Hen).
Qed.

(** * Grz: six active source declarations *)

(** Source declaration 11/28: [Grz.axioms]. *)
Definition normal_Grz_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Grz (Atom 0).

(** Source declaration 12/28: [Grz.axioms.HasK]. *)
Definition normal_Grz_axioms_has_K :
  raw_axioms_has_K normal_Grz_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 13/28: [Grz.axioms.HasGrz]. *)
Definition normal_Grz_axioms_has_Grz :
  raw_axioms_has_Grz normal_Grz_axioms.
Proof.
  refine {| raw_Grz_p := 0;
            raw_Grz_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 14/28: the named logic [Grz]. *)
Definition normal_Grz : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_Grz_axioms.

(** Source declaration 15/28: [Entailment.Grz Modal.Grz]. *)
Lemma normal_Grz_entailment :
  structural_grz_entailment normal_Grz.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_Grz_axioms Nat.eq_dec
        normal_Grz_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_Grz nat normal_Grz_axioms Nat.eq_dec
      normal_Grz_axioms_has_Grz).
Qed.

(** Grz derives T directly in the raw calculus.  If [Box p] holds, boxing
    the K combinator [p -> (Box (p -> Box p) -> p)] yields the antecedent of
    the Grz instance at [p]. *)
Local Lemma normal_Grz_proves_T :
  forall p : formula nat, normal_Grz (T p).
Proof.
  intro p; unfold T.
  set (guard := Box (Imp p (Box p))).
  assert (Hboxed :
    normal_Grz (Box (Imp p (Imp guard p)))).
  { apply NH_nec. apply NH_imply_K. }
  assert (Hantecedent :
    normal_Grz (Imp (Box p) (Box (Imp guard p)))).
  { eapply NH_mp.
    - exact (has_K_axiom
        (structural_k_K (structural_grz_K normal_Grz_entailment))
        p (Imp guard p)).
    - exact Hboxed. }
  assert (Hgrz : normal_Grz (Imp (Box (Imp guard p)) p)).
  { change (normal_Grz (Grz p)).
    exact (has_Grz_axiom (structural_grz_Grz normal_Grz_entailment) p). }
  eapply normal_hilbert_under_mp.
  - exact (@normal_hilbert_imply_intro nat normal_Grz_axioms
      (Box p) (Imp (Box (Imp guard p)) p) Hgrz).
  - exact Hantecedent.
Qed.

(** Source declaration 16/28: [Modal.KT <= Modal.Grz]. *)
Lemma normal_KT_weaker_than_normal_Grz :
  logic_subset normal_KT normal_Grz.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_KT_axioms in Hax.
  destruct Hax as [Hax | Hax]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_grz_K normal_Grz_entailment))
      (Atom 0) (Atom 1)).
  - apply normal_Grz_proves_T.
Qed.

(** * GrzPoint2: six active source declarations *)

(** Source declaration 17/28: [GrzPoint2.axioms]. *)
Definition normal_GrzPoint2_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Grz (Atom 0) \/
    p = Point2 (Atom 0).

(** Source declaration 18/28: [GrzPoint2.axioms.HasK]. *)
Definition normal_GrzPoint2_axioms_has_K :
  raw_axioms_has_K normal_GrzPoint2_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 19/28: [GrzPoint2.axioms.HasGrz]. *)
Definition normal_GrzPoint2_axioms_has_Grz :
  raw_axioms_has_Grz normal_GrzPoint2_axioms.
Proof.
  refine {| raw_Grz_p := 0;
            raw_Grz_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 20/28: [GrzPoint2.axioms.HasPoint2]. *)
Definition normal_GrzPoint2_axioms_has_Point2 :
  raw_axioms_has_Point2 normal_GrzPoint2_axioms.
Proof.
  refine {| raw_Point2_p := 0;
            raw_Point2_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 21/28: the named logic [GrzPoint2]. *)
Definition normal_GrzPoint2 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_GrzPoint2_axioms.

(** Source declaration 22/28: [Entailment.GrzPoint2 Modal.GrzPoint2]. *)
Lemma normal_GrzPoint2_entailment :
  structural_grzpoint2_entailment normal_GrzPoint2.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_GrzPoint2_axioms
          Nat.eq_dec normal_GrzPoint2_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Grz nat normal_GrzPoint2_axioms
        Nat.eq_dec normal_GrzPoint2_axioms_has_Grz).
  - exact (@normal_hilbert_has_Point2 nat normal_GrzPoint2_axioms
      Nat.eq_dec normal_GrzPoint2_axioms_has_Point2).
Qed.

(** * GrzPoint3: six active source declarations *)

(** Source declaration 23/28: [GrzPoint3.axioms]. *)
Definition normal_GrzPoint3_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Grz (Atom 0) \/
    p = Point3 (Atom 0) (Atom 1).

(** Source declaration 24/28: [GrzPoint3.axioms.HasK]. *)
Definition normal_GrzPoint3_axioms_has_K :
  raw_axioms_has_K normal_GrzPoint3_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 25/28: [GrzPoint3.axioms.HasGrz]. *)
Definition normal_GrzPoint3_axioms_has_Grz :
  raw_axioms_has_Grz normal_GrzPoint3_axioms.
Proof.
  refine {| raw_Grz_p := 0;
            raw_Grz_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 26/28: [GrzPoint3.axioms.HasPoint3]. *)
Definition normal_GrzPoint3_axioms_has_Point3 :
  raw_axioms_has_Point3 normal_GrzPoint3_axioms.
Proof.
  refine {| raw_Point3_p := 0;
            raw_Point3_q := 1;
            raw_Point3_ne := _;
            raw_Point3_mem := _ |}.
  - discriminate.
  - right; right; reflexivity.
Defined.

(** Source declaration 27/28: the named logic [GrzPoint3]. *)
Definition normal_GrzPoint3 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_GrzPoint3_axioms.

(** Source declaration 28/28: [Entailment.GrzPoint3 Modal.GrzPoint3]. *)
Lemma normal_GrzPoint3_entailment :
  structural_grzpoint3_entailment normal_GrzPoint3.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_GrzPoint3_axioms
          Nat.eq_dec normal_GrzPoint3_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Grz nat normal_GrzPoint3_axioms
        Nat.eq_dec normal_GrzPoint3_axioms_has_Grz).
  - exact (@normal_hilbert_has_Point3 nat normal_GrzPoint3_axioms
      Nat.eq_dec normal_GrzPoint3_axioms_has_Point3).
Qed.
