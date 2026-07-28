(**
  The raw K4.2 and K4.3 systems from Foundation's Normal catalogue.

  This file independently ports the exact twelve-declaration tranche at
  lines 449--466 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Both systems retain modal K at atoms 0
  and 1 and Four at atom 0; their final raw template is respectively
  WeakPoint2 or WeakPoint3 at the distinct atoms 0 and 1.  Templates enter
  [normal_hilbert_proves] only through same-atom endosubstitution.

  The source-facing records expose exactly K4 plus the selected weak point
  capability.  No canonical-frame, semantic soundness, or completeness
  result is needed for this raw catalogue layer.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertWithRE HilbertNormal HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems HilbertNormalTransitiveBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record structural_k4point2_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4point2_K4 : structural_k4_entailment L0;
  structural_k4point2_WeakPoint2 : has_WeakPoint2 L0
}.

Record structural_k4point3_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4point3_K4 : structural_k4_entailment L0;
  structural_k4point3_WeakPoint3 : has_WeakPoint3 L0
}.

(** * K4Point2: six active source declarations *)

(** Source declaration 1/12: [K4Point2.axioms]. *)
Definition normal_K4Point2_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = WeakPoint2 (Atom 0) (Atom 1).

(** Source declaration 2/12: [K4Point2.axioms.HasK]. *)
Definition normal_K4Point2_axioms_has_K :
  raw_axioms_has_K normal_K4Point2_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/12: [K4Point2.axioms.HasFour]. *)
Definition normal_K4Point2_axioms_has_Four :
  raw_axioms_has_Four normal_K4Point2_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/12: [K4Point2.axioms.HasWeakPoint2]. *)
Definition normal_K4Point2_axioms_has_WeakPoint2 :
  raw_axioms_has_WeakPoint2 normal_K4Point2_axioms.
Proof.
  refine {| raw_WeakPoint2_p := 0;
            raw_WeakPoint2_q := 1;
            raw_WeakPoint2_ne := _;
            raw_WeakPoint2_mem := _ |}.
  - discriminate.
  - right; right; reflexivity.
Defined.

(** Source declaration 5/12: the named logic [K4Point2]. *)
Definition normal_K4Point2 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4Point2_axioms.

(** Source declaration 6/12: [Entailment.K4Point2 Modal.K4Point2]. *)
Lemma normal_K4Point2_entailment :
  structural_k4point2_entailment normal_K4Point2.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_K4Point2_axioms Nat.eq_dec
          normal_K4Point2_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Four nat normal_K4Point2_axioms Nat.eq_dec
        normal_K4Point2_axioms_has_Four).
  - exact (@normal_hilbert_has_WeakPoint2 nat normal_K4Point2_axioms
      Nat.eq_dec normal_K4Point2_axioms_has_WeakPoint2).
Qed.

(** * K4Point3: six active source declarations *)

(** Source declaration 7/12: [K4Point3.axioms]. *)
Definition normal_K4Point3_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = WeakPoint3 (Atom 0) (Atom 1).

(** Source declaration 8/12: [K4Point3.axioms.HasK]. *)
Definition normal_K4Point3_axioms_has_K :
  raw_axioms_has_K normal_K4Point3_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 9/12: [K4Point3.axioms.HasFour]. *)
Definition normal_K4Point3_axioms_has_Four :
  raw_axioms_has_Four normal_K4Point3_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 10/12: [K4Point3.axioms.HasWeakPoint3]. *)
Definition normal_K4Point3_axioms_has_WeakPoint3 :
  raw_axioms_has_WeakPoint3 normal_K4Point3_axioms.
Proof.
  refine {| raw_WeakPoint3_p := 0;
            raw_WeakPoint3_q := 1;
            raw_WeakPoint3_ne := _;
            raw_WeakPoint3_mem := _ |}.
  - discriminate.
  - right; right; reflexivity.
Defined.

(** Source declaration 11/12: the named logic [K4Point3]. *)
Definition normal_K4Point3 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4Point3_axioms.

(** Source declaration 12/12: [Entailment.K4Point3 Modal.K4Point3]. *)
Lemma normal_K4Point3_entailment :
  structural_k4point3_entailment normal_K4Point3.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_K4Point3_axioms Nat.eq_dec
          normal_K4Point3_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Four nat normal_K4Point3_axioms Nat.eq_dec
        normal_K4Point3_axioms_has_Four).
  - exact (@normal_hilbert_has_WeakPoint3 nat normal_K4Point3_axioms
      Nat.eq_dec normal_K4Point3_axioms_has_WeakPoint3).
Qed.
