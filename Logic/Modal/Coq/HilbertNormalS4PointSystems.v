(**
  The raw S4.2, S4.3, and S4.4 systems from Foundation's Normal catalogue.

  This file independently ports the exact twenty-one active declarations at
  lines 602--632 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Every system retains modal K at atoms
  0 and 1, with T and Four at atom 0.  Its final raw template is Point2 at
  atom 0, Point3 at the distinct atoms 0 and 1, or Point4 at atom 0.
  Templates enter [normal_hilbert_proves] only through same-atom
  endosubstitution.

  The source-facing records expose exactly S4 plus the selected point
  capability.  No semantic soundness, canonical-frame construction,
  completeness result, or classical metatheorem is used here.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertNormal
  HilbertNormalAxiomAdapters HilbertNormalBaseSystems
  HilbertNormalTransitiveBaseSystems HilbertNormalS4Systems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of S4Point2, S4Point3, and S4Point4 *)

Record structural_s4point2_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4point2_S4 : structural_s4_entailment L0;
  structural_s4point2_Point2 : has_Point2 L0
}.

Record structural_s4point3_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4point3_S4 : structural_s4_entailment L0;
  structural_s4point3_Point3 : has_Point3 L0
}.

Record structural_s4point4_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4point4_S4 : structural_s4_entailment L0;
  structural_s4point4_Point4 : has_Point4 L0
}.

(** * S4Point2: seven active source declarations *)

(** Source declaration 1/21: [S4Point2.axioms]. *)
Definition normal_S4Point2_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = Point2 (Atom 0).

(** Source declaration 2/21: [S4Point2.axioms.HasK]. *)
Definition normal_S4Point2_axioms_has_K :
  raw_axioms_has_K normal_S4Point2_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/21: [S4Point2.axioms.HasT]. *)
Definition normal_S4Point2_axioms_has_T :
  raw_axioms_has_T normal_S4Point2_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/21: [S4Point2.axioms.HasFour]. *)
Definition normal_S4Point2_axioms_has_Four :
  raw_axioms_has_Four normal_S4Point2_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 5/21: [S4Point2.axioms.HasPoint2]. *)
Definition normal_S4Point2_axioms_has_Point2 :
  raw_axioms_has_Point2 normal_S4Point2_axioms.
Proof.
  refine {| raw_Point2_p := 0;
            raw_Point2_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 6/21: the named logic [S4Point2]. *)
Definition normal_S4Point2 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4Point2_axioms.

(** Source declaration 7/21: [Entailment.S4Point2 Modal.S4Point2]. *)
Lemma normal_S4Point2_entailment :
  structural_s4point2_entailment normal_S4Point2.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- apply normal_hilbert_lukasiewicz.
        -- exact (@normal_hilbert_has_K nat normal_S4Point2_axioms
            Nat.eq_dec normal_S4Point2_axioms_has_K).
        -- apply normal_hilbert_has_DiaDuality.
        -- apply normal_hilbert_necessitation.
      * exact (@normal_hilbert_has_Four nat normal_S4Point2_axioms
          Nat.eq_dec normal_S4Point2_axioms_has_Four).
    + exact (@normal_hilbert_has_T nat normal_S4Point2_axioms
        Nat.eq_dec normal_S4Point2_axioms_has_T).
  - exact (@normal_hilbert_has_Point2 nat normal_S4Point2_axioms
      Nat.eq_dec normal_S4Point2_axioms_has_Point2).
Qed.

(** * S4Point3: seven active source declarations *)

(** Source declaration 8/21: [S4Point3.axioms]. *)
Definition normal_S4Point3_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = Point3 (Atom 0) (Atom 1).

(** Source declaration 9/21: [S4Point3.axioms.HasK]. *)
Definition normal_S4Point3_axioms_has_K :
  raw_axioms_has_K normal_S4Point3_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 10/21: [S4Point3.axioms.HasT]. *)
Definition normal_S4Point3_axioms_has_T :
  raw_axioms_has_T normal_S4Point3_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 11/21: [S4Point3.axioms.HasFour]. *)
Definition normal_S4Point3_axioms_has_Four :
  raw_axioms_has_Four normal_S4Point3_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 12/21: [S4Point3.axioms.HasPoint3]. *)
Definition normal_S4Point3_axioms_has_Point3 :
  raw_axioms_has_Point3 normal_S4Point3_axioms.
Proof.
  refine {| raw_Point3_p := 0;
            raw_Point3_q := 1;
            raw_Point3_ne := _;
            raw_Point3_mem := _ |}.
  - discriminate.
  - right; right; right; reflexivity.
Defined.

(** Source declaration 13/21: the named logic [S4Point3]. *)
Definition normal_S4Point3 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4Point3_axioms.

(** Source declaration 14/21: [Entailment.S4Point3 Modal.S4Point3]. *)
Lemma normal_S4Point3_entailment :
  structural_s4point3_entailment normal_S4Point3.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- apply normal_hilbert_lukasiewicz.
        -- exact (@normal_hilbert_has_K nat normal_S4Point3_axioms
            Nat.eq_dec normal_S4Point3_axioms_has_K).
        -- apply normal_hilbert_has_DiaDuality.
        -- apply normal_hilbert_necessitation.
      * exact (@normal_hilbert_has_Four nat normal_S4Point3_axioms
          Nat.eq_dec normal_S4Point3_axioms_has_Four).
    + exact (@normal_hilbert_has_T nat normal_S4Point3_axioms
        Nat.eq_dec normal_S4Point3_axioms_has_T).
  - exact (@normal_hilbert_has_Point3 nat normal_S4Point3_axioms
      Nat.eq_dec normal_S4Point3_axioms_has_Point3).
Qed.

(** * S4Point4: seven active source declarations *)

(** Source declaration 15/21: [S4Point4.axioms]. *)
Definition normal_S4Point4_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = Point4 (Atom 0).

(** Source declaration 16/21: [S4Point4.axioms.HasK]. *)
Definition normal_S4Point4_axioms_has_K :
  raw_axioms_has_K normal_S4Point4_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 17/21: [S4Point4.axioms.HasT]. *)
Definition normal_S4Point4_axioms_has_T :
  raw_axioms_has_T normal_S4Point4_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 18/21: [S4Point4.axioms.HasFour]. *)
Definition normal_S4Point4_axioms_has_Four :
  raw_axioms_has_Four normal_S4Point4_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 19/21: [S4Point4.axioms.HasPoint4]. *)
Definition normal_S4Point4_axioms_has_Point4 :
  raw_axioms_has_Point4 normal_S4Point4_axioms.
Proof.
  refine {| raw_Point4_p := 0;
            raw_Point4_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 20/21: the named logic [S4Point4]. *)
Definition normal_S4Point4 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4Point4_axioms.

(** Source declaration 21/21: [Entailment.S4Point4 Modal.S4Point4]. *)
Lemma normal_S4Point4_entailment :
  structural_s4point4_entailment normal_S4Point4.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- apply normal_hilbert_lukasiewicz.
        -- exact (@normal_hilbert_has_K nat normal_S4Point4_axioms
            Nat.eq_dec normal_S4Point4_axioms_has_K).
        -- apply normal_hilbert_has_DiaDuality.
        -- apply normal_hilbert_necessitation.
      * exact (@normal_hilbert_has_Four nat normal_S4Point4_axioms
          Nat.eq_dec normal_S4Point4_axioms_has_Four).
    + exact (@normal_hilbert_has_T nat normal_S4Point4_axioms
        Nat.eq_dec normal_S4Point4_axioms_has_T).
  - exact (@normal_hilbert_has_Point4 nat normal_S4Point4_axioms
      Nat.eq_dec normal_S4Point4_axioms_has_Point4).
Qed.
