(**
  Four specialized raw systems from Foundation's Normal catalogue.

  This file independently ports the exact 26-declaration tranche at lines
  848--891 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean]: KTc, KD4Point3Z, KTMk, and S4H.  Every
  named axiom predicate retains the source's natural-numbered templates,
  with modal K at the distinct atoms 0 and 1, unary schemata at atom 0, and
  binary weak-Point3/Mk schemata at atoms 0 and 1.  Raw templates enter
  [normal_hilbert_proves] only through same-atom endosubstitution.

  The source-facing records expose precisely the capabilities selected by
  each named entailment class.  No Kripke semantics, canonical construction,
  soundness theorem, or completeness theorem is used in this catalogue
  layer.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertNormal
  HilbertNormalAxiomAdapters HilbertNormalBaseSystems
  HilbertNormalMixedSystems HilbertNormalS4Systems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_ktc_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_ktc_K : structural_k_entailment L0;
  structural_ktc_Tc : has_Tc L0
}.

Record structural_kd4point3z_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kd4point3z_KD4 : structural_kd4_entailment L0;
  structural_kd4point3z_WeakPoint3 : has_WeakPoint3 L0;
  structural_kd4point3z_Z : has_Z L0
}.

Record structural_ktmk_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_ktmk_KT : structural_kt_entailment L0;
  structural_ktmk_Mk : has_Mk L0
}.

Record structural_s4h_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4h_S4 : structural_s4_entailment L0;
  structural_s4h_H : has_H L0
}.

(** * KTc: five active source declarations *)

(** Source declaration 1/26: [KTc.axioms]. *)
Definition normal_KTc_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Tc (Atom 0).

(** Source declaration 2/26: [KTc.axioms.HasK]. *)
Definition normal_KTc_axioms_has_K :
  raw_axioms_has_K normal_KTc_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/26: [KTc.axioms.HasTc]. *)
Definition normal_KTc_axioms_has_Tc :
  raw_axioms_has_Tc normal_KTc_axioms.
Proof.
  refine {| raw_Tc_p := 0;
            raw_Tc_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 4/26: the named logic [KTc]. *)
Definition normal_KTc : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KTc_axioms.

(** Source declaration 5/26: [Entailment.KTc Modal.KTc]. *)
Lemma normal_KTc_entailment :
  structural_ktc_entailment normal_KTc.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KTc_axioms Nat.eq_dec
        normal_KTc_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_Tc nat normal_KTc_axioms Nat.eq_dec
      normal_KTc_axioms_has_Tc).
Qed.

(** * KD4Point3Z: eight active source declarations *)

(** Source declaration 6/26: [KD4Point3Z.axioms]. *)
Definition normal_KD4Point3Z_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = D (Atom 0) \/
    p = Four (Atom 0) \/
    p = WeakPoint3 (Atom 0) (Atom 1) \/
    p = Z (Atom 0).

(** Source declaration 7/26: [KD4Point3Z.axioms.HasK]. *)
Definition normal_KD4Point3Z_axioms_has_K :
  raw_axioms_has_K normal_KD4Point3Z_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 8/26: [KD4Point3Z.axioms.HasD]. *)
Definition normal_KD4Point3Z_axioms_has_D :
  raw_axioms_has_D normal_KD4Point3Z_axioms.
Proof.
  refine {| raw_D_p := 0;
            raw_D_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 9/26: [KD4Point3Z.axioms.HasFour]. *)
Definition normal_KD4Point3Z_axioms_has_Four :
  raw_axioms_has_Four normal_KD4Point3Z_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 10/26: [KD4Point3Z.axioms.HasWeakPoint3]. *)
Definition normal_KD4Point3Z_axioms_has_WeakPoint3 :
  raw_axioms_has_WeakPoint3 normal_KD4Point3Z_axioms.
Proof.
  refine {| raw_WeakPoint3_p := 0;
            raw_WeakPoint3_q := 1;
            raw_WeakPoint3_ne := _;
            raw_WeakPoint3_mem := _ |}.
  - discriminate.
  - right; right; right; left; reflexivity.
Defined.

(** Source declaration 11/26: [KD4Point3Z.axioms.HasZ]. *)
Definition normal_KD4Point3Z_axioms_has_Z :
  raw_axioms_has_Z normal_KD4Point3Z_axioms.
Proof.
  refine {| raw_Z_p := 0;
            raw_Z_mem := _ |}.
  right; right; right; right; reflexivity.
Defined.

(** Source declaration 12/26: the named logic [KD4Point3Z]. *)
Definition normal_KD4Point3Z : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KD4Point3Z_axioms.

(** Source declaration 13/26: [Entailment.KD4Point3Z Modal.KD4Point3Z]. *)
Lemma normal_KD4Point3Z_entailment :
  structural_kd4point3z_entailment normal_KD4Point3Z.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_KD4Point3Z_axioms
          Nat.eq_dec normal_KD4Point3Z_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_D nat normal_KD4Point3Z_axioms Nat.eq_dec
        normal_KD4Point3Z_axioms_has_D).
    + exact (@normal_hilbert_has_Four nat normal_KD4Point3Z_axioms
        Nat.eq_dec normal_KD4Point3Z_axioms_has_Four).
  - exact (@normal_hilbert_has_WeakPoint3 nat normal_KD4Point3Z_axioms
      Nat.eq_dec normal_KD4Point3Z_axioms_has_WeakPoint3).
  - exact (@normal_hilbert_has_Z nat normal_KD4Point3Z_axioms Nat.eq_dec
      normal_KD4Point3Z_axioms_has_Z).
Qed.

(** * KTMk: six active source declarations *)

(** Source declaration 14/26: [KTMk.axioms]. *)
Definition normal_KTMk_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Mk (Atom 0) (Atom 1).

(** Source declaration 15/26: [KTMk.axioms.HasK]. *)
Definition normal_KTMk_axioms_has_K :
  raw_axioms_has_K normal_KTMk_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 16/26: [KTMk.axioms.HasT]. *)
Definition normal_KTMk_axioms_has_T :
  raw_axioms_has_T normal_KTMk_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 17/26: [KTMk.axioms.HasMk]. *)
Definition normal_KTMk_axioms_has_Mk :
  raw_axioms_has_Mk normal_KTMk_axioms.
Proof.
  refine {| raw_Mk_p := 0;
            raw_Mk_q := 1;
            raw_Mk_ne := _;
            raw_Mk_mem := _ |}.
  - discriminate.
  - right; right; reflexivity.
Defined.

(** Source declaration 18/26: the named logic [KTMk]. *)
Definition normal_KTMk : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KTMk_axioms.

(** Source declaration 19/26: [Entailment.KTMk Modal.KTMk]. *)
Lemma normal_KTMk_entailment :
  structural_ktmk_entailment normal_KTMk.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_KTMk_axioms Nat.eq_dec
          normal_KTMk_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_T nat normal_KTMk_axioms Nat.eq_dec
        normal_KTMk_axioms_has_T).
  - exact (@normal_hilbert_has_Mk nat normal_KTMk_axioms Nat.eq_dec
      normal_KTMk_axioms_has_Mk).
Qed.

(** * S4H: seven active source declarations *)

(** Source declaration 20/26: [S4H.axioms]. *)
Definition normal_S4H_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = H (Atom 0).

(** Source declaration 21/26: [S4H.axioms.HasK]. *)
Definition normal_S4H_axioms_has_K :
  raw_axioms_has_K normal_S4H_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 22/26: [S4H.axioms.HasT]. *)
Definition normal_S4H_axioms_has_T :
  raw_axioms_has_T normal_S4H_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 23/26: [S4H.axioms.HasFour]. *)
Definition normal_S4H_axioms_has_Four :
  raw_axioms_has_Four normal_S4H_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 24/26: [S4H.axioms.HasH1]. *)
Definition normal_S4H_axioms_has_H1 :
  raw_axioms_has_H1 normal_S4H_axioms.
Proof.
  refine {| raw_H1_p := 0;
            raw_H1_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 25/26: the named logic [S4H]. *)
Definition normal_S4H : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4H_axioms.

(** Source declaration 26/26: [Entailment.S4H Modal.S4H]. *)
Lemma normal_S4H_entailment :
  structural_s4h_entailment normal_S4H.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- apply normal_hilbert_lukasiewicz.
        -- exact (@normal_hilbert_has_K nat normal_S4H_axioms Nat.eq_dec
            normal_S4H_axioms_has_K).
        -- apply normal_hilbert_has_DiaDuality.
        -- apply normal_hilbert_necessitation.
      * exact (@normal_hilbert_has_Four nat normal_S4H_axioms Nat.eq_dec
          normal_S4H_axioms_has_Four).
    + exact (@normal_hilbert_has_T nat normal_S4H_axioms Nat.eq_dec
        normal_S4H_axioms_has_T).
  - exact (@normal_hilbert_has_H nat normal_S4H_axioms Nat.eq_dec
      normal_S4H_axioms_has_H1).
Qed.
