(**
  Four mixed raw systems from Foundation's Normal catalogue.

  This file independently ports the exact 25-declaration tranche at lines
  468--506 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean]: KT4B, K45, KD4, and KD5.  Each named
  axiom predicate retains the source's natural-numbered templates, with K
  at the distinct atoms 0 and 1 and every unary schema at atom 0.  Raw
  templates enter [normal_hilbert_proves] only through same-atom
  endosubstitution.

  The source-facing records expose precisely K together with the selected
  T, D, Four, Five, and B capabilities.  No Kripke semantics, canonical
  construction, soundness theorem, or completeness theorem is used here.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertNormal
  HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_kt4b_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kt4b_K : structural_k_entailment L0;
  structural_kt4b_T : has_T L0;
  structural_kt4b_Four : has_Four L0;
  structural_kt4b_B : has_B L0
}.

Record structural_k45_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k45_K : structural_k_entailment L0;
  structural_k45_Four : has_Four L0;
  structural_k45_Five : has_Five L0
}.

Record structural_kd4_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kd4_K : structural_k_entailment L0;
  structural_kd4_D : has_D L0;
  structural_kd4_Four : has_Four L0
}.

Record structural_kd5_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kd5_K : structural_k_entailment L0;
  structural_kd5_D : has_D L0;
  structural_kd5_Five : has_Five L0
}.

(** * KT4B: seven active source declarations *)

(** Source declaration 1/25: [KT4B.axioms]. *)
Definition normal_KT4B_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = B (Atom 0).

(** Source declaration 2/25: [KT4B.axioms.HasK]. *)
Definition normal_KT4B_axioms_has_K :
  raw_axioms_has_K normal_KT4B_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/25: [KT4B.axioms.HasT]. *)
Definition normal_KT4B_axioms_has_T :
  raw_axioms_has_T normal_KT4B_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/25: [KT4B.axioms.HasFour]. *)
Definition normal_KT4B_axioms_has_Four :
  raw_axioms_has_Four normal_KT4B_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 5/25: [KT4B.axioms.HasB]. *)
Definition normal_KT4B_axioms_has_B :
  raw_axioms_has_B normal_KT4B_axioms.
Proof.
  refine {| raw_B_p := 0;
            raw_B_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 6/25: the named logic [KT4B]. *)
Definition normal_KT4B : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KT4B_axioms.

(** Source declaration 7/25: [Entailment.KT4B Modal.KT4B]. *)
Lemma normal_KT4B_entailment :
  structural_kt4b_entailment normal_KT4B.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KT4B_axioms Nat.eq_dec
        normal_KT4B_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_T nat normal_KT4B_axioms Nat.eq_dec
      normal_KT4B_axioms_has_T).
  - exact (@normal_hilbert_has_Four nat normal_KT4B_axioms Nat.eq_dec
      normal_KT4B_axioms_has_Four).
  - exact (@normal_hilbert_has_B nat normal_KT4B_axioms Nat.eq_dec
      normal_KT4B_axioms_has_B).
Qed.

(** * K45: six active source declarations *)

(** Source declaration 8/25: [K45.axioms]. *)
Definition normal_K45_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = Five (Atom 0).

(** Source declaration 9/25: [K45.axioms.HasK]. *)
Definition normal_K45_axioms_has_K :
  raw_axioms_has_K normal_K45_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 10/25: [K45.axioms.HasFour]. *)
Definition normal_K45_axioms_has_Four :
  raw_axioms_has_Four normal_K45_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 11/25: [K45.axioms.HasFive]. *)
Definition normal_K45_axioms_has_Five :
  raw_axioms_has_Five normal_K45_axioms.
Proof.
  refine {| raw_Five_p := 0;
            raw_Five_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 12/25: the named logic [K45]. *)
Definition normal_K45 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K45_axioms.

(** Source declaration 13/25: [Entailment.K45 Modal.K45]. *)
Lemma normal_K45_entailment :
  structural_k45_entailment normal_K45.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_K45_axioms Nat.eq_dec
        normal_K45_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_Four nat normal_K45_axioms Nat.eq_dec
      normal_K45_axioms_has_Four).
  - exact (@normal_hilbert_has_Five nat normal_K45_axioms Nat.eq_dec
      normal_K45_axioms_has_Five).
Qed.

(** * KD4: six active source declarations *)

(** Source declaration 14/25: [KD4.axioms]. *)
Definition normal_KD4_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = D (Atom 0) \/
    p = Four (Atom 0).

(** Source declaration 15/25: [KD4.axioms.HasK]. *)
Definition normal_KD4_axioms_has_K :
  raw_axioms_has_K normal_KD4_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 16/25: [KD4.axioms.HasD]. *)
Definition normal_KD4_axioms_has_D :
  raw_axioms_has_D normal_KD4_axioms.
Proof.
  refine {| raw_D_p := 0;
            raw_D_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 17/25: [KD4.axioms.HasFour]. *)
Definition normal_KD4_axioms_has_Four :
  raw_axioms_has_Four normal_KD4_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 18/25: the named logic [KD4]. *)
Definition normal_KD4 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KD4_axioms.

(** Source declaration 19/25: [Entailment.KD4 Modal.KD4]. *)
Lemma normal_KD4_entailment :
  structural_kd4_entailment normal_KD4.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KD4_axioms Nat.eq_dec
        normal_KD4_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_D nat normal_KD4_axioms Nat.eq_dec
      normal_KD4_axioms_has_D).
  - exact (@normal_hilbert_has_Four nat normal_KD4_axioms Nat.eq_dec
      normal_KD4_axioms_has_Four).
Qed.

(** * KD5: six active source declarations *)

(** Source declaration 20/25: [KD5.axioms]. *)
Definition normal_KD5_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = D (Atom 0) \/
    p = Five (Atom 0).

(** Source declaration 21/25: [KD5.axioms.HasK]. *)
Definition normal_KD5_axioms_has_K :
  raw_axioms_has_K normal_KD5_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 22/25: [KD5.axioms.HasD]. *)
Definition normal_KD5_axioms_has_D :
  raw_axioms_has_D normal_KD5_axioms.
Proof.
  refine {| raw_D_p := 0;
            raw_D_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 23/25: [KD5.axioms.HasFive]. *)
Definition normal_KD5_axioms_has_Five :
  raw_axioms_has_Five normal_KD5_axioms.
Proof.
  refine {| raw_Five_p := 0;
            raw_Five_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 24/25: the named logic [KD5]. *)
Definition normal_KD5 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KD5_axioms.

(** Source declaration 25/25: [Entailment.KD5 Modal.KD5]. *)
Lemma normal_KD5_entailment :
  structural_kd5_entailment normal_KD5.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KD5_axioms Nat.eq_dec
        normal_KD5_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_D nat normal_KD5_axioms Nat.eq_dec
      normal_KD5_axioms_has_D).
  - exact (@normal_hilbert_has_Five nat normal_KD5_axioms Nat.eq_dec
      normal_KD5_axioms_has_Five).
Qed.
