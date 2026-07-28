(**
  The raw KD45, KB4, and KB5 systems from Foundation's Normal catalogue.

  This file independently ports the exact nineteen-declaration tranche
  immediately following KD5 in the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Every named axiom predicate retains
  the source's natural-numbered raw templates: modal K at atoms 0 and 1,
  and each selected unary schema at atom 0.  Those templates enter
  [normal_hilbert_proves] only through same-atom endosubstitution.

  The source-facing records expose precisely the structural K capability
  together with D, Four, Five, or B as appropriate.  No semantic soundness,
  canonical-frame construction, or completeness result is used here.
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

(** * Exact structural counterparts of KD45, KB4, and KB5 *)

Record structural_kd45_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kd45_K : structural_k_entailment L0;
  structural_kd45_D : has_D L0;
  structural_kd45_Four : has_Four L0;
  structural_kd45_Five : has_Five L0
}.

Record structural_kb4_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kb4_K : structural_k_entailment L0;
  structural_kb4_B : has_B L0;
  structural_kb4_Four : has_Four L0
}.

Record structural_kb5_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kb5_K : structural_k_entailment L0;
  structural_kb5_B : has_B L0;
  structural_kb5_Five : has_Five L0
}.

(** * KD45: seven active source declarations *)

(** Source declaration 1/19: [KD45.axioms]. *)
Definition normal_KD45_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = D (Atom 0) \/
    p = Four (Atom 0) \/
    p = Five (Atom 0).

(** Source declaration 2/19: [KD45.axioms.HasK]. *)
Definition normal_KD45_axioms_has_K :
  raw_axioms_has_K normal_KD45_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/19: [KD45.axioms.HasD]. *)
Definition normal_KD45_axioms_has_D :
  raw_axioms_has_D normal_KD45_axioms.
Proof.
  refine {| raw_D_p := 0;
            raw_D_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/19: [KD45.axioms.HasFour]. *)
Definition normal_KD45_axioms_has_Four :
  raw_axioms_has_Four normal_KD45_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 5/19: [KD45.axioms.HasFive]. *)
Definition normal_KD45_axioms_has_Five :
  raw_axioms_has_Five normal_KD45_axioms.
Proof.
  refine {| raw_Five_p := 0;
            raw_Five_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 6/19: the named logic [KD45]. *)
Definition normal_KD45 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KD45_axioms.

(** Source declaration 7/19: [Entailment.KD45 Modal.KD45]. *)
Lemma normal_KD45_entailment :
  structural_kd45_entailment normal_KD45.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KD45_axioms Nat.eq_dec
        normal_KD45_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_D nat normal_KD45_axioms Nat.eq_dec
      normal_KD45_axioms_has_D).
  - exact (@normal_hilbert_has_Four nat normal_KD45_axioms Nat.eq_dec
      normal_KD45_axioms_has_Four).
  - exact (@normal_hilbert_has_Five nat normal_KD45_axioms Nat.eq_dec
      normal_KD45_axioms_has_Five).
Qed.

(** * KB4: six active source declarations *)

(** Source declaration 8/19: [KB4.axioms]. *)
Definition normal_KB4_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = B (Atom 0) \/
    p = Four (Atom 0).

(** Source declaration 9/19: [KB4.axioms.HasK]. *)
Definition normal_KB4_axioms_has_K :
  raw_axioms_has_K normal_KB4_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 10/19: [KB4.axioms.HasB]. *)
Definition normal_KB4_axioms_has_B :
  raw_axioms_has_B normal_KB4_axioms.
Proof.
  refine {| raw_B_p := 0;
            raw_B_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 11/19: [KB4.axioms.HasFour]. *)
Definition normal_KB4_axioms_has_Four :
  raw_axioms_has_Four normal_KB4_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 12/19: the named logic [KB4]. *)
Definition normal_KB4 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KB4_axioms.

(** Source declaration 13/19: [Entailment.KB4 Modal.KB4]. *)
Lemma normal_KB4_entailment :
  structural_kb4_entailment normal_KB4.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KB4_axioms Nat.eq_dec
        normal_KB4_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_B nat normal_KB4_axioms Nat.eq_dec
      normal_KB4_axioms_has_B).
  - exact (@normal_hilbert_has_Four nat normal_KB4_axioms Nat.eq_dec
      normal_KB4_axioms_has_Four).
Qed.

(** * KB5: six active source declarations *)

(** Source declaration 14/19: [KB5.axioms]. *)
Definition normal_KB5_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = B (Atom 0) \/
    p = Five (Atom 0).

(** Source declaration 15/19: [KB5.axioms.HasK]. *)
Definition normal_KB5_axioms_has_K :
  raw_axioms_has_K normal_KB5_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 16/19: [KB5.axioms.HasB]. *)
Definition normal_KB5_axioms_has_B :
  raw_axioms_has_B normal_KB5_axioms.
Proof.
  refine {| raw_B_p := 0;
            raw_B_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 17/19: [KB5.axioms.HasFive]. *)
Definition normal_KB5_axioms_has_Five :
  raw_axioms_has_Five normal_KB5_axioms.
Proof.
  refine {| raw_Five_p := 0;
            raw_Five_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 18/19: the named logic [KB5]. *)
Definition normal_KB5 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KB5_axioms.

(** Source declaration 19/19: [Entailment.KB5 Modal.KB5]. *)
Lemma normal_KB5_entailment :
  structural_kb5_entailment normal_KB5.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KB5_axioms Nat.eq_dec
        normal_KB5_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_B nat normal_KB5_axioms Nat.eq_dec
      normal_KB5_axioms_has_B).
  - exact (@normal_hilbert_has_Five nat normal_KB5_axioms Nat.eq_dec
      normal_KB5_axioms_has_Five).
Qed.
