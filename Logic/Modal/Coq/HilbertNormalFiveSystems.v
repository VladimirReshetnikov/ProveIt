(**
  The raw K5 and S5 systems from Foundation's Normal catalogue.

  This file independently ports the exact eleven-declaration tranche at
  lines 635--651 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Both named axiom predicates retain the
  source's natural-numbered templates: K at the distinct atoms 0 and 1,
  Five at atom 0, and additionally T at atom 0 for S5.  Raw templates enter
  [normal_hilbert_proves] only through same-atom endosubstitution.

  The source-facing records expose precisely K together with the selected
  Five and T capabilities.  This raw catalogue layer uses no Kripke
  semantics, canonical construction, nonconstructive principle, soundness, or
  completeness theorem.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertNormal HilbertNormalAxiomAdapters HilbertNormalBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_k5_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k5_K : structural_k_entailment L0;
  structural_k5_Five : has_Five L0
}.

Record structural_s5_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s5_K : structural_k_entailment L0;
  structural_s5_T : has_T L0;
  structural_s5_Five : has_Five L0
}.

(** * K5: five active source declarations *)

(** Source declaration 1/11: [K5.axioms]. *)
Definition normal_K5_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Five (Atom 0).

(** Source declaration 2/11: [K5.axioms.HasK]. *)
Definition normal_K5_axioms_has_K :
  raw_axioms_has_K normal_K5_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/11: [K5.axioms.HasFive]. *)
Definition normal_K5_axioms_has_Five :
  raw_axioms_has_Five normal_K5_axioms.
Proof.
  refine {| raw_Five_p := 0;
            raw_Five_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 4/11: the named logic [K5]. *)
Definition normal_K5 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K5_axioms.

(** Source declaration 5/11: [Entailment.K5 Modal.K5]. *)
Lemma normal_K5_entailment :
  structural_k5_entailment normal_K5.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_K5_axioms Nat.eq_dec
        normal_K5_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_Five nat normal_K5_axioms Nat.eq_dec
      normal_K5_axioms_has_Five).
Qed.

(** * S5: six active source declarations *)

(** Source declaration 6/11: [S5.axioms]. *)
Definition normal_S5_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Five (Atom 0).

(** Source declaration 7/11: [S5.axioms.HasK]. *)
Definition normal_S5_axioms_has_K :
  raw_axioms_has_K normal_S5_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 8/11: [S5.axioms.HasT]. *)
Definition normal_S5_axioms_has_T :
  raw_axioms_has_T normal_S5_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 9/11: [S5.axioms.HasFive]. *)
Definition normal_S5_axioms_has_Five :
  raw_axioms_has_Five normal_S5_axioms.
Proof.
  refine {| raw_Five_p := 0;
            raw_Five_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 10/11: the named logic [S5]. *)
Definition normal_S5 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S5_axioms.

(** Source declaration 11/11: [Entailment.S5 Modal.S5]. *)
Lemma normal_S5_entailment :
  structural_s5_entailment normal_S5.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_S5_axioms Nat.eq_dec
        normal_S5_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_T nat normal_S5_axioms Nat.eq_dec
      normal_S5_axioms_has_T).
  - exact (@normal_hilbert_has_Five nat normal_S5_axioms Nat.eq_dec
      normal_S5_axioms_has_Five).
Qed.
