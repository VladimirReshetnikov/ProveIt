(**
  The first named replacement-of-equivalents calculi from
  [Modal/Hilbert/WithRE/Basic.lean].

  This file independently ports the complete active declaration surface at
  source lines 196--242 for E, EM, EC, EN, EMC, EMN, ECN, and EK.  The EMCN
  block in that interval is intentionally omitted because it is already
  ported by [HilbertWithRESystems].

  Every raw axiom predicate is fixed over natural-numbered atoms and every
  source raw-capability witness is retained.  The source-facing entailment
  adapters are unconditional by the classical-completeness theorem for the
  faithful six-constructor WithRE calculus; no constructor is added here.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertWithRE
  HilbertWithREClassicalCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Minimal source-class support

    [EntailmentExtensions] already exports the E, EM, EN, and EMC records.
    These are the four additional combinations needed by this catalogue and
    by subsequent portions of [WithRE/Basic.lean]. *)

Record ec_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  ec_E : e_entailment L;
  ec_C : has_C L
}.

Record emn_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  emn_EM : em_entailment L;
  emn_N : has_N L
}.

Record ecn_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  ecn_EC : ec_entailment L;
  ecn_N : has_N L
}.

Record ek_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  ek_E : e_entailment L;
  ek_K : has_K L
}.

(** * E: one active source declaration *)

Definition with_re_E : modal_logic_set nat :=
  with_re_proves (@with_re_empty_axioms nat).

(** * EM: four active source declarations *)

Definition with_re_EM_axioms : with_re_axiom nat :=
  fun p => p = M (Atom 0) (Atom 1).

Definition with_re_EM_axioms_has_M :
    with_re_axioms_has_M with_re_EM_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - reflexivity.
Defined.

Definition with_re_EM : modal_logic_set nat :=
  with_re_proves with_re_EM_axioms.

Lemma with_re_EM_entailment :
  em_entailment with_re_EM.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_M Nat.eq_dec with_re_EM_axioms_has_M).
Qed.

(** * EC: four active source declarations *)

Definition with_re_EC_axioms : with_re_axiom nat :=
  fun p => p = C (Atom 0) (Atom 1).

Definition with_re_EC_axioms_has_C :
    with_re_axioms_has_C with_re_EC_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - reflexivity.
Defined.

Definition with_re_EC : modal_logic_set nat :=
  with_re_proves with_re_EC_axioms.

Lemma with_re_EC_entailment :
  ec_entailment with_re_EC.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_C Nat.eq_dec with_re_EC_axioms_has_C).
Qed.

(** * EN: four active source declarations *)

Definition with_re_EN_axioms : with_re_axiom nat :=
  fun p => p = (@N nat).

Definition with_re_EN_axioms_has_N :
    with_re_axioms_has_N with_re_EN_axioms.
Proof.
  constructor. reflexivity.
Defined.

Definition with_re_EN : modal_logic_set nat :=
  with_re_proves with_re_EN_axioms.

Lemma with_re_EN_entailment :
  en_entailment with_re_EN.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_N with_re_EN_axioms_has_N).
Qed.

(** * EMC: five active source declarations *)

Definition with_re_EMC_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = C (Atom 0) (Atom 1).

Definition with_re_EMC_axioms_has_M :
    with_re_axioms_has_M with_re_EMC_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMC_axioms_has_C :
    with_re_axioms_has_C with_re_EMC_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - right; reflexivity.
Defined.

Definition with_re_EMC : modal_logic_set nat :=
  with_re_proves with_re_EMC_axioms.

Lemma with_re_EMC_entailment :
  emc_entailment with_re_EMC.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_M Nat.eq_dec with_re_EMC_axioms_has_M).
  - exact (with_re_has_C Nat.eq_dec with_re_EMC_axioms_has_C).
Qed.

(** * EMN: five active source declarations *)

Definition with_re_EMN_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = (@N nat).

Definition with_re_EMN_axioms_has_M :
    with_re_axioms_has_M with_re_EMN_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMN_axioms_has_N :
    with_re_axioms_has_N with_re_EMN_axioms.
Proof.
  constructor. right; reflexivity.
Defined.

Definition with_re_EMN : modal_logic_set nat :=
  with_re_proves with_re_EMN_axioms.

Lemma with_re_EMN_entailment :
  emn_entailment with_re_EMN.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_M Nat.eq_dec with_re_EMN_axioms_has_M).
  - exact (with_re_has_N with_re_EMN_axioms_has_N).
Qed.

(** * ECN: five active source declarations *)

Definition with_re_ECN_axioms : with_re_axiom nat :=
  fun p =>
    p = C (Atom 0) (Atom 1) \/
    p = (@N nat).

Definition with_re_ECN_axioms_has_C :
    with_re_axioms_has_C with_re_ECN_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_ECN_axioms_has_N :
    with_re_axioms_has_N with_re_ECN_axioms.
Proof.
  constructor. right; reflexivity.
Defined.

Definition with_re_ECN : modal_logic_set nat :=
  with_re_proves with_re_ECN_axioms.

Lemma with_re_ECN_entailment :
  ecn_entailment with_re_ECN.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_C Nat.eq_dec with_re_ECN_axioms_has_C).
  - exact (with_re_has_N with_re_ECN_axioms_has_N).
Qed.

(** * EK: four active source declarations *)

Definition with_re_EK_axioms : with_re_axiom nat :=
  fun p => p = K (Atom 0) (Atom 1).

Definition with_re_EK_axioms_has_K :
    with_re_axioms_has_K with_re_EK_axioms.
Proof.
  refine {| with_re_K_p := 0;
            with_re_K_q := 1;
            with_re_K_ne := _;
            with_re_K_mem := _ |}.
  - discriminate.
  - reflexivity.
Defined.

Definition with_re_EK : modal_logic_set nat :=
  with_re_proves with_re_EK_axioms.

Lemma with_re_EK_entailment :
  ek_entailment with_re_EK.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_K Nat.eq_dec with_re_EK_axioms_has_K).
Qed.
