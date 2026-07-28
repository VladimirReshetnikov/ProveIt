(**
  The three named replacement-of-equivalents calculi used by
  [Modal/Hilbert/WithRE_Normal.lean].

  This file independently ports the complete 23-declaration source surface
  for EMCN, EMCNT, and EMCNT4 from the pinned Foundation module
  [Modal/Hilbert/WithRE/Basic.lean].  Each raw axiom predicate is fixed over
  natural-numbered atoms, and every source raw-capability witness is retained.

  The raw calculi are unconditional.  The completeness theorem for the
  faithful Lukasiewicz K/S/EC basis supplies unconditional source-facing
  composite entailment adapters; premise-parameterized helpers are retained
  to expose the dependency explicitly.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertWithRE
  HilbertWithREClassicalCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * EMCN: six active source declarations *)

Definition with_re_EMCN_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = C (Atom 0) (Atom 1) \/
    p = (@N nat).

Definition with_re_EMCN_axioms_has_M :
    with_re_axioms_has_M with_re_EMCN_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMCN_axioms_has_C :
    with_re_axioms_has_C with_re_EMCN_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - right; left; reflexivity.
Defined.

Definition with_re_EMCN_axioms_has_N :
    with_re_axioms_has_N with_re_EMCN_axioms.
Proof.
  constructor. right; right; reflexivity.
Defined.

Definition with_re_EMCN : modal_logic_set nat :=
  with_re_proves with_re_EMCN_axioms.

Lemma with_re_EMCN_entailment_of_classical_complete :
  with_re_classical_complete with_re_EMCN_axioms ->
  emcn_entailment with_re_EMCN.
Proof.
  intro Hcomplete.
  constructor.
  - constructor.
    + constructor.
      * now apply with_re_e_entailment.
      * exact (with_re_has_M Nat.eq_dec with_re_EMCN_axioms_has_M).
    + exact (with_re_has_C Nat.eq_dec with_re_EMCN_axioms_has_C).
  - exact (with_re_has_N with_re_EMCN_axioms_has_N).
Qed.

Lemma with_re_EMCN_entailment :
  emcn_entailment with_re_EMCN.
Proof.
  apply with_re_EMCN_entailment_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.

(** * EMCNT: eight active source declarations *)

Definition with_re_EMCNT_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = C (Atom 0) (Atom 1) \/
    p = (@N nat) \/
    p = T (Atom 0).

Definition with_re_EMCNT_axioms_has_M :
    with_re_axioms_has_M with_re_EMCNT_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMCNT_axioms_has_C :
    with_re_axioms_has_C with_re_EMCNT_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - right; left; reflexivity.
Defined.

Definition with_re_EMCNT_axioms_has_N :
    with_re_axioms_has_N with_re_EMCNT_axioms.
Proof.
  constructor. right; right; left; reflexivity.
Defined.

Definition with_re_EMCNT_axioms_has_T :
    with_re_axioms_has_T with_re_EMCNT_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; right; right; reflexivity.
Defined.

Definition with_re_EMCNT : modal_logic_set nat :=
  with_re_proves with_re_EMCNT_axioms.

Lemma with_re_EMCNT_emc_entailment_of_classical_complete :
  with_re_classical_complete with_re_EMCNT_axioms ->
  emc_entailment with_re_EMCNT.
Proof.
  intro Hcomplete.
  constructor.
  - constructor.
    + now apply with_re_e_entailment.
    + exact (with_re_has_M Nat.eq_dec with_re_EMCNT_axioms_has_M).
  - exact (with_re_has_C Nat.eq_dec with_re_EMCNT_axioms_has_C).
Qed.

Lemma with_re_EMCNT_emc_entailment :
  emc_entailment with_re_EMCNT.
Proof.
  apply with_re_EMCNT_emc_entailment_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.

Lemma with_re_EMCNT_en_entailment_of_classical_complete :
  with_re_classical_complete with_re_EMCNT_axioms ->
  en_entailment with_re_EMCNT.
Proof.
  intro Hcomplete; constructor.
  - now apply with_re_e_entailment.
  - exact (with_re_has_N with_re_EMCNT_axioms_has_N).
Qed.

Lemma with_re_EMCNT_en_entailment :
  en_entailment with_re_EMCNT.
Proof.
  apply with_re_EMCNT_en_entailment_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.

(** * EMCNT4: nine active source declarations *)

Definition with_re_EMCNT4_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = C (Atom 0) (Atom 1) \/
    p = (@N nat) \/
    p = T (Atom 0) \/
    p = Four (Atom 0).

Definition with_re_EMCNT4_axioms_has_M :
    with_re_axioms_has_M with_re_EMCNT4_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMCNT4_axioms_has_C :
    with_re_axioms_has_C with_re_EMCNT4_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - right; left; reflexivity.
Defined.

Definition with_re_EMCNT4_axioms_has_N :
    with_re_axioms_has_N with_re_EMCNT4_axioms.
Proof.
  constructor. right; right; left; reflexivity.
Defined.

Definition with_re_EMCNT4_axioms_has_T :
    with_re_axioms_has_T with_re_EMCNT4_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; right; right; left; reflexivity.
Defined.

Definition with_re_EMCNT4_axioms_has_Four :
    with_re_axioms_has_Four with_re_EMCNT4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; right; right; reflexivity.
Defined.

Definition with_re_EMCNT4 : modal_logic_set nat :=
  with_re_proves with_re_EMCNT4_axioms.

Lemma with_re_EMCNT4_emc_entailment_of_classical_complete :
  with_re_classical_complete with_re_EMCNT4_axioms ->
  emc_entailment with_re_EMCNT4.
Proof.
  intro Hcomplete.
  constructor.
  - constructor.
    + now apply with_re_e_entailment.
    + exact (with_re_has_M Nat.eq_dec with_re_EMCNT4_axioms_has_M).
  - exact (with_re_has_C Nat.eq_dec with_re_EMCNT4_axioms_has_C).
Qed.

Lemma with_re_EMCNT4_emc_entailment :
  emc_entailment with_re_EMCNT4.
Proof.
  apply with_re_EMCNT4_emc_entailment_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.

Lemma with_re_EMCNT4_en_entailment_of_classical_complete :
  with_re_classical_complete with_re_EMCNT4_axioms ->
  en_entailment with_re_EMCNT4.
Proof.
  intro Hcomplete; constructor.
  - now apply with_re_e_entailment.
  - exact (with_re_has_N with_re_EMCNT4_axioms_has_N).
Qed.

Lemma with_re_EMCNT4_en_entailment :
  en_entailment with_re_EMCNT4.
Proof.
  apply with_re_EMCNT4_en_entailment_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.
