(**
  Four-based named replacement-of-equivalents calculi.

  This file independently ports the complete 29-declaration source surface
  for EMT4, EMNT4, EMC4, and EMCN4 at lines 369--425 of the pinned Foundation
  module [Modal/Hilbert/WithRE/Basic.lean].  Every raw axiom predicate keeps
  the source order over natural-numbered atoms, every raw capability witness
  is explicit, and the source's deliberately selective entailment adapters
  are preserved.

  The faithful six-constructor WithRE calculus is unchanged.  Its proved
  classical completeness supplies the E component of each source-facing
  adapter unconditionally.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertWithRE
  HilbertWithREClassicalCompleteness HilbertWithREBaseSystems
  HilbertWithREUnarySystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Minimal source-class support *)

(** Foundation's [Entailment.EMT4]: E4 together with T and M. *)
Record emt4_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  emt4_E4 : e4_entailment L;
  emt4_T : has_T L;
  emt4_M : has_M L
}.

(** Foundation's [Entailment.EMC4]: EMC together with Four. *)
Record emc4_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  emc4_EMC : emc_entailment L;
  emc4_Four : has_Four L
}.

(** * EMT4: six active source declarations *)

Definition with_re_EMT4_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0).

Definition with_re_EMT4_axioms_has_M :
    with_re_axioms_has_M with_re_EMT4_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMT4_axioms_has_T :
    with_re_axioms_has_T with_re_EMT4_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; left; reflexivity.
Defined.

Definition with_re_EMT4_axioms_has_Four :
    with_re_axioms_has_Four with_re_EMT4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; reflexivity.
Defined.

Definition with_re_EMT4 : modal_logic_set nat :=
  with_re_proves with_re_EMT4_axioms.

Lemma with_re_EMT4_entailment :
  emt4_entailment with_re_EMT4.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_Four Nat.eq_dec with_re_EMT4_axioms_has_Four).
  - exact (with_re_has_T Nat.eq_dec with_re_EMT4_axioms_has_T).
  - exact (with_re_has_M Nat.eq_dec with_re_EMT4_axioms_has_M).
Qed.

(** * EMNT4: ten active source declarations *)

Definition with_re_EMNT4_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = (@N nat) \/
    p = T (Atom 0) \/
    p = Four (Atom 0).

Definition with_re_EMNT4_axioms_has_M :
    with_re_axioms_has_M with_re_EMNT4_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMNT4_axioms_has_N :
    with_re_axioms_has_N with_re_EMNT4_axioms.
Proof.
  constructor. right; left; reflexivity.
Defined.

Definition with_re_EMNT4_axioms_has_T :
    with_re_axioms_has_T with_re_EMNT4_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; right; left; reflexivity.
Defined.

Definition with_re_EMNT4_axioms_has_Four :
    with_re_axioms_has_Four with_re_EMNT4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; right; reflexivity.
Defined.

Definition with_re_EMNT4 : modal_logic_set nat :=
  with_re_proves with_re_EMNT4_axioms.

Lemma with_re_EMNT4_em_entailment :
  em_entailment with_re_EMNT4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_M Nat.eq_dec with_re_EMNT4_axioms_has_M).
Qed.

Lemma with_re_EMNT4_en_entailment :
  en_entailment with_re_EMNT4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_N with_re_EMNT4_axioms_has_N).
Qed.

Lemma with_re_EMNT4_et_entailment :
  et_entailment with_re_EMNT4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_T Nat.eq_dec with_re_EMNT4_axioms_has_T).
Qed.

Lemma with_re_EMNT4_e4_entailment :
  e4_entailment with_re_EMNT4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_Four Nat.eq_dec with_re_EMNT4_axioms_has_Four).
Qed.

(** * EMC4: six active source declarations *)

Definition with_re_EMC4_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = C (Atom 0) (Atom 1) \/
    p = Four (Atom 0).

Definition with_re_EMC4_axioms_has_M :
    with_re_axioms_has_M with_re_EMC4_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMC4_axioms_has_C :
    with_re_axioms_has_C with_re_EMC4_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - right; left; reflexivity.
Defined.

Definition with_re_EMC4_axioms_has_Four :
    with_re_axioms_has_Four with_re_EMC4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; reflexivity.
Defined.

Definition with_re_EMC4 : modal_logic_set nat :=
  with_re_proves with_re_EMC4_axioms.

Lemma with_re_EMC4_entailment :
  emc4_entailment with_re_EMC4.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply with_re_e_entailment_from_basis.
      * exact (with_re_has_M Nat.eq_dec with_re_EMC4_axioms_has_M).
    + exact (with_re_has_C Nat.eq_dec with_re_EMC4_axioms_has_C).
  - exact (with_re_has_Four Nat.eq_dec with_re_EMC4_axioms_has_Four).
Qed.

(** * EMCN4: seven active source declarations *)

Definition with_re_EMCN4_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = C (Atom 0) (Atom 1) \/
    p = (@N nat) \/
    p = Four (Atom 0).

Definition with_re_EMCN4_axioms_has_M :
    with_re_axioms_has_M with_re_EMCN4_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMCN4_axioms_has_C :
    with_re_axioms_has_C with_re_EMCN4_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - right; left; reflexivity.
Defined.

Definition with_re_EMCN4_axioms_has_N :
    with_re_axioms_has_N with_re_EMCN4_axioms.
Proof.
  constructor. right; right; left; reflexivity.
Defined.

Definition with_re_EMCN4_axioms_has_Four :
    with_re_axioms_has_Four with_re_EMCN4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; right; reflexivity.
Defined.

Definition with_re_EMCN4 : modal_logic_set nat :=
  with_re_proves with_re_EMCN4_axioms.

Lemma with_re_EMCN4_emc_entailment :
  emc_entailment with_re_EMCN4.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_M Nat.eq_dec with_re_EMCN4_axioms_has_M).
  - exact (with_re_has_C Nat.eq_dec with_re_EMCN4_axioms_has_C).
Qed.
