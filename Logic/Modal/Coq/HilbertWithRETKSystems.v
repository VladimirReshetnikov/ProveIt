(**
  The T- and K-based named replacement-of-equivalents calculi.

  This file independently ports the complete 21-declaration source surface
  at lines 318--367 of the pinned Foundation module
  [Modal/Hilbert/WithRE/Basic.lean].  It covers ET, EMT, EMK, and EMCK,
  including the source's equivalences EMK = EMCK and EMC = EMCK.

  Every raw axiom predicate is fixed over natural-numbered atoms and every
  raw capability witness is retained.  The source-facing entailment adapters
  are unconditional by the classical-completeness theorem for the faithful
  six-constructor WithRE calculus.  Both equivalences use only the generic
  WithRE weakening principles: their nontrivial reverse directions derive C
  from EMK and K from EMC, respectively.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertWithRE
  HilbertWithREClassicalCompleteness HilbertWithREBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The reusable counterpart of Foundation's [Entailment.EMT]. *)
Record emt_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  emt_EM : em_entailment L;
  emt_T : has_T L
}.

(** * ET: four active source declarations *)

Definition with_re_ET_axioms : with_re_axiom nat :=
  fun p => p = T (Atom 0).

Definition with_re_ET_axioms_has_T :
    with_re_axioms_has_T with_re_ET_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  reflexivity.
Defined.

Definition with_re_ET : modal_logic_set nat :=
  with_re_proves with_re_ET_axioms.

Lemma with_re_ET_entailment : et_entailment with_re_ET.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_T Nat.eq_dec with_re_ET_axioms_has_T).
Qed.

(** * EMT: five active source declarations *)

Definition with_re_EMT_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = T (Atom 0).

Definition with_re_EMT_axioms_has_M :
    with_re_axioms_has_M with_re_EMT_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMT_axioms_has_T :
    with_re_axioms_has_T with_re_EMT_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; reflexivity.
Defined.

Definition with_re_EMT : modal_logic_set nat :=
  with_re_proves with_re_EMT_axioms.

Lemma with_re_EMT_entailment : emt_entailment with_re_EMT.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_M Nat.eq_dec with_re_EMT_axioms_has_M).
  - exact (with_re_has_T Nat.eq_dec with_re_EMT_axioms_has_T).
Qed.

(** * EMK: five active source declarations *)

Definition with_re_EMK_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = K (Atom 0) (Atom 1).

Definition with_re_EMK_axioms_has_M :
    with_re_axioms_has_M with_re_EMK_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMK_axioms_has_K :
    with_re_axioms_has_K with_re_EMK_axioms.
Proof.
  refine {| with_re_K_p := 0;
            with_re_K_q := 1;
            with_re_K_ne := _;
            with_re_K_mem := _ |}.
  - discriminate.
  - right; reflexivity.
Defined.

Definition with_re_EMK : modal_logic_set nat :=
  with_re_proves with_re_EMK_axioms.

Lemma with_re_EMK_entailment : emk_entailment with_re_EMK.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_M Nat.eq_dec with_re_EMK_axioms_has_M).
  - exact (with_re_has_K Nat.eq_dec with_re_EMK_axioms_has_K).
Qed.

(** * EMCK: seven active source declarations *)

Definition with_re_EMCK_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = C (Atom 0) (Atom 1) \/
    p = K (Atom 0) (Atom 1).

Definition with_re_EMCK_axioms_has_M :
    with_re_axioms_has_M with_re_EMCK_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMCK_axioms_has_C :
    with_re_axioms_has_C with_re_EMCK_axioms.
Proof.
  refine {| with_re_C_p := 0;
            with_re_C_q := 1;
            with_re_C_ne := _;
            with_re_C_mem := _ |}.
  - discriminate.
  - right; left; reflexivity.
Defined.

Definition with_re_EMCK_axioms_has_K :
    with_re_axioms_has_K with_re_EMCK_axioms.
Proof.
  refine {| with_re_K_p := 0;
            with_re_K_q := 1;
            with_re_K_ne := _;
            with_re_K_mem := _ |}.
  - discriminate.
  - right; right; reflexivity.
Defined.

Definition with_re_EMCK : modal_logic_set nat :=
  with_re_proves with_re_EMCK_axioms.

Theorem with_re_EMK_equiv_EMCK :
  logic_equiv with_re_EMK with_re_EMCK.
Proof.
  split.
  - apply with_re_weaker_of_subset_axioms.
    intros p Hp; unfold with_re_EMK_axioms in Hp.
    unfold with_re_EMCK_axioms.
    destruct Hp as [-> | ->].
    + left; reflexivity.
    + right; right; reflexivity.
  - apply with_re_weaker_of_provable_axioms.
    intros p Hp; unfold with_re_EMCK_axioms in Hp.
    destruct Hp as [-> | [-> | ->]].
    + exact
        (has_M_axiom (em_M (emk_EM with_re_EMK_entailment))
          (Atom 0) (Atom 1)).
    + exact
        (has_C_axiom (has_C_of_EMK with_re_EMK_entailment)
          (Atom 0) (Atom 1)).
    + exact
        (has_K_axiom (emk_K with_re_EMK_entailment)
          (Atom 0) (Atom 1)).
Qed.

Theorem with_re_EMC_equiv_EMCK :
  logic_equiv with_re_EMC with_re_EMCK.
Proof.
  split.
  - apply with_re_weaker_of_subset_axioms.
    intros p Hp; unfold with_re_EMC_axioms in Hp.
    unfold with_re_EMCK_axioms.
    destruct Hp as [-> | ->].
    + left; reflexivity.
    + right; left; reflexivity.
  - apply with_re_weaker_of_provable_axioms.
    intros p Hp; unfold with_re_EMCK_axioms in Hp.
    destruct Hp as [-> | [-> | ->]].
    + exact
        (has_M_axiom (em_M (emc_EM with_re_EMC_entailment))
          (Atom 0) (Atom 1)).
    + exact
        (has_C_axiom (emc_C with_re_EMC_entailment)
          (Atom 0) (Atom 1)).
    + exact
        (has_K_axiom (has_K_of_EMC with_re_EMC_entailment)
          (Atom 0) (Atom 1)).
Qed.
