(**
  The B- and Five-based replacement-of-equivalents systems from
  [Modal/Hilbert/WithRE/Basic.lean].

  This file independently ports the complete 27-declaration source surface
  for EB, ETB, ENTB, E5, and ET5.  The raw axiom predicates retain the
  source order and use natural-numbered atoms.  Classical entailment is
  supplied by the proved completeness of the faithful K/S/EC basis; no
  constructor is added to [with_re_proves].
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertWithRE
  HilbertWithREClassicalCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * EB: four active source declarations *)

Definition with_re_EB_axioms : with_re_axiom nat :=
  fun p => p = B (Atom 0).

Definition with_re_EB_axioms_has_B :
    with_re_axioms_has_B with_re_EB_axioms.
Proof.
  refine {| with_re_B_p := 0; with_re_B_mem := _ |}.
  reflexivity.
Defined.

Definition with_re_EB : modal_logic_set nat :=
  with_re_proves with_re_EB_axioms.

Lemma with_re_EB_entailment : eb_entailment with_re_EB.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_B Nat.eq_dec with_re_EB_axioms_has_B).
Qed.

(** * ETB: six active source declarations *)

Definition with_re_ETB_axioms : with_re_axiom nat :=
  fun p =>
    p = B (Atom 0) \/
    p = T (Atom 0).

Definition with_re_ETB_axioms_has_B :
    with_re_axioms_has_B with_re_ETB_axioms.
Proof.
  refine {| with_re_B_p := 0; with_re_B_mem := _ |}.
  left; reflexivity.
Defined.

Definition with_re_ETB_axioms_has_T :
    with_re_axioms_has_T with_re_ETB_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; reflexivity.
Defined.

Definition with_re_ETB : modal_logic_set nat :=
  with_re_proves with_re_ETB_axioms.

Lemma with_re_ETB_entailment : etb_entailment with_re_ETB.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_T Nat.eq_dec with_re_ETB_axioms_has_T).
  - exact (with_re_has_B Nat.eq_dec with_re_ETB_axioms_has_B).
Qed.

Lemma with_re_ETB_en_entailment : en_entailment with_re_ETB.
Proof.
  now apply EN_of_ETB, with_re_ETB_entailment.
Qed.

(** * ENTB: eight active source declarations *)

Definition with_re_ENTB_axioms : with_re_axiom nat :=
  fun p =>
    p = (@N nat) \/
    p = B (Atom 0) \/
    p = T (Atom 0).

Definition with_re_ENTB_axioms_has_N :
    with_re_axioms_has_N with_re_ENTB_axioms.
Proof.
  constructor. left; reflexivity.
Defined.

Definition with_re_ENTB_axioms_has_T :
    with_re_axioms_has_T with_re_ENTB_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; right; reflexivity.
Defined.

Definition with_re_ENTB_axioms_has_B :
    with_re_axioms_has_B with_re_ENTB_axioms.
Proof.
  refine {| with_re_B_p := 0; with_re_B_mem := _ |}.
  right; left; reflexivity.
Defined.

Definition with_re_ENTB : modal_logic_set nat :=
  with_re_proves with_re_ENTB_axioms.

Lemma with_re_ENTB_etb_entailment : etb_entailment with_re_ENTB.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_T Nat.eq_dec with_re_ENTB_axioms_has_T).
  - exact (with_re_has_B Nat.eq_dec with_re_ENTB_axioms_has_B).
Qed.

Lemma with_re_ENTB_en_entailment : en_entailment with_re_ENTB.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_N with_re_ENTB_axioms_has_N).
Qed.

Theorem with_re_ETB_equiv_ENTB :
  logic_equiv with_re_ETB with_re_ENTB.
Proof.
  split.
  - apply with_re_weaker_of_subset_axioms.
    intros p Hp; unfold with_re_ETB_axioms in Hp.
    unfold with_re_ENTB_axioms.
    destruct Hp as [-> | ->].
    + right; left; reflexivity.
    + right; right; reflexivity.
  - apply with_re_weaker_of_provable_axioms.
    intros p Hp; unfold with_re_ENTB_axioms in Hp.
    destruct Hp as [-> | [-> | ->]].
    + exact (has_N_axiom (en_N with_re_ETB_en_entailment)).
    + exact
        (has_B_axiom
          (with_re_has_B Nat.eq_dec with_re_ETB_axioms_has_B) (Atom 0)).
    + exact
        (has_T_axiom
          (with_re_has_T Nat.eq_dec with_re_ETB_axioms_has_T) (Atom 0)).
Qed.

(** * E5: four active source declarations *)

Definition with_re_E5_axioms : with_re_axiom nat :=
  fun p => p = Five (Atom 0).

Definition with_re_E5_axioms_has_Five :
    with_re_axioms_has_Five with_re_E5_axioms.
Proof.
  refine {| with_re_Five_p := 0; with_re_Five_mem := _ |}.
  reflexivity.
Defined.

Definition with_re_E5 : modal_logic_set nat :=
  with_re_proves with_re_E5_axioms.

Lemma with_re_E5_entailment : e5_entailment with_re_E5.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_Five Nat.eq_dec with_re_E5_axioms_has_Five).
Qed.

(** * ET5: five active source declarations *)

Definition with_re_ET5_axioms : with_re_axiom nat :=
  fun p =>
    p = T (Atom 0) \/
    p = Five (Atom 0).

Definition with_re_ET5_axioms_has_Five :
    with_re_axioms_has_Five with_re_ET5_axioms.
Proof.
  refine {| with_re_Five_p := 0; with_re_Five_mem := _ |}.
  right; reflexivity.
Defined.

Definition with_re_ET5_axioms_has_T :
    with_re_axioms_has_T with_re_ET5_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  left; reflexivity.
Defined.

Definition with_re_ET5 : modal_logic_set nat :=
  with_re_proves with_re_ET5_axioms.

Lemma with_re_ET5_entailment : et5_entailment with_re_ET5.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_T Nat.eq_dec with_re_ET5_axioms_has_T).
  - exact (with_re_has_Five Nat.eq_dec with_re_ET5_axioms_has_Five).
Qed.
