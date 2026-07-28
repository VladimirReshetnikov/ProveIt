(**
  The raw KMcK and K4McK systems from Foundation's Normal catalogue.

  This file independently ports the exact twelve-declaration McKinsey
  tranche at lines 411--446 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Both named axiom predicates retain the
  source's natural-numbered raw templates: modal K at atoms 0 and 1,
  McKinsey at atom 0, and (for K4McK) Four at atom 0.  Those templates enter
  [normal_hilbert_proves] only through same-atom endosubstitution.

  The final source instance is represented by a constructive capability
  lift.  If an arbitrary raw normal Hilbert calculus already has the K
  structure and contains every theorem of the named K4McK calculus, then it
  inherits Four and McKinsey by applying that inclusion to the corresponding
  named theorems.  Coq's proposition-valued proofs need no analogue of the
  source's noncomputable proof-object selection.

  No semantic soundness or completeness theorem is used here, and no import
  of the later canonical McKinsey development is required.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertWithRE HilbertNormal HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems HilbertNormalTransitiveBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of KMcK and K4McK *)

Record structural_kmck_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kmck_K : structural_k_entailment L0;
  structural_kmck_McK : has_McK L0
}.

Record structural_k4mck_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4mck_K4 : structural_k4_entailment L0;
  structural_k4mck_McK : has_McK L0
}.

(** * KMcK: five active source declarations *)

(** Source declaration 1/12: [KMcK.axioms]. *)
Definition normal_KMcK_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = McK (Atom 0).

(** Source declaration 2/12: [KMcK.axioms.HasK]. *)
Definition normal_KMcK_axioms_has_K :
  raw_axioms_has_K normal_KMcK_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/12: [KMcK.axioms.HasMcK]. *)
Definition normal_KMcK_axioms_has_McK :
  raw_axioms_has_McK normal_KMcK_axioms.
Proof.
  refine {| raw_McK_p := 0;
            raw_McK_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 4/12: the named logic [KMcK]. *)
Definition normal_KMcK : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KMcK_axioms.

(** Source declaration 5/12: [Entailment.KMcK Modal.KMcK]. *)
Lemma normal_KMcK_entailment :
  structural_kmck_entailment normal_KMcK.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KMcK_axioms Nat.eq_dec
        normal_KMcK_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_McK nat normal_KMcK_axioms Nat.eq_dec
      normal_KMcK_axioms_has_McK).
Qed.

(** * K4McK: six active source declarations *)

(** Source declaration 6/12: [K4McK.axioms]. *)
Definition normal_K4McK_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0) \/
    p = McK (Atom 0).

(** Source declaration 7/12: [K4McK.axioms.HasK]. *)
Definition normal_K4McK_axioms_has_K :
  raw_axioms_has_K normal_K4McK_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 8/12: [K4McK.axioms.HasFour]. *)
Definition normal_K4McK_axioms_has_Four :
  raw_axioms_has_Four normal_K4McK_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 9/12: [K4McK.axioms.HasMcK]. *)
Definition normal_K4McK_axioms_has_McK :
  raw_axioms_has_McK normal_K4McK_axioms.
Proof.
  refine {| raw_McK_p := 0;
            raw_McK_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 10/12: the named logic [K4McK]. *)
Definition normal_K4McK : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4McK_axioms.

(** Source declaration 11/12: [Entailment.K4McK Modal.K4McK]. *)
Lemma normal_K4McK_entailment :
  structural_k4mck_entailment normal_K4McK.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_K4McK_axioms Nat.eq_dec
          normal_K4McK_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Four nat normal_K4McK_axioms Nat.eq_dec
        normal_K4McK_axioms_has_Four).
  - exact (@normal_hilbert_has_McK nat normal_K4McK_axioms Nat.eq_dec
      normal_K4McK_axioms_has_McK).
Qed.

(** * Generic K4McK capability lift *)

(** Source declaration 12/12: the generic [Entailment.K4McK] instance at
    lines 444--446.  Its two selected source proofs are exactly the following
    applications of theorem inclusion. *)
Lemma normal_K4McK_entailment_of_subset :
  forall (Ax : raw_modal_axiom nat),
    structural_k_entailment (@normal_hilbert_proves nat Ax) ->
    logic_subset normal_K4McK (@normal_hilbert_proves nat Ax) ->
    structural_k4mck_entailment (@normal_hilbert_proves nat Ax).
Proof.
  intros Ax HK Hsubset; constructor.
  - constructor.
    + exact HK.
    + constructor; intro p.
      apply Hsubset.
      exact (has_Four_axiom
        (structural_k4_Four
          (structural_k4mck_K4 normal_K4McK_entailment)) p).
  - constructor; intro p.
    apply Hsubset.
    exact (has_McK_axiom
      (structural_k4mck_McK normal_K4McK_entailment) p).
Qed.
