(**
  The raw S4 and S4McK systems from Foundation's Normal catalogue.

  This file independently ports the exact fifteen active declarations at
  lines 540--560 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Both axiom predicates retain the
  source's natural-numbered templates: modal K at atoms 0 and 1, with T,
  Four, and (for S4McK) McKinsey at atom 0.  A raw template enters
  [normal_hilbert_proves] only through a same-atom endosubstitution.

  The two source inclusions remain wholly syntactic.  K4 is included in S4
  by literal raw-axiom inclusion.  K4McK is included in S4McK through the
  source-facing provable-axiom principle: each of K, Four, and McKinsey is
  selected constructively from the target entailment record before generic
  substitution closure transports its instances.  No semantics, classical
  principle, or completeness theorem is imported.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertWithRE HilbertNormal HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems HilbertNormalTransitiveBaseSystems
  HilbertNormalMcKSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of S4 and S4McK *)

Record structural_s4_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4_K4 : structural_k4_entailment L0;
  structural_s4_T : has_T L0
}.

Record structural_s4mck_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4mck_K4McK : structural_k4mck_entailment L0;
  structural_s4mck_T : has_T L0
}.

(** * S4: seven active source declarations *)

(** Source declaration 1/15: [S4.axioms]. *)
Definition normal_S4_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0).

(** Source declaration 2/15: [S4.axioms.HasK]. *)
Definition normal_S4_axioms_has_K :
  raw_axioms_has_K normal_S4_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/15: [S4.axioms.HasT]. *)
Definition normal_S4_axioms_has_T :
  raw_axioms_has_T normal_S4_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/15: [S4.axioms.HasFour]. *)
Definition normal_S4_axioms_has_Four :
  raw_axioms_has_Four normal_S4_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 5/15: the named logic [S4]. *)
Definition normal_S4 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4_axioms.

(** Source declaration 6/15: [Entailment.S4 Modal.S4]. *)
Lemma normal_S4_entailment :
  structural_s4_entailment normal_S4.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_S4_axioms Nat.eq_dec
          normal_S4_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_Four nat normal_S4_axioms Nat.eq_dec
        normal_S4_axioms_has_Four).
  - exact (@normal_hilbert_has_T nat normal_S4_axioms Nat.eq_dec
      normal_S4_axioms_has_T).
Qed.

(** Source declaration 7/15: [Modal.K4 <= Modal.S4]. *)
Lemma normal_K4_weaker_than_normal_S4 :
  logic_subset normal_K4 normal_S4.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_K4_axioms in Hax.
  unfold normal_S4_axioms.
  destruct Hax as [Hax | Hax]; subst p.
  - left; reflexivity.
  - right; right; reflexivity.
Qed.

(** * S4McK: eight active source declarations *)

(** Source declaration 8/15: [S4McK.axioms]. *)
Definition normal_S4McK_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = McK (Atom 0).

(** Source declaration 9/15: [S4McK.axioms.HasK]. *)
Definition normal_S4McK_axioms_has_K :
  raw_axioms_has_K normal_S4McK_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 10/15: [S4McK.axioms.HasT]. *)
Definition normal_S4McK_axioms_has_T :
  raw_axioms_has_T normal_S4McK_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 11/15: [S4McK.axioms.HasFour]. *)
Definition normal_S4McK_axioms_has_Four :
  raw_axioms_has_Four normal_S4McK_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 12/15: [S4McK.axioms.HasMcK]. *)
Definition normal_S4McK_axioms_has_McK :
  raw_axioms_has_McK normal_S4McK_axioms.
Proof.
  refine {| raw_McK_p := 0;
            raw_McK_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 13/15: the named logic [S4McK]. *)
Definition normal_S4McK : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4McK_axioms.

(** Source declaration 14/15: [Entailment.S4McK Modal.S4McK]. *)
Lemma normal_S4McK_entailment :
  structural_s4mck_entailment normal_S4McK.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- apply normal_hilbert_lukasiewicz.
        -- exact (@normal_hilbert_has_K nat normal_S4McK_axioms Nat.eq_dec
            normal_S4McK_axioms_has_K).
        -- apply normal_hilbert_has_DiaDuality.
        -- apply normal_hilbert_necessitation.
      * exact (@normal_hilbert_has_Four nat normal_S4McK_axioms Nat.eq_dec
          normal_S4McK_axioms_has_Four).
    + exact (@normal_hilbert_has_McK nat normal_S4McK_axioms Nat.eq_dec
        normal_S4McK_axioms_has_McK).
  - exact (@normal_hilbert_has_T nat normal_S4McK_axioms Nat.eq_dec
      normal_S4McK_axioms_has_T).
Qed.

(** Source declaration 15/15: [Modal.K4McK <= Modal.S4McK].  This uses the
    exact provable-axiom weakening boundary selected by the source. *)
Lemma normal_K4McK_weaker_than_normal_S4McK :
  logic_subset normal_K4McK normal_S4McK.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4McK_axioms in Hax.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom
      (structural_k_K
        (structural_k4_K
          (structural_k4mck_K4
            (structural_s4mck_K4McK normal_S4McK_entailment))))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom
      (structural_k4_Four
        (structural_k4mck_K4
          (structural_s4mck_K4McK normal_S4McK_entailment)))
      (Atom 0)).
  - exact (has_McK_axiom
      (structural_k4mck_McK
        (structural_s4mck_K4McK normal_S4McK_entailment))
      (Atom 0)).
Qed.
