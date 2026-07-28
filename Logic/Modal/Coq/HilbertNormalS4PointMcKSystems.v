(**
  The raw S4Point2McK, S4Point3McK, and S4Point4McK systems.

  This file independently ports the exact twenty-seven active declarations
  at lines 563--599 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Every raw predicate retains modal K at
  atoms 0 and 1 and the unary T, Four, and McKinsey templates at atom 0.
  Point2 and Point4 use atom 0; binary Point3 uses the distinct atoms 0 and
  1.  Templates enter [normal_hilbert_proves] only through same-atom
  endosubstitution.

  Each K4McK inclusion uses the source's provable-axiom weakening boundary.
  The K, Four, and McKinsey source templates are selected constructively from
  the target structural entailment bundle, after which the generic calculus
  supplies substitution closure.  No semantics, classical principle,
  admission, or completeness theorem is used.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertWithRE HilbertNormal
  HilbertNormalAxiomAdapters HilbertNormalBaseSystems
  HilbertNormalTransitiveBaseSystems HilbertNormalMcKSystems
  HilbertNormalS4Systems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the three source entailment classes *)

Record structural_s4point2mck_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4point2mck_S4McK : structural_s4mck_entailment L0;
  structural_s4point2mck_Point2 : has_Point2 L0
}.

Record structural_s4point3mck_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4point3mck_S4McK : structural_s4mck_entailment L0;
  structural_s4point3mck_Point3 : has_Point3 L0
}.

Record structural_s4point4mck_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s4point4mck_S4McK : structural_s4mck_entailment L0;
  structural_s4point4mck_Point4 : has_Point4 L0
}.

(** * S4Point2McK: nine active source declarations *)

(** Source declaration 1/27: [S4Point2McK.axioms]. *)
Definition normal_S4Point2McK_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = McK (Atom 0) \/
    p = Point2 (Atom 0).

(** Source declaration 2/27: [S4Point2McK.axioms.HasK]. *)
Definition normal_S4Point2McK_axioms_has_K :
  raw_axioms_has_K normal_S4Point2McK_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/27: [S4Point2McK.axioms.HasT]. *)
Definition normal_S4Point2McK_axioms_has_T :
  raw_axioms_has_T normal_S4Point2McK_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 4/27: [S4Point2McK.axioms.HasFour]. *)
Definition normal_S4Point2McK_axioms_has_Four :
  raw_axioms_has_Four normal_S4Point2McK_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 5/27: [S4Point2McK.axioms.HasMcK]. *)
Definition normal_S4Point2McK_axioms_has_McK :
  raw_axioms_has_McK normal_S4Point2McK_axioms.
Proof.
  refine {| raw_McK_p := 0;
            raw_McK_mem := _ |}.
  right; right; right; left; reflexivity.
Defined.

(** Source declaration 6/27: [S4Point2McK.axioms.HasPoint2]. *)
Definition normal_S4Point2McK_axioms_has_Point2 :
  raw_axioms_has_Point2 normal_S4Point2McK_axioms.
Proof.
  refine {| raw_Point2_p := 0;
            raw_Point2_mem := _ |}.
  right; right; right; right; reflexivity.
Defined.

(** Source declaration 7/27: the named logic [S4Point2McK]. *)
Definition normal_S4Point2McK : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4Point2McK_axioms.

(** Source declaration 8/27:
    [Entailment.S4Point2McK Modal.S4Point2McK]. *)
Lemma normal_S4Point2McK_entailment :
  structural_s4point2mck_entailment normal_S4Point2McK.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- constructor.
           ++ apply normal_hilbert_lukasiewicz.
           ++ exact (@normal_hilbert_has_K nat normal_S4Point2McK_axioms
                Nat.eq_dec normal_S4Point2McK_axioms_has_K).
           ++ apply normal_hilbert_has_DiaDuality.
           ++ apply normal_hilbert_necessitation.
        -- exact (@normal_hilbert_has_Four nat normal_S4Point2McK_axioms
             Nat.eq_dec normal_S4Point2McK_axioms_has_Four).
      * exact (@normal_hilbert_has_McK nat normal_S4Point2McK_axioms
          Nat.eq_dec normal_S4Point2McK_axioms_has_McK).
    + exact (@normal_hilbert_has_T nat normal_S4Point2McK_axioms
        Nat.eq_dec normal_S4Point2McK_axioms_has_T).
  - exact (@normal_hilbert_has_Point2 nat normal_S4Point2McK_axioms
      Nat.eq_dec normal_S4Point2McK_axioms_has_Point2).
Qed.

(** Source declaration 9/27:
    [Modal.K4McK <= Modal.S4Point2McK]. *)
Lemma normal_K4McK_weaker_than_normal_S4Point2McK :
  logic_subset normal_K4McK normal_S4Point2McK.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4McK_axioms in Hax.
  pose proof
    (structural_s4mck_K4McK
      (structural_s4point2mck_S4McK
        normal_S4Point2McK_entailment)) as Hbase.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_k4_K (structural_k4mck_K4 Hbase)))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom
      (structural_k4_Four (structural_k4mck_K4 Hbase)) (Atom 0)).
  - exact (has_McK_axiom (structural_k4mck_McK Hbase) (Atom 0)).
Qed.

(** * S4Point3McK: nine active source declarations *)

(** Source declaration 10/27: [S4Point3McK.axioms]. *)
Definition normal_S4Point3McK_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = McK (Atom 0) \/
    p = Point3 (Atom 0) (Atom 1).

(** Source declaration 11/27: [S4Point3McK.axioms.HasK]. *)
Definition normal_S4Point3McK_axioms_has_K :
  raw_axioms_has_K normal_S4Point3McK_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 12/27: [S4Point3McK.axioms.HasT]. *)
Definition normal_S4Point3McK_axioms_has_T :
  raw_axioms_has_T normal_S4Point3McK_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 13/27: [S4Point3McK.axioms.HasFour]. *)
Definition normal_S4Point3McK_axioms_has_Four :
  raw_axioms_has_Four normal_S4Point3McK_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 14/27: [S4Point3McK.axioms.HasMcK]. *)
Definition normal_S4Point3McK_axioms_has_McK :
  raw_axioms_has_McK normal_S4Point3McK_axioms.
Proof.
  refine {| raw_McK_p := 0;
            raw_McK_mem := _ |}.
  right; right; right; left; reflexivity.
Defined.

(** Source declaration 15/27: [S4Point3McK.axioms.HasPoint3]. *)
Definition normal_S4Point3McK_axioms_has_Point3 :
  raw_axioms_has_Point3 normal_S4Point3McK_axioms.
Proof.
  refine {| raw_Point3_p := 0;
            raw_Point3_q := 1;
            raw_Point3_ne := _;
            raw_Point3_mem := _ |}.
  - discriminate.
  - right; right; right; right; reflexivity.
Defined.

(** Source declaration 16/27: the named logic [S4Point3McK]. *)
Definition normal_S4Point3McK : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4Point3McK_axioms.

(** Source declaration 17/27:
    [Entailment.S4Point3McK Modal.S4Point3McK]. *)
Lemma normal_S4Point3McK_entailment :
  structural_s4point3mck_entailment normal_S4Point3McK.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- constructor.
           ++ apply normal_hilbert_lukasiewicz.
           ++ exact (@normal_hilbert_has_K nat normal_S4Point3McK_axioms
                Nat.eq_dec normal_S4Point3McK_axioms_has_K).
           ++ apply normal_hilbert_has_DiaDuality.
           ++ apply normal_hilbert_necessitation.
        -- exact (@normal_hilbert_has_Four nat normal_S4Point3McK_axioms
             Nat.eq_dec normal_S4Point3McK_axioms_has_Four).
      * exact (@normal_hilbert_has_McK nat normal_S4Point3McK_axioms
          Nat.eq_dec normal_S4Point3McK_axioms_has_McK).
    + exact (@normal_hilbert_has_T nat normal_S4Point3McK_axioms
        Nat.eq_dec normal_S4Point3McK_axioms_has_T).
  - exact (@normal_hilbert_has_Point3 nat normal_S4Point3McK_axioms
      Nat.eq_dec normal_S4Point3McK_axioms_has_Point3).
Qed.

(** Source declaration 18/27:
    [Modal.K4McK <= Modal.S4Point3McK]. *)
Lemma normal_K4McK_weaker_than_normal_S4Point3McK :
  logic_subset normal_K4McK normal_S4Point3McK.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4McK_axioms in Hax.
  pose proof
    (structural_s4mck_K4McK
      (structural_s4point3mck_S4McK
        normal_S4Point3McK_entailment)) as Hbase.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_k4_K (structural_k4mck_K4 Hbase)))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom
      (structural_k4_Four (structural_k4mck_K4 Hbase)) (Atom 0)).
  - exact (has_McK_axiom (structural_k4mck_McK Hbase) (Atom 0)).
Qed.

(** * S4Point4McK: nine active source declarations *)

(** Source declaration 19/27: [S4Point4McK.axioms]. *)
Definition normal_S4Point4McK_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Four (Atom 0) \/
    p = McK (Atom 0) \/
    p = Point4 (Atom 0).

(** Source declaration 20/27: [S4Point4McK.axioms.HasK]. *)
Definition normal_S4Point4McK_axioms_has_K :
  raw_axioms_has_K normal_S4Point4McK_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 21/27: [S4Point4McK.axioms.HasT]. *)
Definition normal_S4Point4McK_axioms_has_T :
  raw_axioms_has_T normal_S4Point4McK_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 22/27: [S4Point4McK.axioms.HasFour]. *)
Definition normal_S4Point4McK_axioms_has_Four :
  raw_axioms_has_Four normal_S4Point4McK_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 23/27: [S4Point4McK.axioms.HasMcK]. *)
Definition normal_S4Point4McK_axioms_has_McK :
  raw_axioms_has_McK normal_S4Point4McK_axioms.
Proof.
  refine {| raw_McK_p := 0;
            raw_McK_mem := _ |}.
  right; right; right; left; reflexivity.
Defined.

(** Source declaration 24/27: [S4Point4McK.axioms.HasPoint4]. *)
Definition normal_S4Point4McK_axioms_has_Point4 :
  raw_axioms_has_Point4 normal_S4Point4McK_axioms.
Proof.
  refine {| raw_Point4_p := 0;
            raw_Point4_mem := _ |}.
  right; right; right; right; reflexivity.
Defined.

(** Source declaration 25/27: the named logic [S4Point4McK]. *)
Definition normal_S4Point4McK : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S4Point4McK_axioms.

(** Source declaration 26/27:
    [Entailment.S4Point4McK Modal.S4Point4McK]. *)
Lemma normal_S4Point4McK_entailment :
  structural_s4point4mck_entailment normal_S4Point4McK.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor.
        -- constructor.
           ++ apply normal_hilbert_lukasiewicz.
           ++ exact (@normal_hilbert_has_K nat normal_S4Point4McK_axioms
                Nat.eq_dec normal_S4Point4McK_axioms_has_K).
           ++ apply normal_hilbert_has_DiaDuality.
           ++ apply normal_hilbert_necessitation.
        -- exact (@normal_hilbert_has_Four nat normal_S4Point4McK_axioms
             Nat.eq_dec normal_S4Point4McK_axioms_has_Four).
      * exact (@normal_hilbert_has_McK nat normal_S4Point4McK_axioms
          Nat.eq_dec normal_S4Point4McK_axioms_has_McK).
    + exact (@normal_hilbert_has_T nat normal_S4Point4McK_axioms
        Nat.eq_dec normal_S4Point4McK_axioms_has_T).
  - exact (@normal_hilbert_has_Point4 nat normal_S4Point4McK_axioms
      Nat.eq_dec normal_S4Point4McK_axioms_has_Point4).
Qed.

(** Source declaration 27/27:
    [Modal.K4McK <= Modal.S4Point4McK]. *)
Lemma normal_K4McK_weaker_than_normal_S4Point4McK :
  logic_subset normal_K4McK normal_S4Point4McK.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4McK_axioms in Hax.
  pose proof
    (structural_s4mck_K4McK
      (structural_s4point4mck_S4McK
        normal_S4Point4McK_entailment)) as Hbase.
  destruct Hax as [Hax | [Hax | Hax]]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_k4_K (structural_k4mck_K4 Hbase)))
      (Atom 0) (Atom 1)).
  - exact (has_Four_axiom
      (structural_k4_Four (structural_k4mck_K4 Hbase)) (Atom 0)).
  - exact (has_McK_axiom (structural_k4mck_McK Hbase) (Atom 0)).
Qed.
