(**
  The raw GL, GL.2, and GL.3 systems from Foundation's Normal catalogue.

  This file independently ports the exact twenty active declarations at
  lines 654--683 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Each raw predicate retains modal K at
  the distinct atoms 0 and 1 and Loeb's axiom at atom 0.  GL.2 and GL.3 add
  respectively WeakPoint2 or WeakPoint3 at the same distinct atoms.  Raw
  templates enter [normal_hilbert_proves] only through same-atom
  endosubstitution.

  Foundation contains duplicate anonymous entailment instances for GL and
  GL.2.  They are represented below by separately named, definitionally
  equal aliases, so no source declaration is silently discarded.  The
  GL-to-GL.2 inclusion follows the source's literal raw-axiom subset.  This
  catalogue layer uses no semantics, completeness theorem, nonconstructive
  principle, or admission.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertNormal HilbertNormalAxiomAdapters HilbertNormalBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_gl_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_gl_K : structural_k_entailment L0;
  structural_gl_L : has_L L0
}.

Record structural_glpoint2_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_glpoint2_GL : structural_gl_entailment L0;
  structural_glpoint2_WeakPoint2 : has_WeakPoint2 L0
}.

Record structural_glpoint3_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_glpoint3_GL : structural_gl_entailment L0;
  structural_glpoint3_WeakPoint3 : has_WeakPoint3 L0
}.

(** * GL: six active source declarations *)

(** Source declaration 1/20: [GL.axioms]. *)
Definition normal_GL_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = L (Atom 0).

(** Source declaration 2/20: [GL.axioms.HasK]. *)
Definition normal_GL_axioms_has_K :
  raw_axioms_has_K normal_GL_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/20: [GL.axioms.HasL]. *)
Definition normal_GL_axioms_has_L :
  raw_axioms_has_L normal_GL_axioms.
Proof.
  refine {| raw_L_p := 0;
            raw_L_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 4/20: the named logic [GL]. *)
Definition normal_GL : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_GL_axioms.

(** Source declaration 5/20: the first [Entailment.GL Modal.GL]. *)
Lemma normal_GL_entailment :
  structural_gl_entailment normal_GL.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_GL_axioms Nat.eq_dec
        normal_GL_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_L nat normal_GL_axioms Nat.eq_dec
      normal_GL_axioms_has_L).
Qed.

(** Source declaration 6/20: the duplicate [Entailment.GL Modal.GL]. *)
Definition normal_GL_entailment_duplicate :
  structural_gl_entailment normal_GL :=
  normal_GL_entailment.

(** * GLPoint2: eight active source declarations *)

(** Source declaration 7/20: [GLPoint2.axioms]. *)
Definition normal_GLPoint2_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = L (Atom 0) \/
    p = WeakPoint2 (Atom 0) (Atom 1).

(** Source declaration 8/20: [GLPoint2.axioms.HasK]. *)
Definition normal_GLPoint2_axioms_has_K :
  raw_axioms_has_K normal_GLPoint2_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 9/20: [GLPoint2.axioms.HasL]. *)
Definition normal_GLPoint2_axioms_has_L :
  raw_axioms_has_L normal_GLPoint2_axioms.
Proof.
  refine {| raw_L_p := 0;
            raw_L_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 10/20: [GLPoint2.axioms.HasWeakPoint2]. *)
Definition normal_GLPoint2_axioms_has_WeakPoint2 :
  raw_axioms_has_WeakPoint2 normal_GLPoint2_axioms.
Proof.
  refine {| raw_WeakPoint2_p := 0;
            raw_WeakPoint2_q := 1;
            raw_WeakPoint2_ne := _;
            raw_WeakPoint2_mem := _ |}.
  - discriminate.
  - right; right; reflexivity.
Defined.

(** Source declaration 11/20: the named logic [GLPoint2]. *)
Definition normal_GLPoint2 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_GLPoint2_axioms.

(** Source declaration 12/20:
    the first [Entailment.GLPoint2 Modal.GLPoint2]. *)
Lemma normal_GLPoint2_entailment :
  structural_glpoint2_entailment normal_GLPoint2.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_GLPoint2_axioms Nat.eq_dec
          normal_GLPoint2_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_L nat normal_GLPoint2_axioms Nat.eq_dec
        normal_GLPoint2_axioms_has_L).
  - exact (@normal_hilbert_has_WeakPoint2 nat normal_GLPoint2_axioms
      Nat.eq_dec normal_GLPoint2_axioms_has_WeakPoint2).
Qed.

(** Source declaration 13/20:
    the duplicate [Entailment.GLPoint2 Modal.GLPoint2]. *)
Definition normal_GLPoint2_entailment_duplicate :
  structural_glpoint2_entailment normal_GLPoint2 :=
  normal_GLPoint2_entailment.

(** Source declaration 14/20: [Modal.GL <= Modal.GLPoint2]. *)
Lemma normal_GL_weaker_than_normal_GLPoint2 :
  logic_subset normal_GL normal_GLPoint2.
Proof.
  apply normal_hilbert_weaker_of_subset_axioms.
  intros p Hax. unfold normal_GL_axioms in Hax.
  unfold normal_GLPoint2_axioms.
  destruct Hax as [Hax | Hax]; subst p.
  - left; reflexivity.
  - right; left; reflexivity.
Qed.

(** * GLPoint3: six active source declarations *)

(** Source declaration 15/20: [GLPoint3.axioms]. *)
Definition normal_GLPoint3_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = L (Atom 0) \/
    p = WeakPoint3 (Atom 0) (Atom 1).

(** Source declaration 16/20: [GLPoint3.axioms.HasK]. *)
Definition normal_GLPoint3_axioms_has_K :
  raw_axioms_has_K normal_GLPoint3_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 17/20: [GLPoint3.axioms.HasL]. *)
Definition normal_GLPoint3_axioms_has_L :
  raw_axioms_has_L normal_GLPoint3_axioms.
Proof.
  refine {| raw_L_p := 0;
            raw_L_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 18/20: [GLPoint3.axioms.HasWeakPoint3]. *)
Definition normal_GLPoint3_axioms_has_WeakPoint3 :
  raw_axioms_has_WeakPoint3 normal_GLPoint3_axioms.
Proof.
  refine {| raw_WeakPoint3_p := 0;
            raw_WeakPoint3_q := 1;
            raw_WeakPoint3_ne := _;
            raw_WeakPoint3_mem := _ |}.
  - discriminate.
  - right; right; reflexivity.
Defined.

(** Source declaration 19/20: the named logic [GLPoint3]. *)
Definition normal_GLPoint3 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_GLPoint3_axioms.

(** Source declaration 20/20:
    [Entailment.GLPoint3 Modal.GLPoint3]. *)
Lemma normal_GLPoint3_entailment :
  structural_glpoint3_entailment normal_GLPoint3.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_GLPoint3_axioms Nat.eq_dec
          normal_GLPoint3_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_L nat normal_GLPoint3_axioms Nat.eq_dec
        normal_GLPoint3_axioms_has_L).
  - exact (@normal_hilbert_has_WeakPoint3 nat normal_GLPoint3_axioms
      Nat.eq_dec normal_GLPoint3_axioms_has_WeakPoint3).
Qed.
