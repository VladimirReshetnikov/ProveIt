(**
  The first three named raw normal Hilbert systems.

  This file independently ports the exact fifteen-declaration catalogue
  tranche at lines 338--368 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean]: K, KT, and KD.  Each source axiom set is
  retained as a predicate over formulas with natural-numbered atoms.  Raw
  templates enter [normal_hilbert_proves] only through same-atom
  endosubstitution, exactly as in Foundation.

  The source-facing entailment records below expose the constructive
  Lukasiewicz basis, modal K, definitional diamond duality, necessitation, and
  the selected T or D schema.  They deliberately do not replace that basis
  with this repository's stronger extensional [normal_logic].  Substitution
  remains available separately through [normal_hilbert_proves_substitute].

  The final section gives direct constructor translations to the older
  schema-polymorphic [K_normal_proves], [KT_proves], and [KD_proves]
  calculi.  These bridges are entirely syntactic: no soundness, semantic
  completeness, or classical metatheorem is involved.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertWithRE HilbertNormal
  HilbertNormalAxiomAdapters NormalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_k_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k_lukasiewicz : lukasiewicz_entailment L0;
  structural_k_K : has_K L0;
  structural_k_dia_duality : has_DiaDuality L0;
  structural_k_necessitation : necessitation L0
}.

Record structural_kt_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kt_K : structural_k_entailment L0;
  structural_kt_T : has_T L0
}.

Record structural_kd_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kd_K : structural_k_entailment L0;
  structural_kd_D : has_D L0
}.

Definition structural_k_of_normal {AtomType}
    {L0 : modal_logic_set AtomType}
    (HN : structural_normal_entailment L0)
    : structural_k_entailment L0 :=
  {| structural_k_lukasiewicz := structural_normal_lukasiewicz HN;
     structural_k_K := structural_normal_K HN;
     structural_k_dia_duality := structural_normal_dia_duality HN;
     structural_k_necessitation := structural_normal_necessitation HN |}.

(** * K: five active source declarations *)

(** Source declaration 1/15: [K.axioms]. *)
Definition normal_K_axioms : raw_modal_axiom nat :=
  fun p => p = K (Atom 0) (Atom 1).

(** Source declaration 2/15: [K.axioms.HasK]. *)
Definition normal_K_axioms_has_K :
  raw_axioms_has_K normal_K_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - reflexivity.
Defined.

(** Source declaration 3/15: the named logic [K]. *)
Definition normal_K : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K_axioms.

(** Source declaration 4/15: [Entailment.K Modal.K]. *)
Lemma normal_K_entailment :
  structural_k_entailment normal_K.
Proof.
  constructor.
  - apply normal_hilbert_lukasiewicz.
  - exact (@normal_hilbert_has_K nat normal_K_axioms Nat.eq_dec
      normal_K_axioms_has_K).
  - apply normal_hilbert_has_DiaDuality.
  - apply normal_hilbert_necessitation.
Qed.

(** Source declaration 5/15: K is weaker than every normal nat logic. *)
Lemma normal_K_weaker_than_structural_normal :
  forall (L0 : modal_logic_set nat),
    structural_normal_entailment L0 ->
    logic_subset normal_K L0.
Proof.
  intros L0 Hnormal p Hp; unfold normal_K in Hp.
  induction Hp as
    [p sigma Hax
    |p q Hpq IHpq Hp IHp
    |p Hp IHp
    |p q
    |p q r
    |p q].
  - unfold normal_K_axioms in Hax; subst p; simpl.
    exact (has_K_axiom (structural_normal_K Hnormal)
      (sigma 0) (sigma 1)).
  - exact (lukasiewicz_mp (structural_normal_lukasiewicz Hnormal)
      IHpq IHp).
  - exact (structural_normal_necessitation Hnormal IHp).
  - exact (lukasiewicz_imply_K
      (structural_normal_lukasiewicz Hnormal) p q).
  - exact (lukasiewicz_imply_S
      (structural_normal_lukasiewicz Hnormal) p q r).
  - exact (lukasiewicz_elim_contra
      (structural_normal_lukasiewicz Hnormal) p q).
Qed.

(** * KT: five active source declarations *)

(** Source declaration 6/15: [KT.axioms]. *)
Definition normal_KT_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0).

(** Source declaration 7/15: [KT.axioms.HasK]. *)
Definition normal_KT_axioms_has_K :
  raw_axioms_has_K normal_KT_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 8/15: [KT.axioms.HasT]. *)
Definition normal_KT_axioms_has_T :
  raw_axioms_has_T normal_KT_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 9/15: the named logic [KT]. *)
Definition normal_KT : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KT_axioms.

(** Source declaration 10/15: [Entailment.KT Modal.KT]. *)
Lemma normal_KT_entailment :
  structural_kt_entailment normal_KT.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KT_axioms Nat.eq_dec
        normal_KT_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_T nat normal_KT_axioms Nat.eq_dec
      normal_KT_axioms_has_T).
Qed.

(** * KD: five active source declarations *)

(** Source declaration 11/15: [KD.axioms]. *)
Definition normal_KD_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = D (Atom 0).

(** Source declaration 12/15: [KD.axioms.HasK]. *)
Definition normal_KD_axioms_has_K :
  raw_axioms_has_K normal_KD_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 13/15: [KD.axioms.HasD]. *)
Definition normal_KD_axioms_has_D :
  raw_axioms_has_D normal_KD_axioms.
Proof.
  refine {| raw_D_p := 0;
            raw_D_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 14/15: the named logic [KD]. *)
Definition normal_KD : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KD_axioms.

(** Source declaration 15/15: [Entailment.KD Modal.KD]. *)
Lemma normal_KD_entailment :
  structural_kd_entailment normal_KD.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KD_axioms Nat.eq_dec
        normal_KD_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_D nat normal_KD_axioms Nat.eq_dec
      normal_KD_axioms_has_D).
Qed.

(** * Fully syntactic bridges to the established calculi *)

Lemma normal_K_to_K_normal_proves :
  logic_subset normal_K (@K_normal_proves nat).
Proof.
  intros p Hp; unfold normal_K in Hp; unfold K_normal_proves.
  induction Hp as
    [p sigma Hax
    |p q Hpq IHpq Hp IHp
    |p Hp IHp
    |p q
    |p q r
    |p q].
  - unfold normal_K_axioms in Hax; subst p; simpl.
    apply Np_modal_K.
  - exact (Np_mp IHpq IHp).
  - exact (Np_nec IHp).
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
Qed.

Lemma K_normal_proves_to_normal_K :
  logic_subset (@K_normal_proves nat) normal_K.
Proof.
  intros p Hp; unfold K_normal_proves in Hp; unfold normal_K.
  induction Hp as
    [p q
    |p q r
    |p q
    |p q
    |p Hextra
    |p q Hpq IHpq Hp IHp
    |p Hp IHp].
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
  - exact (has_K_axiom (structural_k_K normal_K_entailment) p q).
  - contradiction.
  - exact (NH_mp IHpq IHp).
  - exact (NH_nec IHp).
Qed.

Theorem normal_K_iff_K_normal_proves :
  forall p : formula nat,
    normal_K p <-> K_normal_proves p.
Proof.
  intro p; split.
  - apply normal_K_to_K_normal_proves.
  - apply K_normal_proves_to_normal_K.
Qed.

Definition normal_K_equiv_K_normal_proves :
  logic_equiv normal_K (@K_normal_proves nat) :=
  conj normal_K_to_K_normal_proves K_normal_proves_to_normal_K.

Lemma normal_KT_to_KT_proves :
  logic_subset normal_KT (@KT_proves nat).
Proof.
  intros p Hp; unfold normal_KT in Hp; unfold KT_proves.
  induction Hp as
    [p sigma Hax
    |p q Hpq IHpq Hp IHp
    |p Hp IHp
    |p q
    |p q r
    |p q].
  - unfold normal_KT_axioms in Hax.
    destruct Hax as [Hax | Hax]; subst p; simpl.
    + apply Np_modal_K.
    + apply Np_extra. exists (sigma 0). reflexivity.
  - exact (Np_mp IHpq IHp).
  - exact (Np_nec IHp).
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
Qed.

Lemma KT_proves_to_normal_KT :
  logic_subset (@KT_proves nat) normal_KT.
Proof.
  intros p Hp; unfold KT_proves in Hp; unfold normal_KT.
  induction Hp as
    [p q
    |p q r
    |p q
    |p q
    |p Hextra
    |p q Hpq IHpq Hp IHp
    |p Hp IHp].
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
  - exact (has_K_axiom
      (structural_k_K (structural_kt_K normal_KT_entailment)) p q).
  - destruct Hextra as [q ->].
    exact (has_T_axiom (structural_kt_T normal_KT_entailment) q).
  - exact (NH_mp IHpq IHp).
  - exact (NH_nec IHp).
Qed.

Theorem normal_KT_iff_KT_proves :
  forall p : formula nat,
    normal_KT p <-> KT_proves p.
Proof.
  intro p; split.
  - apply normal_KT_to_KT_proves.
  - apply KT_proves_to_normal_KT.
Qed.

Definition normal_KT_equiv_KT_proves :
  logic_equiv normal_KT (@KT_proves nat) :=
  conj normal_KT_to_KT_proves KT_proves_to_normal_KT.

Lemma normal_KD_to_KD_proves :
  logic_subset normal_KD (@KD_proves nat).
Proof.
  intros p Hp; unfold normal_KD in Hp; unfold KD_proves.
  induction Hp as
    [p sigma Hax
    |p q Hpq IHpq Hp IHp
    |p Hp IHp
    |p q
    |p q r
    |p q].
  - unfold normal_KD_axioms in Hax.
    destruct Hax as [Hax | Hax]; subst p; simpl.
    + apply Np_modal_K.
    + apply Np_extra. exists (sigma 0). reflexivity.
  - exact (Np_mp IHpq IHp).
  - exact (Np_nec IHp).
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
Qed.

Lemma KD_proves_to_normal_KD :
  logic_subset (@KD_proves nat) normal_KD.
Proof.
  intros p Hp; unfold KD_proves in Hp; unfold normal_KD.
  induction Hp as
    [p q
    |p q r
    |p q
    |p q
    |p Hextra
    |p q Hpq IHpq Hp IHp
    |p Hp IHp].
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
  - exact (has_K_axiom
      (structural_k_K (structural_kd_K normal_KD_entailment)) p q).
  - destruct Hextra as [q ->].
    exact (has_D_axiom (structural_kd_D normal_KD_entailment) q).
  - exact (NH_mp IHpq IHp).
  - exact (NH_nec IHp).
Qed.

Theorem normal_KD_iff_KD_proves :
  forall p : formula nat,
    normal_KD p <-> KD_proves p.
Proof.
  intro p; split.
  - apply normal_KD_to_KD_proves.
  - apply KD_proves_to_normal_KD.
Qed.

Definition normal_KD_equiv_KD_proves :
  logic_equiv normal_KD (@KD_proves nat) :=
  conj normal_KD_to_KD_proves KD_proves_to_normal_KD.
