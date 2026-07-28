(**
  The raw K4 and K4n systems from Foundation's Normal catalogue.

  This file independently ports the exact ten-declaration tranche at lines
  419--433 of the pinned
  [Foundation/Modal/Hilbert/Normal/Basic.lean].  Both axiom predicates retain
  the source's natural-numbered raw templates: K at atoms 0 and 1, together
  with Four (or its n-indexed variant) at atom 0.  The templates enter the
  calculus only through same-atom endosubstitution.

  The source-facing structural records deliberately expose only the
  substitution-free K/K4 capability boundary.  Structural substitution is
  still available from [normal_hilbert_proves_substitute], but is not folded
  into a stronger extensional logic interface.  The final K4 compatibility
  bridge is constructorwise and uses no semantic completeness theorem.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertWithRE HilbertNormal HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems NormalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of K4 and K4n *)

Record structural_k4_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4_K : structural_k_entailment L0;
  structural_k4_Four : has_Four L0
}.

Record structural_k4n_entailment {AtomType} (n : nat)
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_k4n_K : structural_k_entailment L0;
  structural_k4n_FourN : has_FourN n L0
}.

(** * K4: five active source declarations *)

(** Source declaration 1/10: [K4.axioms]. *)
Definition normal_K4_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Four (Atom 0).

(** Source declaration 2/10: [K4.axioms.HasK]. *)
Definition normal_K4_axioms_has_K :
  raw_axioms_has_K normal_K4_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/10: [K4.axioms.HasFour]. *)
Definition normal_K4_axioms_has_Four :
  raw_axioms_has_Four normal_K4_axioms.
Proof.
  refine {| raw_Four_p := 0;
            raw_Four_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 4/10: the named logic [K4]. *)
Definition normal_K4 : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_K4_axioms.

(** Source declaration 5/10: [Entailment.K4 Modal.K4]. *)
Lemma normal_K4_entailment :
  structural_k4_entailment normal_K4.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_K4_axioms Nat.eq_dec
        normal_K4_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_Four nat normal_K4_axioms Nat.eq_dec
      normal_K4_axioms_has_Four).
Qed.

(** * K4n: five active source declarations *)

(** Source declaration 6/10: [K4n.axioms]. *)
Definition normal_K4n_axioms (n : nat) : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = FourN n (Atom 0).

(** Source declaration 7/10: [K4n.axioms.HasK]. *)
Definition normal_K4n_axioms_has_K (n : nat) :
  raw_axioms_has_K (normal_K4n_axioms n).
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 8/10: [K4n.axioms.HasFourN n]. *)
Definition normal_K4n_axioms_has_FourN (n : nat) :
  raw_axioms_has_FourN n (normal_K4n_axioms n).
Proof.
  refine {| raw_FourN_p := 0;
            raw_FourN_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 9/10: the indexed named logic [K4n n]. *)
Definition normal_K4n (n : nat) : modal_logic_set nat :=
  @normal_hilbert_proves nat (normal_K4n_axioms n).

(** Source declaration 10/10: [Entailment.K4n n (Modal.K4n n)]. *)
Lemma normal_K4n_entailment :
  forall n, structural_k4n_entailment n (normal_K4n n).
Proof.
  intro n; constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat (normal_K4n_axioms n) Nat.eq_dec
        (normal_K4n_axioms_has_K n)).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_FourN nat (normal_K4n_axioms n) n
      Nat.eq_dec (normal_K4n_axioms_has_FourN n)).
Qed.

(** * Fully syntactic compatibility with the established K4 calculus *)

Lemma normal_K4_to_K4_proves :
  logic_subset normal_K4 (@K4_proves nat).
Proof.
  intros p Hp; unfold normal_K4 in Hp; unfold K4_proves.
  induction Hp as
    [p sigma Hax
    |p q Hpq IHpq Hp IHp
    |p Hp IHp
    |p q
    |p q r
    |p q].
  - unfold normal_K4_axioms in Hax.
    destruct Hax as [Hax | Hax]; subst p; simpl.
    + apply Np_modal_K.
    + apply Np_extra. exists (sigma 0). reflexivity.
  - exact (Np_mp IHpq IHp).
  - exact (Np_nec IHp).
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
Qed.

Lemma K4_proves_to_normal_K4 :
  logic_subset (@K4_proves nat) normal_K4.
Proof.
  intros p Hp; unfold K4_proves in Hp; unfold normal_K4.
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
      (structural_k_K (structural_k4_K normal_K4_entailment)) p q).
  - destruct Hextra as [q ->].
    exact (has_Four_axiom (structural_k4_Four normal_K4_entailment) q).
  - exact (NH_mp IHpq IHp).
  - exact (NH_nec IHp).
Qed.

Theorem normal_K4_iff_K4_proves :
  forall p : formula nat,
    normal_K4 p <-> K4_proves p.
Proof.
  intro p; split.
  - apply normal_K4_to_K4_proves.
  - apply K4_proves_to_normal_K4.
Qed.

Definition normal_K4_equiv_K4_proves :
  logic_equiv normal_K4 (@K4_proves nat) :=
  conj normal_K4_to_K4_proves K4_proves_to_normal_K4.
