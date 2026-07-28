(**
  Unary and nullary named replacement-of-equivalents calculi.

  This file independently ports the complete 55-declaration source surface
  on lines 243--316 of the pinned Foundation module
  [Modal/Hilbert/WithRE/Basic.lean].  It covers E4, EN4, ET4, ENT4, ED, END,
  END4, EMND4, and EP.  Every raw axiom predicate, raw capability witness,
  logic alias, entailment adapter, and the E4-to-EN4 inclusion is retained.

  The small [e4_entailment] record below supplies the previously missing Coq
  counterpart of Foundation's [Entailment.E4] by combining this repository's
  existing [e_entailment] and [has_Four] records.  The faithful six-constructor
  WithRE calculus is unchanged; unconditional E structure is supplied by
  [with_re_e_entailment_from_basis].

  Two apparent target typos are preserved literally.  The instance inside
  the source's END4 block and the instance inside its EMND4 block both state
  [Entailment.END Modal.END], rather than targeting END4 and EMND4.  Their Coq
  counterparts therefore have explicit [_source_END_entailment] names and
  return [end_entailment with_re_END].
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertWithRE
  HilbertWithREClassicalCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The reusable counterpart of Foundation's [Entailment.E4].  This support
    declaration is shared by later catalogue batches. *)
Record e4_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  e4_E : e_entailment L;
  e4_Four : has_Four L
}.

(** * E4: four active source declarations *)

Definition with_re_E4_axioms : with_re_axiom nat :=
  fun p => p = Four (Atom 0).

Definition with_re_E4_axioms_has_Four :
    with_re_axioms_has_Four with_re_E4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  reflexivity.
Defined.

Definition with_re_E4 : modal_logic_set nat :=
  with_re_proves with_re_E4_axioms.

Lemma with_re_E4_e4_entailment :
  e4_entailment with_re_E4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_Four Nat.eq_dec with_re_E4_axioms_has_Four).
Qed.

(** * EN4: seven active source declarations *)

Definition with_re_EN4_axioms : with_re_axiom nat :=
  fun p => p = (@N nat) \/ p = Four (Atom 0).

Definition with_re_EN4_axioms_has_N :
    with_re_axioms_has_N with_re_EN4_axioms.
Proof.
  constructor. left; reflexivity.
Defined.

Definition with_re_EN4_axioms_has_Four :
    with_re_axioms_has_Four with_re_EN4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; reflexivity.
Defined.

Definition with_re_EN4 : modal_logic_set nat :=
  with_re_proves with_re_EN4_axioms.

Lemma with_re_EN4_en_entailment :
  en_entailment with_re_EN4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_N with_re_EN4_axioms_has_N).
Qed.

Lemma with_re_EN4_e4_entailment :
  e4_entailment with_re_EN4.
Proof.
  constructor.
  - exact (en_E with_re_EN4_en_entailment).
  - exact (with_re_has_Four Nat.eq_dec with_re_EN4_axioms_has_Four).
Qed.

Lemma with_re_E4_weaker_than_EN4 :
  logic_subset with_re_E4 with_re_EN4.
Proof.
  apply with_re_weaker_of_subset_axioms.
  intros p Hp.
  unfold with_re_E4_axioms in Hp.
  unfold with_re_EN4_axioms.
  right; exact Hp.
Qed.

(** * ET4: seven active source declarations *)

Definition with_re_ET4_axioms : with_re_axiom nat :=
  fun p => p = Four (Atom 0) \/ p = T (Atom 0).

Definition with_re_ET4_axioms_has_Four :
    with_re_axioms_has_Four with_re_ET4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  left; reflexivity.
Defined.

Definition with_re_ET4_axioms_has_T :
    with_re_axioms_has_T with_re_ET4_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; reflexivity.
Defined.

Definition with_re_ET4 : modal_logic_set nat :=
  with_re_proves with_re_ET4_axioms.

Lemma with_re_ET4_e_entailment :
  e_entailment with_re_ET4.
Proof. apply with_re_e_entailment_from_basis. Qed.

Lemma with_re_ET4_et_entailment :
  et_entailment with_re_ET4.
Proof.
  constructor.
  - exact with_re_ET4_e_entailment.
  - exact (with_re_has_T Nat.eq_dec with_re_ET4_axioms_has_T).
Qed.

Lemma with_re_ET4_e4_entailment :
  e4_entailment with_re_ET4.
Proof.
  constructor.
  - exact with_re_ET4_e_entailment.
  - exact (with_re_has_Four Nat.eq_dec with_re_ET4_axioms_has_Four).
Qed.

(** * ENT4: eight active source declarations *)

Definition with_re_ENT4_axioms : with_re_axiom nat :=
  fun p =>
    p = (@N nat) \/
    p = T (Atom 0) \/
    p = Four (Atom 0).

Definition with_re_ENT4_axioms_has_N :
    with_re_axioms_has_N with_re_ENT4_axioms.
Proof.
  constructor. left; reflexivity.
Defined.

Definition with_re_ENT4_axioms_has_T :
    with_re_axioms_has_T with_re_ENT4_axioms.
Proof.
  refine {| with_re_T_p := 0; with_re_T_mem := _ |}.
  right; left; reflexivity.
Defined.

Definition with_re_ENT4_axioms_has_Four :
    with_re_axioms_has_Four with_re_ENT4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; reflexivity.
Defined.

Definition with_re_ENT4 : modal_logic_set nat :=
  with_re_proves with_re_ENT4_axioms.

Lemma with_re_ENT4_en_entailment :
  en_entailment with_re_ENT4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_N with_re_ENT4_axioms_has_N).
Qed.

Lemma with_re_ENT4_et_entailment :
  et_entailment with_re_ENT4.
Proof.
  constructor.
  - exact (en_E with_re_ENT4_en_entailment).
  - exact (with_re_has_T Nat.eq_dec with_re_ENT4_axioms_has_T).
Qed.

Lemma with_re_ENT4_e4_entailment :
  e4_entailment with_re_ENT4.
Proof.
  constructor.
  - exact (en_E with_re_ENT4_en_entailment).
  - exact (with_re_has_Four Nat.eq_dec with_re_ENT4_axioms_has_Four).
Qed.

(** * ED: four active source declarations *)

Definition with_re_ED_axioms : with_re_axiom nat :=
  fun p => p = D (Atom 0).

Definition with_re_ED_axioms_has_D :
    with_re_axioms_has_D with_re_ED_axioms.
Proof.
  refine {| with_re_D_p := 0; with_re_D_mem := _ |}.
  reflexivity.
Defined.

Definition with_re_ED : modal_logic_set nat :=
  with_re_proves with_re_ED_axioms.

Lemma with_re_ED_has_D :
  has_D with_re_ED.
Proof.
  exact (with_re_has_D Nat.eq_dec with_re_ED_axioms_has_D).
Qed.

(** * END: five active source declarations *)

Definition with_re_END_axioms : with_re_axiom nat :=
  fun p => p = (@N nat) \/ p = D (Atom 0).

Definition with_re_END_axioms_has_N :
    with_re_axioms_has_N with_re_END_axioms.
Proof.
  constructor. left; reflexivity.
Defined.

Definition with_re_END_axioms_has_D :
    with_re_axioms_has_D with_re_END_axioms.
Proof.
  refine {| with_re_D_p := 0; with_re_D_mem := _ |}.
  right; reflexivity.
Defined.

Definition with_re_END : modal_logic_set nat :=
  with_re_proves with_re_END_axioms.

Lemma with_re_END_entailment :
  end_entailment with_re_END.
Proof.
  constructor.
  - constructor.
    + apply with_re_e_entailment_from_basis.
    + exact (with_re_has_N with_re_END_axioms_has_N).
  - exact (with_re_has_D Nat.eq_dec with_re_END_axioms_has_D).
Qed.

(** * END4: seven active source declarations *)

Definition with_re_END4_axioms : with_re_axiom nat :=
  fun p =>
    p = (@N nat) \/
    p = D (Atom 0) \/
    p = Four (Atom 0).

Definition with_re_END4_axioms_has_N :
    with_re_axioms_has_N with_re_END4_axioms.
Proof.
  constructor. left; reflexivity.
Defined.

Definition with_re_END4_axioms_has_D :
    with_re_axioms_has_D with_re_END4_axioms.
Proof.
  refine {| with_re_D_p := 0; with_re_D_mem := _ |}.
  right; left; reflexivity.
Defined.

Definition with_re_END4_axioms_has_Four :
    with_re_axioms_has_Four with_re_END4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; reflexivity.
Defined.

Definition with_re_END4 : modal_logic_set nat :=
  with_re_proves with_re_END4_axioms.

(** This deliberately mirrors source line 297's target [Modal.END]. *)
Lemma with_re_END4_source_END_entailment :
  end_entailment with_re_END.
Proof. exact with_re_END_entailment. Qed.

Lemma with_re_END4_e4_entailment :
  e4_entailment with_re_END4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_Four Nat.eq_dec with_re_END4_axioms_has_Four).
Qed.

(** * EMND4: nine active source declarations *)

Definition with_re_EMND4_axioms : with_re_axiom nat :=
  fun p =>
    p = M (Atom 0) (Atom 1) \/
    p = (@N nat) \/
    p = D (Atom 0) \/
    p = Four (Atom 0).

Definition with_re_EMND4_axioms_has_M :
    with_re_axioms_has_M with_re_EMND4_axioms.
Proof.
  refine {| with_re_M_p := 0;
            with_re_M_q := 1;
            with_re_M_ne := _;
            with_re_M_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

Definition with_re_EMND4_axioms_has_N :
    with_re_axioms_has_N with_re_EMND4_axioms.
Proof.
  constructor. right; left; reflexivity.
Defined.

Definition with_re_EMND4_axioms_has_D :
    with_re_axioms_has_D with_re_EMND4_axioms.
Proof.
  refine {| with_re_D_p := 0; with_re_D_mem := _ |}.
  right; right; left; reflexivity.
Defined.

Definition with_re_EMND4_axioms_has_Four :
    with_re_axioms_has_Four with_re_EMND4_axioms.
Proof.
  refine {| with_re_Four_p := 0; with_re_Four_mem := _ |}.
  right; right; right; reflexivity.
Defined.

Definition with_re_EMND4 : modal_logic_set nat :=
  with_re_proves with_re_EMND4_axioms.

(** This deliberately mirrors source line 308's target [Modal.END]. *)
Lemma with_re_EMND4_source_END_entailment :
  end_entailment with_re_END.
Proof. exact with_re_END_entailment. Qed.

Lemma with_re_EMND4_em_entailment :
  em_entailment with_re_EMND4.
Proof.
  constructor.
  - apply with_re_e_entailment_from_basis.
  - exact (with_re_has_M Nat.eq_dec with_re_EMND4_axioms_has_M).
Qed.

Lemma with_re_EMND4_e4_entailment :
  e4_entailment with_re_EMND4.
Proof.
  constructor.
  - exact (em_E with_re_EMND4_em_entailment).
  - exact (with_re_has_Four Nat.eq_dec with_re_EMND4_axioms_has_Four).
Qed.

(** * EP: four active source declarations *)

Definition with_re_EP_axioms : with_re_axiom nat :=
  fun p => p = (@P nat).

Definition with_re_EP_axioms_has_P :
    with_re_axioms_has_P with_re_EP_axioms.
Proof.
  constructor. reflexivity.
Defined.

Definition with_re_EP : modal_logic_set nat :=
  with_re_proves with_re_EP_axioms.

Lemma with_re_EP_has_P :
  has_P with_re_EP.
Proof.
  exact (with_re_has_P with_re_EP_axioms_has_P).
Qed.
