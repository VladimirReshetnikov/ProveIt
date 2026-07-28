(**
  Classical normal Hilbert systems immediately following K, KT, and KD.

  This file independently ports the exact 23-declaration catalogue tranche
  at lines 370--409 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean]: KP (including KP = KD), KB, KDB, and
  KTB.  As in [HilbertNormalBaseSystems], each source axiom collection is
  retained as a predicate over formulas with natural-numbered atoms, and
  raw templates enter [normal_hilbert_proves] only through substitution.

  The KP/KD equivalence below is wholly proof-theoretic.  In particular, its
  two directions use only the Lukasiewicz Hilbert basis, modal K,
  necessitation, and the selected P or D axiom; neither Kripke semantics nor
  completeness enters the argument.  The source-facing structural records
  deliberately remain weaker than this repository's extensional
  [normal_logic] interface.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions HilbertAxiom HilbertWithRE HilbertNormal
  HilbertNormalAxiomAdapters NormalHilbert HilbertNormalBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the source entailment classes *)

Record structural_kp_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kp_K : structural_k_entailment L0;
  structural_kp_P : has_P L0
}.

Record structural_kb_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kb_K : structural_k_entailment L0;
  structural_kb_B : has_B L0
}.

Record structural_kdb_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_kdb_K : structural_k_entailment L0;
  structural_kdb_D : has_D L0;
  structural_kdb_B : has_B L0
}.

Record structural_ktb_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_ktb_K : structural_k_entailment L0;
  structural_ktb_T : has_T L0;
  structural_ktb_B : has_B L0
}.

(** * KP: six active source declarations *)

(** Source declaration 1/23: [KP.axioms]. *)
Definition normal_KP_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = (@P nat).

(** Source declaration 2/23: [KP.axioms.HasK]. *)
Definition normal_KP_axioms_has_K :
  raw_axioms_has_K normal_KP_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/23: [KP.axioms.HasP]. *)
Definition normal_KP_axioms_has_P :
  raw_axioms_has_P normal_KP_axioms.
Proof.
  constructor; right; reflexivity.
Defined.

(** Source declaration 4/23: the named logic [KP]. *)
Definition normal_KP : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KP_axioms.

(** Source declaration 5/23: [Entailment.KP Modal.KP]. *)
Lemma normal_KP_entailment :
  structural_kp_entailment normal_KP.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KP_axioms Nat.eq_dec
        normal_KP_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_P nat normal_KP_axioms
      normal_KP_axioms_has_P).
Qed.

(** The following local lemmas make every step in KP = KD syntactic. *)

Local Lemma normal_hilbert_embed_K_proves :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    has_K (@normal_hilbert_proves AtomType Ax) ->
    forall p, K_proves p -> normal_hilbert_proves Ax p.
Proof.
  intros AtomType Ax HK p Hp; induction Hp.
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
  - now apply (has_K_axiom HK).
  - exact (NH_mp IHHp1 IHHp2).
  - exact (NH_nec IHHp).
Qed.

Local Lemma K_proves_internal_compose :
  forall (AtomType : Type) (p q r : formula AtomType),
    K_proves
      (Imp (Imp p q)
        (Imp (Imp q r) (Imp p r))).
Proof.
  intros AtomType p q r.
  apply (proj1 (K_derives_empty_iff _)).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_assumption. right; left; reflexivity.
  - eapply Kd_mp.
    + apply Kd_assumption. right; right; left; reflexivity.
    + apply Kd_assumption. left; reflexivity.
Qed.

Local Lemma normal_hilbert_imp_trans :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (p q r : formula AtomType),
    normal_hilbert_proves Ax (Imp p q) ->
    normal_hilbert_proves Ax (Imp q r) ->
    normal_hilbert_proves Ax (Imp p r).
Proof.
  intros AtomType Ax p q r Hpq Hqr.
  exact (@normal_hilbert_under_mp AtomType Ax p q r
    (@normal_hilbert_imply_intro AtomType Ax p (Imp q r) Hqr) Hpq).
Qed.

Local Lemma normal_KD_proves_P : normal_KD P.
Proof.
  pose proof
    (has_D_axiom (structural_kd_D normal_KD_entailment) Bottom) as HD.
  pose proof
    (@normal_hilbert_identity nat normal_KD_axioms Bottom) as Htop.
  pose proof (NH_nec Htop) as Hbox_top.
  pose proof
    (@normal_hilbert_imply_intro nat normal_KD_axioms
      (Box Bottom) (Box (Neg Bottom)) Hbox_top) as Hbox_top_under.
  unfold P.
  exact (@normal_hilbert_under_mp nat normal_KD_axioms
    (Box Bottom) (Box (Neg Bottom)) Bottom HD Hbox_top_under).
Qed.

Local Lemma normal_KP_proves_D :
  forall p : formula nat, normal_KP (D p).
Proof.
  intro p.
  pose proof (structural_kp_K normal_KP_entailment) as Hbase.
  pose proof (structural_k_K Hbase) as HK.
  pose proof
    (@normal_hilbert_embed_K_proves nat normal_KP_axioms HK
      (Imp p (Neg (Neg p))) (K_proves_dni p)) as Hdni.
  pose proof (NH_nec Hdni) as Hbox_dni_theorem.
  pose proof
    (NH_mp (has_K_axiom HK p (Neg (Neg p))) Hbox_dni_theorem)
    as Hboxed_dni.
  pose proof (has_K_axiom HK (Neg p) Bottom) as HKneg.
  pose proof
    (@normal_hilbert_imp_trans nat normal_KP_axioms
      (Box p) (Box (Neg (Neg p)))
      (Imp (Box (Neg p)) (Box Bottom)) Hboxed_dni HKneg)
    as Hcurried.
  pose proof (has_P_axiom (structural_kp_P normal_KP_entailment)) as HP.
  pose proof
    (@normal_hilbert_embed_K_proves nat normal_KP_axioms HK
      (Imp (Imp (Box (Neg p)) (Box Bottom))
        (Imp (Imp (Box Bottom) Bottom)
          (Imp (Box (Neg p)) Bottom)))
      (K_proves_internal_compose
        (Box (Neg p)) (Box Bottom) Bottom)) as Hcompose.
  pose proof
    (@normal_hilbert_imply_intro nat normal_KP_axioms
      (Box p)
      (Imp (Imp (Box (Neg p)) (Box Bottom))
        (Imp (Imp (Box Bottom) Bottom)
          (Imp (Box (Neg p)) Bottom))) Hcompose)
    as Hcompose_under.
  pose proof
    (@normal_hilbert_under_mp nat normal_KP_axioms
      (Box p)
      (Imp (Box (Neg p)) (Box Bottom))
      (Imp (Imp (Box Bottom) Bottom)
        (Imp (Box (Neg p)) Bottom))
      Hcompose_under Hcurried) as Hwith_curried.
  pose proof
    (@normal_hilbert_imply_intro nat normal_KP_axioms
      (Box p) (Imp (Box Bottom) Bottom) HP) as HP_under.
  unfold D, Dia.
  exact (@normal_hilbert_under_mp nat normal_KP_axioms
    (Box p) (Imp (Box Bottom) Bottom)
    (Imp (Box (Neg p)) Bottom) Hwith_curried HP_under).
Qed.

Local Lemma normal_KP_to_normal_KD :
  logic_subset normal_KP normal_KD.
Proof.
  unfold normal_KP, normal_KD.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax; destruct Hax as [-> | ->].
  - exact (has_K_axiom
      (structural_k_K (structural_kd_K normal_KD_entailment))
      (Atom 0) (Atom 1)).
  - exact normal_KD_proves_P.
Qed.

Local Lemma normal_KD_to_normal_KP :
  logic_subset normal_KD normal_KP.
Proof.
  unfold normal_KD, normal_KP.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax; destruct Hax as [-> | ->].
  - exact (has_K_axiom
      (structural_k_K (structural_kp_K normal_KP_entailment))
      (Atom 0) (Atom 1)).
  - exact (normal_KP_proves_D (Atom 0)).
Qed.

(** Source declaration 6/23: [Modal.KP ≊ Modal.KD]. *)
Definition normal_KP_equiv_KD :
  logic_equiv normal_KP normal_KD :=
  conj normal_KP_to_normal_KD normal_KD_to_normal_KP.

(** * KB: five active source declarations *)

(** Source declaration 7/23: [KB.axioms]. *)
Definition normal_KB_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = B (Atom 0).

(** Source declaration 8/23: [KB.axioms.HasK]. *)
Definition normal_KB_axioms_has_K :
  raw_axioms_has_K normal_KB_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 9/23: [KB.axioms.HasB]. *)
Definition normal_KB_axioms_has_B :
  raw_axioms_has_B normal_KB_axioms.
Proof.
  refine {| raw_B_p := 0;
            raw_B_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 10/23: the named logic [KB]. *)
Definition normal_KB : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KB_axioms.

(** Source declaration 11/23: [Entailment.KB Modal.KB]. *)
Lemma normal_KB_entailment :
  structural_kb_entailment normal_KB.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KB_axioms Nat.eq_dec
        normal_KB_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_B nat normal_KB_axioms Nat.eq_dec
      normal_KB_axioms_has_B).
Qed.

(** * KDB: six active source declarations *)

(** Source declaration 12/23: [KDB.axioms]. *)
Definition normal_KDB_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = D (Atom 0) \/
    p = B (Atom 0).

(** Source declaration 13/23: [KDB.axioms.HasK]. *)
Definition normal_KDB_axioms_has_K :
  raw_axioms_has_K normal_KDB_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 14/23: [KDB.axioms.HasD]. *)
Definition normal_KDB_axioms_has_D :
  raw_axioms_has_D normal_KDB_axioms.
Proof.
  refine {| raw_D_p := 0;
            raw_D_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 15/23: [KDB.axioms.HasB]. *)
Definition normal_KDB_axioms_has_B :
  raw_axioms_has_B normal_KDB_axioms.
Proof.
  refine {| raw_B_p := 0;
            raw_B_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 16/23: the named logic [KDB]. *)
Definition normal_KDB : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KDB_axioms.

(** Source declaration 17/23: [Entailment.KDB Modal.KDB]. *)
Lemma normal_KDB_entailment :
  structural_kdb_entailment normal_KDB.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KDB_axioms Nat.eq_dec
        normal_KDB_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_D nat normal_KDB_axioms Nat.eq_dec
      normal_KDB_axioms_has_D).
  - exact (@normal_hilbert_has_B nat normal_KDB_axioms Nat.eq_dec
      normal_KDB_axioms_has_B).
Qed.

(** * KTB: six active source declarations *)

(** Source declaration 18/23: [KTB.axioms]. *)
Definition normal_KTB_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = B (Atom 0).

(** Source declaration 19/23: [KTB.axioms.HasK]. *)
Definition normal_KTB_axioms_has_K :
  raw_axioms_has_K normal_KTB_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 20/23: [KTB.axioms.HasT]. *)
Definition normal_KTB_axioms_has_T :
  raw_axioms_has_T normal_KTB_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 21/23: [KTB.axioms.HasB]. *)
Definition normal_KTB_axioms_has_B :
  raw_axioms_has_B normal_KTB_axioms.
Proof.
  refine {| raw_B_p := 0;
            raw_B_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 22/23: the named logic [KTB]. *)
Definition normal_KTB : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_KTB_axioms.

(** Source declaration 23/23: [Entailment.KTB Modal.KTB]. *)
Lemma normal_KTB_entailment :
  structural_ktb_entailment normal_KTB.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_KTB_axioms Nat.eq_dec
        normal_KTB_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_T nat normal_KTB_axioms Nat.eq_dec
      normal_KTB_axioms_has_T).
  - exact (@normal_hilbert_has_B nat normal_KTB_axioms Nat.eq_dec
      normal_KTB_axioms_has_B).
Qed.

(** * Constructorwise bridge for the already established KB calculus *)

Lemma normal_KB_to_KB_proves :
  logic_subset normal_KB (@KB_proves nat).
Proof.
  intros p Hp; unfold normal_KB in Hp; unfold KB_proves.
  induction Hp as
    [p sigma Hax
    |p q Hpq IHpq Hp IHp
    |p Hp IHp
    |p q
    |p q r
    |p q].
  - unfold normal_KB_axioms in Hax.
    destruct Hax as [Hax | Hax]; subst p; simpl.
    + apply Np_modal_K.
    + apply Np_extra. exists (sigma 0). reflexivity.
  - exact (Np_mp IHpq IHp).
  - exact (Np_nec IHp).
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
Qed.

Lemma KB_proves_to_normal_KB :
  logic_subset (@KB_proves nat) normal_KB.
Proof.
  intros p Hp; unfold KB_proves in Hp; unfold normal_KB.
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
      (structural_k_K (structural_kb_K normal_KB_entailment)) p q).
  - destruct Hextra as [q ->].
    exact (has_B_axiom (structural_kb_B normal_KB_entailment) q).
  - exact (NH_mp IHpq IHp).
  - exact (NH_nec IHp).
Qed.

Theorem normal_KB_iff_KB_proves :
  forall p : formula nat,
    normal_KB p <-> KB_proves p.
Proof.
  intro p; split.
  - apply normal_KB_to_KB_proves.
  - apply KB_proves_to_normal_KB.
Qed.

Definition normal_KB_equiv_KB_proves :
  logic_equiv normal_KB (@KB_proves nat) :=
  conj normal_KB_to_KB_proves KB_proves_to_normal_KB.
