(**
  The terminal Ver, Triv, S5Grz, N, and NP systems from Foundation's Normal
  catalogue.

  This file independently ports the exact twenty-six active commands at
  lines 894--939 of the pinned Foundation module
  [Modal/Hilbert/Normal/Basic.lean].  Raw templates retain the source atoms:
  binary K uses the distinct atoms 0 and 1, while unary templates use atom
  0.  The N predicate is genuinely empty, and NP exposes only its formula-
  free P witness; neither system is silently strengthened with an absent K
  witness or named entailment bundle.

  The K4-to-Triv inclusion and the S5Grz/Triv equivalence are entirely
  proof-theoretic.  Triv derives Five directly as Tc at a diamond and derives
  Grz from T and Tc.  Conversely, S5Grz derives the Five dual, then DiaT,
  then Tc by closed K/S/EC proofs.  No semantics, completeness theorem,
  classical metaprinciple, choice principle, or admission is used.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure EntailmentExtensions
  HilbertAxiom HilbertWithRE HilbertNormal HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems HilbertNormalTransitiveBaseSystems
  HilbertNormalFiveSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Exact structural counterparts of the named entailment classes *)

Record structural_ver_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_ver_K : structural_k_entailment L0;
  structural_ver_Ver : has_Ver L0
}.

Record structural_triv_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_triv_K : structural_k_entailment L0;
  structural_triv_T : has_T L0;
  structural_triv_Tc : has_Tc L0
}.

Record structural_s5grz_entailment {AtomType}
    (L0 : modal_logic_set AtomType) : Prop := {
  structural_s5grz_S5 : structural_s5_entailment L0;
  structural_s5grz_Grz : has_Grz L0
}.

(** * Closed propositional tools used by the two-way equivalence *)

Local Lemma K_proves_contraposition :
  forall (a b : formula nat),
    K_proves (Imp (Imp a b) (Imp (Neg b) (Neg a))).
Proof.
  intros a b; unfold Neg.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp (Imp a b) (Imp (Imp b Bottom) (Imp a Bottom))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_assumption. right; left; reflexivity.
  - eapply Kd_mp.
    + apply Kd_assumption. right; right; left; reflexivity.
    + apply Kd_assumption. left; reflexivity.
Qed.

Local Lemma K_proves_under_contraposition :
  forall (a b c : formula nat),
    K_proves
      (Imp (Imp a (Imp b c))
        (Imp a (Imp (Neg c) (Neg b)))).
Proof.
  intros a b c; unfold Neg.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp (Imp a (Imp b c))
      (Imp a (Imp (Imp c Bottom) (Imp b Bottom)))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_assumption. right; left; reflexivity.
  - eapply Kd_mp.
    + eapply Kd_mp.
      * apply Kd_assumption. right; right; right; left; reflexivity.
      * apply Kd_assumption. right; right; left; reflexivity.
    + apply Kd_assumption. left; reflexivity.
Qed.

Local Lemma K_proves_nested_postcompose :
  forall (a b c d : formula nat),
    K_proves
      (Imp (Imp a (Imp b c))
        (Imp (Imp c d) (Imp a (Imp b d)))).
Proof.
  intros a b c d.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp (Imp a (Imp b c))
      (Imp (Imp c d) (Imp a (Imp b d)))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_assumption. right; right; left; reflexivity.
  - eapply Kd_mp.
    + eapply Kd_mp.
      * apply Kd_assumption. right; right; right; left; reflexivity.
      * apply Kd_assumption. right; left; reflexivity.
    + apply Kd_assumption. left; reflexivity.
Qed.

Local Lemma K_proves_swap_antecedents :
  forall (a b c : formula nat),
    K_proves
      (Imp (Imp a (Imp b c)) (Imp b (Imp a c))).
Proof.
  intros a b c.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp (Imp a (Imp b c)) (Imp b (Imp a c))))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - eapply Kd_mp.
    + apply Kd_assumption. right; right; left; reflexivity.
    + apply Kd_assumption. left; reflexivity.
  - apply Kd_assumption. right; left; reflexivity.
Qed.

Local Lemma K_proves_true_antecedent_elim :
  forall (a p : formula nat),
    K_proves (Imp a (Imp (Imp a p) p)).
Proof.
  intros a p.
  apply (proj1 (@K_derives_empty_iff nat
    (Imp a (Imp (Imp a p) p)))).
  apply K_derives_deduction.
  apply K_derives_deduction.
  eapply Kd_mp.
  - apply Kd_assumption. left; reflexivity.
  - apply Kd_assumption. right; left; reflexivity.
Qed.

(** Every structural K fragment contains the closed K calculus. *)
Local Lemma structural_K_contains_K_proves :
  forall (L0 : modal_logic_set nat),
    structural_k_entailment L0 ->
    logic_subset (@K_proves nat) L0.
Proof.
  intros L0 HK p Hp; induction Hp.
  - exact (lukasiewicz_imply_K
      (structural_k_lukasiewicz HK) p q).
  - exact (lukasiewicz_imply_S
      (structural_k_lukasiewicz HK) p q r).
  - exact (lukasiewicz_elim_contra
      (structural_k_lukasiewicz HK) p q).
  - exact (has_K_axiom (structural_k_K HK) p q).
  - exact (lukasiewicz_mp
      (structural_k_lukasiewicz HK) IHHp1 IHHp2).
  - exact (structural_k_necessitation HK IHHp).
Qed.

Local Lemma structural_K_box_regularity :
  forall (L0 : modal_logic_set nat),
    structural_k_entailment L0 ->
    forall p q, L0 (Imp p q) -> L0 (Imp (Box p) (Box q)).
Proof.
  intros L0 HK p q Hpq.
  eapply lukasiewicz_mp.
  - exact (structural_k_lukasiewicz HK).
  - exact (has_K_axiom (structural_k_K HK) p q).
  - exact (structural_k_necessitation HK Hpq).
Qed.

Local Lemma structural_K_imp_trans :
  forall (L0 : modal_logic_set nat),
    structural_k_entailment L0 ->
    forall p q r,
      L0 (Imp p q) -> L0 (Imp q r) -> L0 (Imp p r).
Proof.
  intros L0 HK p q r Hpq Hqr.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  eapply lukasiewicz_mp; [exact HLuk | | exact Hpq].
  eapply lukasiewicz_mp; [exact HLuk | |].
  - exact (lukasiewicz_imply_S HLuk p q r).
  - eapply lukasiewicz_mp; [exact HLuk | | exact Hqr].
    exact (lukasiewicz_imply_K HLuk (Imp q r) p).
Qed.

Local Lemma structural_K_contraposition :
  forall (L0 : modal_logic_set nat),
    structural_k_entailment L0 ->
    forall a b,
      L0 (Imp a b) -> L0 (Imp (Neg b) (Neg a)).
Proof.
  intros L0 HK a b Hab.
  eapply lukasiewicz_mp.
  - exact (structural_k_lukasiewicz HK).
  - apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_contraposition.
  - exact Hab.
Qed.

(** The dual consequence of Five, proved without the generic classical
    entailment layer: [diamond (box p) -> box p]. *)
Local Lemma structural_S5_proves_Five_dual :
  forall (L0 : modal_logic_set nat),
    structural_s5_entailment L0 ->
    forall p, L0 (Imp (Dia (Box p)) (Box p)).
Proof.
  intros L0 HS5 p.
  pose proof (structural_s5_K HS5) as HK.
  assert (Hbox_dni :
    L0 (Imp (Box p) (Box (Neg (Neg p))))).
  {
    apply (structural_K_box_regularity HK).
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_dni.
  }
  assert (Hdianeg_to_notbox :
    L0 (Imp (Dia (Neg p)) (Neg (Box p)))).
  {
    unfold Dia.
    exact (structural_K_contraposition HK Hbox_dni).
  }
  assert (Hboxed :
    L0 (Imp (Box (Dia (Neg p))) (Box (Neg (Box p))))).
  { exact (structural_K_box_regularity HK Hdianeg_to_notbox). }
  assert (Hleft :
    L0 (Imp (Dia (Box p)) (Neg (Box (Dia (Neg p)))))).
  {
    unfold Dia.
    exact (structural_K_contraposition HK Hboxed).
  }
  pose proof
    (has_Five_axiom (structural_s5_Five HS5) (Neg p)) as Hfive.
  assert (Hfive_contra :
    L0 (Imp (Neg (Box (Dia (Neg p)))) (Neg (Dia (Neg p))))).
  { exact (structural_K_contraposition HK Hfive). }
  assert (Hnotdia_to_box :
    L0 (Imp (Neg (Dia (Neg p))) (Box p))).
  {
    eapply structural_K_imp_trans; [exact HK | |].
    - apply (structural_K_contains_K_proves (L0 := L0) HK).
      unfold Dia.
      apply K_proves_dne.
    - apply (structural_K_box_regularity HK).
      apply (structural_K_contains_K_proves (L0 := L0) HK).
      apply K_proves_dne.
  }
  eapply structural_K_imp_trans; [exact HK | exact Hleft |].
  exact (structural_K_imp_trans HK Hfive_contra Hnotdia_to_box).
Qed.

(** The source S5Grz argument, kept at the structural raw boundary. *)
Local Lemma structural_S5Grz_proves_DiaT :
  forall (L0 : modal_logic_set nat),
    structural_s5grz_entailment L0 ->
    forall p, L0 (DiaT p).
Proof.
  intros L0 HS5Grz p.
  pose proof (structural_s5grz_S5 HS5Grz) as HS5.
  pose proof (structural_s5_K HS5) as HK.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  set (a := Box (Imp p (Box p))).
  set (b := Box (Neg (Box p))).
  set (c := Box (Neg p)).
  assert (Hcontra :
    L0 (Imp (Imp p (Box p)) (Imp (Neg (Box p)) (Neg p)))).
  {
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_contraposition.
  }
  assert (Hboxed_contra :
    L0 (Imp a (Box (Imp (Neg (Box p)) (Neg p))))).
  { unfold a. exact (structural_K_box_regularity HK Hcontra). }
  assert (Hdistributed : L0 (Imp a (Imp b c))).
  {
    unfold b, c.
    eapply structural_K_imp_trans; [exact HK | exact Hboxed_contra |].
    exact (has_K_axiom (structural_k_K HK)
      (Neg (Box p)) (Neg p)).
  }
  assert (Hdiamond_step :
    L0 (Imp a (Imp (Dia p) (Dia (Box p))))).
  {
    change (L0 (Imp a (Imp (Neg c) (Neg b)))).
    eapply lukasiewicz_mp; [exact HLuk | | exact Hdistributed].
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_under_contraposition.
  }
  assert (Hto_box : L0 (Imp a (Imp (Dia p) (Box p)))).
  {
    eapply lukasiewicz_mp; [exact HLuk | |].
    - eapply lukasiewicz_mp; [exact HLuk | | exact Hdiamond_step].
      apply (structural_K_contains_K_proves (L0 := L0) HK).
      apply K_proves_nested_postcompose.
    - apply structural_S5_proves_Five_dual. exact HS5.
  }
  assert (Hto_plain : L0 (Imp a (Imp (Dia p) p))).
  {
    eapply lukasiewicz_mp; [exact HLuk | |].
    - eapply lukasiewicz_mp; [exact HLuk | | exact Hto_box].
      apply (structural_K_contains_K_proves (L0 := L0) HK).
      apply K_proves_nested_postcompose.
    - exact (has_T_axiom (structural_s5_T HS5) p).
  }
  assert (Hswapped : L0 (Imp (Dia p) (Imp a p))).
  {
    eapply lukasiewicz_mp; [exact HLuk | | exact Hto_plain].
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_swap_antecedents.
  }
  assert (Hboxed :
    L0 (Imp (Box (Dia p)) (Box (Imp a p)))).
  { exact (structural_K_box_regularity HK Hswapped). }
  assert (Hboxdia_to_plain : L0 (Imp (Box (Dia p)) p)).
  {
    eapply structural_K_imp_trans; [exact HK | exact Hboxed |].
    unfold a. exact (has_Grz_axiom
      (structural_s5grz_Grz HS5Grz) p).
  }
  unfold DiaT.
  eapply structural_K_imp_trans; [exact HK | | exact Hboxdia_to_plain].
  exact (has_Five_axiom (structural_s5_Five HS5) p).
Qed.

(** DiaT at [not p], followed by contraposition and boxed DNE, yields Tc. *)
Local Lemma structural_S5Grz_has_Tc :
  forall (L0 : modal_logic_set nat),
    structural_s5grz_entailment L0 -> has_Tc L0.
Proof.
  intros L0 HS5Grz; constructor; intro p.
  pose proof (structural_s5_K (structural_s5grz_S5 HS5Grz)) as HK.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  pose proof
    (structural_S5Grz_proves_DiaT HS5Grz (Neg p)) as HdiaT.
  assert (Hfirst : L0 (Imp p (Box (Neg (Neg p))))).
  {
    eapply lukasiewicz_mp; [exact HLuk | | exact HdiaT].
    exact (lukasiewicz_elim_contra HLuk p (Box (Neg (Neg p)))).
  }
  assert (Hbox_dne :
    L0 (Imp (Box (Neg (Neg p))) (Box p))).
  {
    apply (structural_K_box_regularity HK).
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_dne.
  }
  unfold Tc. exact (structural_K_imp_trans HK Hfirst Hbox_dne).
Qed.

(** Triv proves Grz using only Tc, necessitation, and T. *)
Local Lemma structural_Triv_has_Grz :
  forall (L0 : modal_logic_set nat),
    structural_triv_entailment L0 -> has_Grz L0.
Proof.
  intros L0 HTriv; constructor; intro p.
  pose proof (structural_triv_K HTriv) as HK.
  pose proof (structural_k_lukasiewicz HK) as HLuk.
  set (a := Box (Imp p (Box p))).
  assert (Ha : L0 a).
  {
    unfold a.
    apply (structural_k_necessitation HK).
    exact (has_Tc_axiom (structural_triv_Tc HTriv) p).
  }
  assert (Helim : L0 (Imp (Imp a p) p)).
  {
    eapply lukasiewicz_mp; [exact HLuk | | exact Ha].
    apply (structural_K_contains_K_proves (L0 := L0) HK).
    apply K_proves_true_antecedent_elim.
  }
  unfold Grz.
  eapply structural_K_imp_trans; [exact HK | | exact Helim].
  exact (has_T_axiom (structural_triv_T HTriv) (Imp a p)).
Qed.

(** * Ver: five active source commands *)

(** Source declaration 1/26: [Ver.axioms]. *)
Definition normal_Ver_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = Ver (Atom 0).

(** Source declaration 2/26: [Ver.axioms.HasK]. *)
Definition normal_Ver_axioms_has_K :
  raw_axioms_has_K normal_Ver_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 3/26: [Ver.axioms.HasVer]. *)
Definition normal_Ver_axioms_has_Ver :
  raw_axioms_has_Ver normal_Ver_axioms.
Proof.
  refine {| raw_Ver_p := 0;
            raw_Ver_mem := _ |}.
  right; reflexivity.
Defined.

(** Source declaration 4/26: the named logic [Ver]. *)
Definition normal_Ver : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_Ver_axioms.

(** Source declaration 5/26: [Entailment.Ver Modal.Ver]. *)
Lemma normal_Ver_entailment :
  structural_ver_entailment normal_Ver.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_Ver_axioms Nat.eq_dec
        normal_Ver_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_Ver nat normal_Ver_axioms Nat.eq_dec
      normal_Ver_axioms_has_Ver).
Qed.

(** * Triv: seven active source commands *)

(** Source declaration 6/26: [Triv.axioms]. *)
Definition normal_Triv_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Tc (Atom 0).

(** Source declaration 7/26: [Triv.axioms.HasK]. *)
Definition normal_Triv_axioms_has_K :
  raw_axioms_has_K normal_Triv_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 8/26: [Triv.axioms.HasT]. *)
Definition normal_Triv_axioms_has_T :
  raw_axioms_has_T normal_Triv_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 9/26: [Triv.axioms.HasTc]. *)
Definition normal_Triv_axioms_has_Tc :
  raw_axioms_has_Tc normal_Triv_axioms.
Proof.
  refine {| raw_Tc_p := 0;
            raw_Tc_mem := _ |}.
  right; right; reflexivity.
Defined.

(** Source declaration 10/26: the named logic [Triv]. *)
Definition normal_Triv : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_Triv_axioms.

(** Source declaration 11/26: [Entailment.Triv Modal.Triv]. *)
Lemma normal_Triv_entailment :
  structural_triv_entailment normal_Triv.
Proof.
  constructor.
  - constructor.
    + apply normal_hilbert_lukasiewicz.
    + exact (@normal_hilbert_has_K nat normal_Triv_axioms Nat.eq_dec
        normal_Triv_axioms_has_K).
    + apply normal_hilbert_has_DiaDuality.
    + apply normal_hilbert_necessitation.
  - exact (@normal_hilbert_has_T nat normal_Triv_axioms Nat.eq_dec
      normal_Triv_axioms_has_T).
  - exact (@normal_hilbert_has_Tc nat normal_Triv_axioms Nat.eq_dec
      normal_Triv_axioms_has_Tc).
Qed.

(** Source declaration 12/26: [Modal.K4 <= Modal.Triv], through
    target-provable raw axioms.  The Four template is Tc at [box p]. *)
Lemma normal_K4_weaker_than_normal_Triv :
  logic_subset normal_K4 normal_Triv.
Proof.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hax. unfold normal_K4_axioms in Hax.
  destruct Hax as [Hax | Hax]; subst p.
  - exact (has_K_axiom
      (structural_k_K (structural_triv_K normal_Triv_entailment))
      (Atom 0) (Atom 1)).
  - exact (has_Tc_axiom (structural_triv_Tc normal_Triv_entailment)
      (Box (Atom 0))).
Qed.

(** * S5Grz: eight active source commands, in source order *)

(** Source declaration 13/26: [S5Grz.axioms]. *)
Definition normal_S5Grz_axioms : raw_modal_axiom nat :=
  fun p =>
    p = K (Atom 0) (Atom 1) \/
    p = T (Atom 0) \/
    p = Five (Atom 0) \/
    p = Grz (Atom 0).

(** Source declaration 14/26: the named logic [S5Grz].  Foundation places
    this abbreviation before the four raw witness instances. *)
Definition normal_S5Grz : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_S5Grz_axioms.

(** Source declaration 15/26: [S5Grz.axioms.HasK]. *)
Definition normal_S5Grz_axioms_has_K :
  raw_axioms_has_K normal_S5Grz_axioms.
Proof.
  refine {| raw_K_p := 0;
            raw_K_q := 1;
            raw_K_ne := _;
            raw_K_mem := _ |}.
  - discriminate.
  - left; reflexivity.
Defined.

(** Source declaration 16/26: [S5Grz.axioms.HasT]. *)
Definition normal_S5Grz_axioms_has_T :
  raw_axioms_has_T normal_S5Grz_axioms.
Proof.
  refine {| raw_T_p := 0;
            raw_T_mem := _ |}.
  right; left; reflexivity.
Defined.

(** Source declaration 17/26: [S5Grz.axioms.HasFive]. *)
Definition normal_S5Grz_axioms_has_Five :
  raw_axioms_has_Five normal_S5Grz_axioms.
Proof.
  refine {| raw_Five_p := 0;
            raw_Five_mem := _ |}.
  right; right; left; reflexivity.
Defined.

(** Source declaration 18/26: [S5Grz.axioms.HasGrz]. *)
Definition normal_S5Grz_axioms_has_Grz :
  raw_axioms_has_Grz normal_S5Grz_axioms.
Proof.
  refine {| raw_Grz_p := 0;
            raw_Grz_mem := _ |}.
  right; right; right; reflexivity.
Defined.

(** Source declaration 19/26: [Entailment.S5Grz Modal.S5Grz]. *)
Lemma normal_S5Grz_entailment :
  structural_s5grz_entailment normal_S5Grz.
Proof.
  constructor.
  - constructor.
    + constructor.
      * apply normal_hilbert_lukasiewicz.
      * exact (@normal_hilbert_has_K nat normal_S5Grz_axioms Nat.eq_dec
          normal_S5Grz_axioms_has_K).
      * apply normal_hilbert_has_DiaDuality.
      * apply normal_hilbert_necessitation.
    + exact (@normal_hilbert_has_T nat normal_S5Grz_axioms Nat.eq_dec
        normal_S5Grz_axioms_has_T).
    + exact (@normal_hilbert_has_Five nat normal_S5Grz_axioms Nat.eq_dec
        normal_S5Grz_axioms_has_Five).
  - exact (@normal_hilbert_has_Grz nat normal_S5Grz_axioms Nat.eq_dec
      normal_S5Grz_axioms_has_Grz).
Qed.

(** Source declaration 20/26: [Modal.S5Grz equiv Modal.Triv].  Both
    directions are target-provable-axiom folds, so the equivalence is exactly
    proof-theoretic rather than semantic. *)
Theorem normal_S5Grz_equiv_normal_Triv :
  logic_equiv normal_S5Grz normal_Triv.
Proof.
  split.
  - apply normal_hilbert_weaker_of_provable_axioms.
    intros p Hax. unfold normal_S5Grz_axioms in Hax.
    destruct Hax as [Hax | [Hax | [Hax | Hax]]]; subst p.
    + exact (has_K_axiom
        (structural_k_K (structural_triv_K normal_Triv_entailment))
        (Atom 0) (Atom 1)).
    + exact (has_T_axiom (structural_triv_T normal_Triv_entailment)
        (Atom 0)).
    + exact (has_Tc_axiom (structural_triv_Tc normal_Triv_entailment)
        (Dia (Atom 0))).
    + exact (has_Grz_axiom
        (structural_Triv_has_Grz normal_Triv_entailment) (Atom 0)).
  - apply normal_hilbert_weaker_of_provable_axioms.
    intros p Hax. unfold normal_Triv_axioms in Hax.
    destruct Hax as [Hax | [Hax | Hax]]; subst p.
    + exact (has_K_axiom
        (structural_k_K
          (structural_s5_K
            (structural_s5grz_S5 normal_S5Grz_entailment)))
        (Atom 0) (Atom 1)).
    + exact (has_T_axiom
        (structural_s5_T
          (structural_s5grz_S5 normal_S5Grz_entailment))
        (Atom 0)).
    + exact (has_Tc_axiom
        (structural_S5Grz_has_Tc normal_S5Grz_entailment) (Atom 0)).
Qed.

(** * N: exactly the two source abbreviations *)

(** Source declaration 21/26: the empty predicate [N.axioms]. *)
Definition normal_N_axioms : raw_modal_axiom nat :=
  fun _ => False.

(** Source declaration 22/26: the named logic [N].  The source declares no
    raw witness and no named entailment instance here. *)
Definition normal_N : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_N_axioms.

(** * NP: exactly four source commands *)

(** Source declaration 23/26: [NP.axioms]. *)
Definition normal_NP_axioms : raw_modal_axiom nat :=
  fun p => p = P.

(** Source declaration 24/26: [NP.axioms.HasP]. *)
Definition normal_NP_axioms_has_P :
  raw_axioms_has_P normal_NP_axioms.
Proof.
  constructor; reflexivity.
Defined.

(** Source declaration 25/26: the named logic [NP]. *)
Definition normal_NP : modal_logic_set nat :=
  @normal_hilbert_proves nat normal_NP_axioms.

(** Source declaration 26/26: [Entailment.HasAxiomP Modal.NP].  No broader
    NP entailment class is present in the source tranche. *)
Lemma normal_NP_has_P : has_P normal_NP.
Proof.
  exact (@normal_hilbert_has_P nat normal_NP_axioms
    normal_NP_axioms_has_P).
Qed.
