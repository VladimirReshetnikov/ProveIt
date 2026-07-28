(**
  The three named WithRE/normal-system equivalences.

  This is an independent Rocq port of the final three instances in the
  pinned Foundation module [Modal/Hilbert/WithRE_Normal.lean].  The proofs
  instantiate [with_re_normal_equiv_of_provable_generators] directly:

    - M, C, and N are derived in each normal target;
    - T and Four are supplied by the corresponding normal extra schemas;
    - modal K, T, and Four are available in the matching WithRE source; and
    - replacement and necessitation are derived from the two systems'
      entailment capabilities.

  The raw WithRE calculus contains only the Lukasiewicz K/S/EC basis.  The
  conditional proofs below expose its classical-completeness boundary; the
  final source-facing theorems discharge that boundary with the independent
  completeness theorem for the basis.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  NormalHilbert LogicInfrastructure EntailmentExtensions
  HilbertWithRE HilbertWithRESystems HilbertWithRENormal
  HilbertWithREClassicalCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** A substitution-closed normal Hilbert calculus has precisely the
    substitution-free K-entailment interface needed by the generic bridge. *)
Local Lemma normal_with_re_k_entailment :
  forall (Ax : modal_axiom_schema),
    schema_substitution_closed Ax ->
    k_entailment (@normal_proves Ax nat).
Proof.
  intros Ax Hclosed.
  pose proof (@normal_proves_logic_is_normal Ax Hclosed) as Hnormal.
  constructor.
  - exact (quasi_classical (normal_quasi Hnormal)).
  - exact (normal_nec Hnormal).
  - constructor. exact (quasi_modal_K (normal_quasi Hnormal)).
  - exact (quasi_dia_duality (normal_quasi Hnormal)).
Qed.

(** EMCN and normal K prove the same formulas, conditional only on the
    faithful WithRE propositional basis being classically complete. *)
Theorem with_re_EMCN_equiv_K_of_classical_complete :
  with_re_classical_complete with_re_EMCN_axioms ->
  logic_equiv with_re_EMCN (@K_normal_proves nat).
Proof.
  intro Hcomplete.
  pose proof
    (k_entailment_of_EMCN
      (with_re_EMCN_entailment_of_classical_complete Hcomplete))
    as Hwith_re_K.
  pose proof
    (@normal_with_re_k_entailment empty_schema
      empty_schema_substitution_closed) as Hnormal_K.
  pose proof (EMCN_of_k_entailment Hnormal_K) as Hnormal_EMCN.
  unfold K_normal_proves.
  eapply with_re_normal_equiv_of_provable_generators.
  - exact (e_replacement (e_entailment_of_k Hnormal_K)).
  - exact (k_necessitation Hwith_re_K).
  - intros p sigma Hp.
    unfold with_re_EMCN_axioms in Hp.
    destruct Hp as [-> | [-> | ->]]; simpl.
    + exact
        (has_M_axiom
          (em_M (emc_EM (emcn_EMC Hnormal_EMCN))) (sigma 0) (sigma 1)).
    + exact
        (has_C_axiom
          (emc_C (emcn_EMC Hnormal_EMCN)) (sigma 0) (sigma 1)).
    + exact (has_N_axiom (emcn_N Hnormal_EMCN)).
  - intros p Hgenerator; destruct Hgenerator as [p q | p Hp].
    + exact (has_K_axiom (k_axiom Hwith_re_K) p q).
    + contradiction.
Qed.

(** EMCNT and normal KT prove the same formulas under the corresponding
    classical-completeness premise. *)
Theorem with_re_EMCNT_equiv_KT_of_classical_complete :
  with_re_classical_complete with_re_EMCNT_axioms ->
  logic_equiv with_re_EMCNT (@KT_proves nat).
Proof.
  intro Hcomplete.
  pose proof
    (with_re_EMCNT_emc_entailment_of_classical_complete Hcomplete)
    as Hwith_re_EMC.
  pose proof
    (with_re_EMCNT_en_entailment_of_classical_complete Hcomplete)
    as Hwith_re_EN.
  assert (Hwith_re_EMCN : emcn_entailment with_re_EMCNT).
  { constructor; [exact Hwith_re_EMC | exact (en_N Hwith_re_EN)]. }
  pose proof (k_entailment_of_EMCN Hwith_re_EMCN) as Hwith_re_K.
  pose proof
    (@normal_with_re_k_entailment schema_T
      schema_T_substitution_closed) as Hnormal_K.
  pose proof (EMCN_of_k_entailment Hnormal_K) as Hnormal_EMCN.
  unfold KT_proves.
  eapply with_re_normal_equiv_of_provable_generators.
  - exact (e_replacement (e_entailment_of_k Hnormal_K)).
  - exact (k_necessitation Hwith_re_K).
  - intros p sigma Hp.
    unfold with_re_EMCNT_axioms in Hp.
    destruct Hp as [-> | [-> | [-> | ->]]]; simpl.
    + exact
        (has_M_axiom
          (em_M (emc_EM (emcn_EMC Hnormal_EMCN))) (sigma 0) (sigma 1)).
    + exact
        (has_C_axiom
          (emc_C (emcn_EMC Hnormal_EMCN)) (sigma 0) (sigma 1)).
    + exact (has_N_axiom (emcn_N Hnormal_EMCN)).
    + apply Np_extra. now exists (sigma 0).
  - intros p Hgenerator; destruct Hgenerator as [p q | p Hp].
    + exact (has_K_axiom (k_axiom Hwith_re_K) p q).
    + destruct Hp as [q ->].
      exact
        (has_T_axiom
          (with_re_has_T Nat.eq_dec with_re_EMCNT_axioms_has_T) q).
Qed.

(** EMCNT4 and normal S4 prove the same formulas under the corresponding
    classical-completeness premise. *)
Theorem with_re_EMCNT4_equiv_S4_of_classical_complete :
  with_re_classical_complete with_re_EMCNT4_axioms ->
  logic_equiv with_re_EMCNT4 (@S4_proves nat).
Proof.
  intro Hcomplete.
  pose proof
    (with_re_EMCNT4_emc_entailment_of_classical_complete Hcomplete)
    as Hwith_re_EMC.
  pose proof
    (with_re_EMCNT4_en_entailment_of_classical_complete Hcomplete)
    as Hwith_re_EN.
  assert (Hwith_re_EMCN : emcn_entailment with_re_EMCNT4).
  { constructor; [exact Hwith_re_EMC | exact (en_N Hwith_re_EN)]. }
  pose proof (k_entailment_of_EMCN Hwith_re_EMCN) as Hwith_re_K.
  assert (HS4_closed : schema_substitution_closed S4_schema).
  { apply schema_union_substitution_closed.
    - exact schema_T_substitution_closed.
    - exact schema_Four_substitution_closed. }
  pose proof
    (@normal_with_re_k_entailment S4_schema HS4_closed) as Hnormal_K.
  pose proof (EMCN_of_k_entailment Hnormal_K) as Hnormal_EMCN.
  unfold S4_proves.
  eapply with_re_normal_equiv_of_provable_generators.
  - exact (e_replacement (e_entailment_of_k Hnormal_K)).
  - exact (k_necessitation Hwith_re_K).
  - intros p sigma Hp.
    unfold with_re_EMCNT4_axioms in Hp.
    destruct Hp as [-> | [-> | [-> | [-> | ->]]]]; simpl.
    + exact
        (has_M_axiom
          (em_M (emc_EM (emcn_EMC Hnormal_EMCN))) (sigma 0) (sigma 1)).
    + exact
        (has_C_axiom
          (emc_C (emcn_EMC Hnormal_EMCN)) (sigma 0) (sigma 1)).
    + exact (has_N_axiom (emcn_N Hnormal_EMCN)).
    + apply Np_extra. left. now exists (sigma 0).
    + apply Np_extra. right. now exists (sigma 0).
  - intros p Hgenerator; destruct Hgenerator as [p q | p Hp].
    + exact (has_K_axiom (k_axiom Hwith_re_K) p q).
    + destruct Hp as [[q ->] | [q ->]].
      * exact
          (has_T_axiom
            (with_re_has_T Nat.eq_dec with_re_EMCNT4_axioms_has_T) q).
      * exact
          (has_Four_axiom
            (with_re_has_Four Nat.eq_dec
              with_re_EMCNT4_axioms_has_Four) q).
Qed.

(** * Unconditional source-facing equivalences *)

Theorem with_re_EMCN_equiv_K :
  logic_equiv with_re_EMCN (@K_normal_proves nat).
Proof.
  apply with_re_EMCN_equiv_K_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.

Theorem with_re_EMCNT_equiv_KT :
  logic_equiv with_re_EMCNT (@KT_proves nat).
Proof.
  apply with_re_EMCNT_equiv_KT_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.

Theorem with_re_EMCNT4_equiv_S4 :
  logic_equiv with_re_EMCNT4 (@S4_proves nat).
Proof.
  apply with_re_EMCNT4_equiv_S4_of_classical_complete.
  apply with_re_classical_complete_weaken.
Qed.
