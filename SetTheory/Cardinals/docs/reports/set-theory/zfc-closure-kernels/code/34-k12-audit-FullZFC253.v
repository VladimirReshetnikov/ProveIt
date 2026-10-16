(** * FullZFC253: the public 253-state table and ZFC including Foundation.

    Source dependency: jeff87654/busy-beaver PR #20, head
      0d544f2a2e3c18f12278441a74b7879f31cbe856
    Literal table SHA256:
      84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95

    This wrapper adds no machine states and no assumptions.  The existing
    E2E253 theorem relates the machine to closed ZF without Foundation.
    ZFCReg_equicons already supplies the refutation equivalence with closed
    ZF plus both Foundation (ax_reg') and Choice (ax_ac).

    The statements below are external propositions in Coq about finite
    object-theory derivations.  They are not a syntactic ZFC proof object
    of an arithmetized formula, and they do not prove consistency.

    Verification status for this wrapper: source reviewed, NOT separately
    kernel rebuilt in the current environment (no Coq executable installed).
    Its upstream dependency tree has a successful public Coq 8.20.1 CI run.

    Compile from the PR #20 repository after its complete checker passes;
    use the -Q roots printed by check_wrapper.py --command. *)

From Undecidability.FOL Require Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From RegCon Require MinZF.
From M253E Require E2E253.
From ZFC Require Z_main.

(** Exact object-theory predicate: closed ZF, Foundation, and Choice. *)
Definition Full_ZFC :=
  fun phi =>
    (ZF.Std_iface.ZFc phi \/
       phi = RegCon.MinZF.ax_reg') \/
    phi = ZFC.Z_wo.ax_ac.

Definition Refutable_full_ZFC : Prop :=
  @Undecidability.FOL.Deduction.FullND.tprv
    Undecidability.FOL.Syntax.BinSig.sig_empty
    Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
    Undecidability.FOL.Syntax.Core.falsity_on
    Undecidability.FOL.Syntax.Core.class
    Full_ZFC
    Undecidability.FOL.Syntax.Core.falsity.

(** Literal blank-tape halting, with every initializer state already counted. *)
Definition Public253_halts : Prop :=
  M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0.

Theorem zf253_halts_iff_full_ZFC_refutable :
  Public253_halts <-> Refutable_full_ZFC.
Proof.
  unfold Public253_halts, Refutable_full_ZFC, Full_ZFC.
  split.
  - intro H.
    apply (proj2 ZFC.Z_main.ZFCReg_equicons).
    apply (proj1 M253E.E2E253.zf253_halts_iff_ZF).
    exact H.
  - intro H.
    apply (proj2 M253E.E2E253.zf253_halts_iff_ZF).
    apply (proj1 ZFC.Z_main.ZFCReg_equicons).
    exact H.
Qed.

Definition Consistent_full_ZFC : Prop := ~ Refutable_full_ZFC.

(** Negating the preceding biconditional requires no classical principle. *)
Theorem zf253_nonhalts_iff_full_ZFC_consistent :
  (~ Public253_halts) <-> Consistent_full_ZFC.
Proof.
  unfold Consistent_full_ZFC.
  split.
  - intros Hnonhalt Hrefutation.
    apply Hnonhalt.
    apply (proj2 zf253_halts_iff_full_ZFC_refutable).
    exact Hrefutation.
  - intros Hconsistent Hhalt.
    apply Hconsistent.
    apply (proj1 zf253_halts_iff_full_ZFC_refutable).
    exact Hhalt.
Qed.

Print Assumptions zf253_halts_iff_full_ZFC_refutable.
Print Assumptions zf253_nonhalts_iff_full_ZFC_consistent.
