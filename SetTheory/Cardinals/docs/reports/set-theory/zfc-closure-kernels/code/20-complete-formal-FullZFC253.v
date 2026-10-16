(** * FullZFC253: proposed endpoint composition for upstream PR 20.

    SOURCE ONLY. This file has not been compiled in the present environment.
    No new theorem or kernel acceptance is claimed for this file.

    Required upstream tree:
      mira-emmy/busy-beaver 0d544f2a2e3c18f12278441a74b7879f31cbe856
    Logical roots: the existing M253, M253E, ZF, ZFC and Undecidability roots.

    E2E253.v names its (ZFc + AC) endpoint ZFC; ZFc itself excludes
    Regularity. Z_main.ZFCReg_equicons already provides the exact finite-
    refutation equivalence with Regularity included. This file merely
    composes those two existing external statements.

    These are metatheoretic Coq propositions about finite derivations.
    They are NOT exported arithmetic proof-code transformers, a theorem
    formalized internally in ZFC, or a proof of consistency of ZFC.
*)
From Undecidability.FOL Require
  Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From Undecidability.FOL.Sets Require Import minZF.
From M253 Require TM253.
From M253E Require E2E253.
From ZF Require Std_iface.
From ZFC Require Z_wo Z_main.

Notation tprv := Undecidability.FOL.Deduction.FullND.tprv.
Notation sig0 := Undecidability.FOL.Syntax.BinSig.sig_empty.
Notation zfp := Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig.
Notation fon := Undecidability.FOL.Syntax.Core.falsity_on.
Notation cls := Undecidability.FOL.Syntax.Core.class.
Notation bot := Undecidability.FOL.Syntax.Core.falsity.

Theorem zf253_halts_iff_ZFC_with_Regularity :
  M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0 <->
  @tprv sig0 zfp fon cls
    (fun phi => (ZF.Std_iface.ZFc phi \/ phi = ax_reg') \/
                phi = ZFC.Z_wo.ax_ac) bot.
Proof.
  rewrite M253E.E2E253.zf253_halts_iff_ZF.
  symmetry. exact ZFC.Z_main.ZFCReg_equicons.
Qed.

Corollary zf253_nonhalting_iff_no_finite_standard_ZFC_refutation :
  (~ M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0) <->
  (~ @tprv sig0 zfp fon cls
    (fun phi => (ZF.Std_iface.ZFc phi \/ phi = ax_reg') \/
                phi = ZFC.Z_wo.ax_ac) bot).
Proof. rewrite zf253_halts_iff_ZFC_with_Regularity. reflexivity. Qed.

Print Assumptions zf253_halts_iff_ZFC_with_Regularity.
Print Assumptions zf253_nonhalting_iff_no_finite_standard_ZFC_refutation.
