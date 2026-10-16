(** Conventional Foundation-and-Choice endpoint for the public M253 theorem.

    Source pin: jeff87654/busy-beaver PR #20,
    0d544f2a2e3c18f12278441a74b7879f31cbe856.

    This file only composes already published theorems.  It does not
    internalize Coq's result as an arithmetic theorem of ZFC.  It was not
    kernel-checked in the environment in which this file was prepared;
    compile it with the load paths used by ZF/m253/check.py.

    The public name [zf253_halts_iff_ZFC] uses ZFc + Choice, where ZFc
    omits Regularity.  This explicit endpoint also includes Regularity.
*)
From M253E Require Import E2E253.
From ZFC Require Z_main.
From RegCon Require MinZF.

Definition FullZFC253 := fun phi =>
  (ZF.Std_iface.ZFc phi \/ phi = RegCon.MinZF.ax_reg') \/
  phi = ZFC.Z_wo.ax_ac.

Theorem zf253_halts_iff_FullZFC :
  M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0 <->
  @Undecidability.FOL.Deduction.FullND.tprv
    Undecidability.FOL.Syntax.BinSig.sig_empty
    Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
    Undecidability.FOL.Syntax.Core.falsity_on
    Undecidability.FOL.Syntax.Core.class
    FullZFC253
    Undecidability.FOL.Syntax.Core.falsity.
Proof.
  rewrite M253E.E2E253.zf253_halts_iff_ZF.
  unfold FullZFC253.
  symmetry.
  exact ZFC.Z_main.ZFCReg_equicons.
Qed.

Corollary zf253_nonhalting_iff_FullZFC_consistency :
  ~ M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0 <->
  ~ @Undecidability.FOL.Deduction.FullND.tprv
    Undecidability.FOL.Syntax.BinSig.sig_empty
    Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
    Undecidability.FOL.Syntax.Core.falsity_on
    Undecidability.FOL.Syntax.Core.class
    FullZFC253
    Undecidability.FOL.Syntax.Core.falsity.
Proof.
  rewrite zf253_halts_iff_FullZFC.
  reflexivity.
Qed.

Print Assumptions zf253_halts_iff_FullZFC.
Print Assumptions zf253_nonhalting_iff_FullZFC_consistency.
