(* Statement check: the type ascriptions fail to compile unless the theorems have exactly
   these statements.  ⊢TC is the library's classical natural deduction from a theory. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_iface.
From RegCon Require MinZF.
From ZFC Require Import Z_wo Z_main.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.

Check (ac_relcon :
  (fun phi => (Std_iface.ZFc phi \/ phi = MinZF.ax_reg') \/ phi = ax_ac) ⊢TC ⊥ ->
  (fun phi => Std_iface.ZFc phi \/ phi = MinZF.ax_reg') ⊢TC ⊥).
Check (ac_reg_relcon :
  (fun phi => (Std_iface.ZFc phi \/ phi = MinZF.ax_reg') \/ phi = ax_ac) ⊢TC ⊥ -> Std_iface.ZFc ⊢TC ⊥).
Check (zfc_relcon : (fun phi => Std_iface.ZFc phi \/ phi = ax_ac) ⊢TC ⊥ -> Std_iface.ZFc ⊢TC ⊥).
Check (ZFC_equicons : (fun phi => Std_iface.ZFc phi \/ phi = ax_ac) ⊢TC ⊥ <-> Std_iface.ZFc ⊢TC ⊥).
Check (ZFCReg_equicons :
  (fun phi => (Std_iface.ZFc phi \/ phi = MinZF.ax_reg') \/ phi = ax_ac) ⊢TC ⊥ <-> Std_iface.ZFc ⊢TC ⊥).
Print ax_ac.
Print ACmat.
Print MinZF.ax_reg'.
Print Std_iface.ZFc.
Print Std_iface.ZF0.
Print Std_iface.ZF0base.
Print Assumptions ac_relcon.
Print Assumptions ac_reg_relcon.
Print Assumptions zfc_relcon.
Print Assumptions ZFC_equicons.
Print Assumptions ZFCReg_equicons.
