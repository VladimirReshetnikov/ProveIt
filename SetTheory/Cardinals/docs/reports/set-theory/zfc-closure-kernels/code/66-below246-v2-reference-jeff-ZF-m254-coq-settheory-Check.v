(** Statement check for zf/m254/settheory: SIR (the 254-state machine's set theory), S0 = SIR
    without IR, ZF and ZFC are equiconsistent, at the object level in the library's ND.
    build.py prints CHECK PASS when every [Print Assumptions] is "Closed under the global context". *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_iface.
From M254S Require Import S_def S_main.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.

Check (S_equicons : SIR ⊢TC ⊥ <-> ZFc ⊢TC ⊥).
Check (S0_equicons : S0 ⊢TC ⊥ <-> ZFc ⊢TC ⊥).
Check (S_ZFC_equicons : SIR ⊢TC ⊥ <-> (fun phi => ZFc phi \/ phi = ZFC.Z_wo.ax_ac) ⊢TC ⊥).
Print Assumptions S_equicons.
Print Assumptions S_ZFC_equicons.
Check (ZF_to_S0 : ZFc ⊢TC ⊥ -> S0 ⊢TC ⊥).
Print Assumptions ZF_to_S0.
