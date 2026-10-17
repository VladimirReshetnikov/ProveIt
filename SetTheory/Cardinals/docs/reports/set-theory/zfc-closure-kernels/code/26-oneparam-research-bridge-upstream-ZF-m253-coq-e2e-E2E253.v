(** * E2E253: end to end, the 253-state candidate zfc_253.tm, derived locally from Mira-Cult's ZFC254
    (github.com/Mira-Cult/turing-machines)
    halts from the blank tape
    iff the library's ZF (closed schemes) is inconsistent, and likewise for ZFC.

    [halts], [c0]: busycoq's TM semantics; [tm]: M253.TM253, built from the literal table Table253.v,
    which ../../check.py compares with machine/zfc_253.tm (sha256 84a21f71...).

    Chain (namespaces: M253 = coq/tm, M254 = ../m254/coq/tm, M254P = ../m254/coq/prog, M254L = ../m254/coq/logic, M254S = ../m254/coq/settheory):
      halts tm c0
        <-> rm_halts p254 ([], R0)        M253.Main.tm253_rm         (TM layer: symbolic executor on the table)
        <-> enum254_halts                 M254P.Main254.prog254      (program layer: DAG + bisim certificate)
        <-> thm254 1                      M254L.L1_254.L1_254        (enumerator <-> code-level calculus)
        <-> SIR ⊢TC ⊥                     M254L.Bridge254.bridge254  (calculus <-> library ND over SIR)
        <-> ZFc ⊢TC ⊥                     M254S.S_main.S_equicons    (bisimulation quotient / relativization to L)

    Names are fully qualified: the library's notations clash with busycoq's. *)
From Undecidability.FOL Require Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From BusyCoq Require Import TM.
From M253 Require Import TM253.
From M253 Require Main.
From M254P Require Main254.
From M254L Require Enum254 Thm254 L1_254 Bridge254.
From M254S Require S_def S_main.
From ZF Require Std_iface.
From ZFC Require Z_wo.

Notation tprv := Undecidability.FOL.Deduction.FullND.tprv.
Notation sig0 := Undecidability.FOL.Syntax.BinSig.sig_empty.
Notation zfp := Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig.
Notation fon := Undecidability.FOL.Syntax.Core.falsity_on.
Notation cls := Undecidability.FOL.Syntax.Core.class.
Notation bot := Undecidability.FOL.Syntax.Core.falsity.

(** their own target theory, for reference *)
Theorem zf253_halts_iff_SIR : M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0 <-> @tprv sig0 zfp fon cls M254S.S_def.SIR bot.
Proof.
  rewrite M253.Main.tm253_rm, M254P.Main254.prog254, M254L.L1_254.L1_254.
  exact M254L.Bridge254.bridge254.
Qed.

Theorem zf253_halts_iff_ZF : M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0 <-> @tprv sig0 zfp fon cls ZF.Std_iface.ZFc bot.
Proof. rewrite zf253_halts_iff_SIR. exact M254S.S_main.S_equicons. Qed.

Theorem zf253_halts_iff_ZFC :
  M253.TM253.TM253.halts M253.TM253.tm M253.TM253.TM253.c0 <-> @tprv sig0 zfp fon cls (fun phi => ZF.Std_iface.ZFc phi \/ phi = ZFC.Z_wo.ax_ac) bot.
Proof. rewrite zf253_halts_iff_SIR. exact M254S.S_main.S_ZFC_equicons. Qed.

Print zf253_halts_iff_SIR.
Print zf253_halts_iff_ZF.
Print zf253_halts_iff_ZFC.
Print Assumptions zf253_halts_iff_SIR.
Print Assumptions zf253_halts_iff_ZF.
Print Assumptions zf253_halts_iff_ZFC.
