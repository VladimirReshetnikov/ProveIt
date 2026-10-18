(** * E2E254: end to end, the 254-state machine zfc_254.tm (by Mira-Cult, github.com/Mira-Cult/turing-machines)
    halts from the blank tape
    iff the library's ZF (closed schemes) is inconsistent, and likewise for ZFC.

    [halts], [c0]: busycoq's TM semantics; [tm]: M254.TM254, built from the literal table Table254.v,
    which ../../check.py compares with machine/zfc_254.tm (sha256 d655ce2c...).

    Chain (namespaces: M254 = coq/tm, M254P = coq/prog, M254L = coq/logic, M254S = coq/settheory):
      halts tm c0
        <-> rm_halts p254 ([], R0)        M254.Main.tm254_rm         (TM layer: symbolic executor on the table)
        <-> enum254_halts                 M254P.Main254.prog254      (program layer: DAG + bisim certificate)
        <-> thm254 1                      M254L.L1_254.L1_254        (enumerator <-> code-level calculus)
        <-> SIR ⊢TC ⊥                     M254L.Bridge254.bridge254  (calculus <-> library ND over SIR)
        <-> ZFc ⊢TC ⊥                     M254S.S_main.S_equicons    (bisimulation quotient / relativization to L)

    Names are fully qualified: the library's notations clash with busycoq's. *)
From Undecidability.FOL Require Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From BusyCoq Require Import TM.
From M254 Require Import TM254.
From M254 Require Main.
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
Theorem zf254_halts_iff_SIR : halts tm c0 <-> @tprv sig0 zfp fon cls M254S.S_def.SIR bot.
Proof.
  rewrite M254.Main.tm254_rm, M254P.Main254.prog254, M254L.L1_254.L1_254.
  exact M254L.Bridge254.bridge254.
Qed.

Theorem zf254_halts_iff_ZF : halts tm c0 <-> @tprv sig0 zfp fon cls ZF.Std_iface.ZFc bot.
Proof. rewrite zf254_halts_iff_SIR. exact M254S.S_main.S_equicons. Qed.

Theorem zf254_halts_iff_ZFC :
  halts tm c0 <-> @tprv sig0 zfp fon cls (fun phi => ZF.Std_iface.ZFc phi \/ phi = ZFC.Z_wo.ax_ac) bot.
Proof. rewrite zf254_halts_iff_SIR. exact M254S.S_main.S_ZFC_equicons. Qed.

Print ZFC.Z_wo.ax_ac.
Print Assumptions zf254_halts_iff_SIR.
Print Assumptions zf254_halts_iff_ZF.
Print Assumptions zf254_halts_iff_ZFC.
