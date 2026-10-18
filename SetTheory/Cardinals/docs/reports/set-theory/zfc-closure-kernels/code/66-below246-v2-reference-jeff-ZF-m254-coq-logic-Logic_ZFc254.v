(** * Logic_ZFc254: the abstract enumerator of the zfc_254 source halts iff the library's ZF
    (closed schemes, Std_iface.ZFc) is inconsistent.  Composes Bridge254.enum254_SIR with
    m254/settheory's S_equicons (SIR ⊢TC ⊥ <-> ZFc ⊢TC ⊥). *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_iface.
From M254S Require Import S_def S_main.
From M254L Require Import Enum254 Bridge254.

Theorem enum254_ZFc : enum254_halts <-> @tprv _ _ falsity_on class Std_iface.ZFc falsity.
Proof. rewrite enum254_SIR. exact S_equicons. Qed.

Print Assumptions enum254_ZFc.
