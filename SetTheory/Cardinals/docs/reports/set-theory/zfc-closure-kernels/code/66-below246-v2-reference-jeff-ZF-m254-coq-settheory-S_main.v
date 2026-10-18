(** * S_main: SIR, S0, ZF and ZFC are equiconsistent (object level, library ND)

      ZF_to_S0  : ZFc ⊢TC ⊥ -> S0 ⊢TC ⊥     (B) bisimulation quotient (S_quot, S_ax)
      S_to_ZF   : SIR ⊢TC ⊥ -> ZFc ⊢TC ⊥     (A) S_sound + regularity_relcon_std (zf/regcon)
      S_equicons, S0_equicons, S_ZFC_equicons (with zfc_relcon of zf/zfc) *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setinf.
From ZFC Require Z_wo Z_main.
From M254S Require Import S_def S_qt S_quot S_ax S_sound.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma ZFc_to_ZFinf : ZFc ⊢TC ⊥ -> (fun a => ZF0 a \/ a = INF_lib) ⊢TC ⊥.
Proof.
  apply tprv_cut. intros a [Ha | ->].
  - exists [a]. split; [intros b [<-|[]]; now left | apply Ctx; now left].
  - exact inf_or_to_zf.
Qed.

Theorem ZF_to_S0 : ZFc ⊢TC ⊥ -> S0 ⊢TC ⊥.
Proof.
  intros H. apply ZFc_to_ZFinf in H.
  exact (qt_tprv Eqv Mem Eqv_subst Mem_subst _ S0 ⊥ S_ZF0inf H).
Qed.

Lemma S0_S phi : S0 ⊢TC phi -> SIR ⊢TC phi.
Proof. intros [A [HA D]]. exists A. split; [intros b Hb; left; now apply HA | exact D]. Qed.

Theorem ZF_to_S : ZFc ⊢TC ⊥ -> SIR ⊢TC ⊥.
Proof. intros H. apply S0_S, ZF_to_S0, H. Qed.

Theorem S_equicons : SIR ⊢TC ⊥ <-> ZFc ⊢TC ⊥.
Proof. split; [exact S_to_ZF | exact ZF_to_S]. Qed.

Theorem S0_equicons : S0 ⊢TC ⊥ <-> ZFc ⊢TC ⊥.
Proof. split; [intros H; apply S_to_ZF, S0_S, H | exact ZF_to_S0]. Qed.

Theorem S_ZFC_equicons : SIR ⊢TC ⊥ <-> (fun phi => ZFc phi \/ phi = Z_wo.ax_ac) ⊢TC ⊥.
Proof. rewrite Z_main.ZFC_equicons. exact S_equicons. Qed.
