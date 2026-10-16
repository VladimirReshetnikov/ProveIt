(** * Z_main: relative consistency of the axiom of choice.

      (ZF + Reg + AC) ⊢TC ⊥  →  (ZF + Reg) ⊢TC ⊥

    in the library's minimal signature, ZF = Std_iface.ZFc (minZFeq with closed schema
    instances), Reg = ax_reg', AC = ax_ac (Z_wo).  Proof: relativize the derivation to L
    (RegCon.Rel.rel_prv via Z_rel.transfer); every axiom holds in L (Z_axL, Z_ac). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From RegCon Require Import Rel.
From RegCon Require MinZF.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl Z_axL Z_wo Z_ac.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma ax_reg'_closed : closedf ax_reg'.
Proof. cbn. lia. Qed.

Lemma ZFR_closed a : ZFR a -> closedf a.
Proof.
  intros [[[phi H | phi n H | phi n H] | ->] | ->].
  - now apply ZF0base_closed.
  - exact H.
  - exact H.
  - apply ax_om'_closed.
  - apply ax_reg'_closed.
Qed.

Definition ZFRAC (phi : form) : Prop := ZFR phi \/ phi = ax_ac.

Lemma axL_all a : ZFRAC a -> exists A, (forall b, In b A -> ZFR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G -> incl A G -> G ⊢C rel Lform a.
Proof. intros [H | ->]; [now apply axL_ZFR | apply acL_ex]. Qed.

Theorem ac_relcon : ZFRAC ⊢TC ⊥ -> ZFR ⊢TC ⊥.
Proof.
  intros [A [HA H]].
  destruct (MinZF.collect (R := fun L (a : form) => forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G ->
               incl Ax_L G -> incl L G -> G ⊢C rel Lform a) (Q := ZFR) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL G H1 H2 H3 H4 H5. apply Hx; trivial. intros b Hb. now apply H5, HL.
  - intros a Ha. now apply axL_all, HA.
  - set (G0 := ax_reg' :: ax_om' :: ZF0base ++ Ax_L ++ L).
    assert (HG0 : incl ZF0base G0) by (intros b Hb; right; right; apply in_app_iff; now left).
    assert (HR0 : In ax_reg' G0) by now left.
    assert (HO0 : In ax_om' G0) by (right; now left).
    assert (HL0 : incl Ax_L G0) by (intros b Hb; right; right; apply in_app_iff; right; apply in_app_iff; now left).
    assert (HLL : incl L G0) by (intros b Hb; right; right; apply in_app_iff; right; apply in_app_iff; now right).
    exists G0. split.
    + intros b [ <- | [ <- | Hb ] ]; [apply ZFR_reg | apply ZFR_om |].
      apply in_app_iff in Hb as [Hb|Hb]; [now apply ZFR_base|].
      apply in_app_iff in Hb as [Hb|Hb]; [now apply Ax_L_ok | now apply HL1].
    + apply (ExE_named (L_ex HG0 HR0 HO0 HL0)). intros t.
      change ⊥ with (rel Lform ⊥).
      apply (transfer Lform bounded_Lform A ⊥ _ t H).
      * cbn. exact I.
      * intros a Ha. destruct (HA a Ha) as [Ha' | ->]; [now apply ZFR_closed | apply ax_ac_closed].
      * intros a Ha. apply weak_cons. apply HL2; trivial.
      * apply Ctx. now left.
Qed.

(** ** Combined with the relative consistency of regularity (zf/regcon) *)
From RegCon Require Link.

Corollary ac_reg_relcon :
  (fun phi => (ZFc phi \/ phi = ax_reg') \/ phi = ax_ac) ⊢TC ⊥ -> ZFc ⊢TC ⊥.
Proof. intros H. apply Link.regularity_relcon_std. exact (ac_relcon H). Qed.

(** ZFC without regularity *)
Corollary zfc_relcon : (fun phi => ZFc phi \/ phi = ax_ac) ⊢TC ⊥ -> ZFc ⊢TC ⊥.
Proof.
  intros H. apply ac_reg_relcon. apply (Weak_T H). intros phi [Hphi | ->]; [left; now left | now right].
Qed.

(** ZF, ZF + AC and ZF + Reg + AC are equiconsistent *)
Theorem ZFC_equicons : (fun phi => ZFc phi \/ phi = ax_ac) ⊢TC ⊥ <-> ZFc ⊢TC ⊥.
Proof.
  split; [exact zfc_relcon|]. intros H. apply (Weak_T H). intros phi Hphi. now left.
Qed.

Theorem ZFCReg_equicons : (fun phi => (ZFc phi \/ phi = ax_reg') \/ phi = ax_ac) ⊢TC ⊥ <-> ZFc ⊢TC ⊥.
Proof.
  split; [exact ac_reg_relcon|]. intros H. apply (Weak_T H). intros phi Hphi. left. now left.
Qed.
