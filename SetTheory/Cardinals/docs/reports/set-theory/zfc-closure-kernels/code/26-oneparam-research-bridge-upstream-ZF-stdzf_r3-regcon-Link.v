(** * Instantiation for the shared target theory of zf-l1-logic (zf/stdzf/coq/Std_iface.v)

    Std_iface.ZFc = the library's minZFeq axioms with the separation and replacement instances
    universally closed (closedness via Std_tr.fb).  Results:

      regularity_relcon_std : (Std_iface.ZFc + ax_reg') ⊢TC ⊥ -> Std_iface.ZFc ⊢TC ⊥
      bridge_std            : Std_iface.ZFc ⊢TC ⊥ <-> ZFc ⊢TC ⊥   (function-symbol signature)   *)

From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts.
From Undecidability.FOL.Sets Require Import ZF minZF.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Undecidability.FOL.Reductions Require Import PCPb_to_minZF.
From RegCon Require Import Main MinZF.
From ZF Require Std_tr Std_iface.

Lemma bounded_t_idx N (t : @term sig_empty) : bounded_t N t -> Std_tr.idx t < N.
Proof. intros H. destruct H as [x Hx | f v _]; [exact Hx | destruct f]. Qed.

Lemma bounded_fb {ff} N (phi : @form sig_empty ZF_pred_sig full_operators ff) :
  bounded N phi -> Std_tr.fb N phi.
Proof.
  induction 1 as [ff N P v H | b ff N phi psi _ IH1 _ IH2 | q ff N phi _ IH |]; cbn; auto.
  destruct P; cbn in v |- *; rewrite (vec_inv2 v) in H |- *; cbn;
    split; apply bounded_t_idx, H; first [apply Vector.In_cons_hd | apply Vector.In_cons_tl, Vector.In_cons_hd].
Qed.

Lemma std_min phi : ZFcl_min phi -> Std_iface.ZFc phi.
Proof.
  intros [H | [(n & psi & -> & Hb) | (n & psi & -> & Hb)]].
  - unfold minZFeq', minZF' in H.
    repeat (destruct H as [<-|H]; [try (left; apply Std_iface.ZF0_base; cbn; tauto) |]); try destruct H.
    now right.
  - left. apply Std_iface.ZF0_sep. now apply bounded_fb.
  - left. apply Std_iface.ZF0_rep. now apply bounded_fb.
Qed.

Lemma std_all phi : Std_iface.ZFc phi -> ZFcl_all phi.
Proof.
  intros [[psi H | psi n _ | psi n _] | ->].
  - exists 0, psi. split; [| reflexivity]. constructor.
    unfold Std_iface.ZF0base in H. unfold minZFeq', minZF'. cbn in *. tauto.
  - exists n, (ax_sep' psi). split; [apply minZFeq_sep | reflexivity].
  - exists n, (ax_rep' psi). split; [apply minZFeq_rep | reflexivity].
  - exists 0, ax_om'. split; [| reflexivity]. constructor. cbn. tauto.
Qed.

Theorem regularity_relcon_std :
  (fun phi => Std_iface.ZFc phi \/ phi = ax_reg') ⊢TC ⊥ -> Std_iface.ZFc ⊢TC ⊥.
Proof. apply regularity_relcon_min'; [exact std_min | exact std_all]. Qed.

Theorem bridge_std : Std_iface.ZFc ⊢TC ⊥ <-> ZFc ⊢TC ⊥.
Proof. apply bridge; [exact std_min | exact std_all]. Qed.

Theorem bridge_reg_std :
  (fun phi => Std_iface.ZFc phi \/ phi = ax_reg') ⊢TC ⊥ <-> ZFcReg ⊢TC ⊥.
Proof. apply bridge_reg; [exact std_min | exact std_all]. Qed.

(* The same statements with zf-l1-logic's [thm] (definitionally the library's classical tprv). *)
Lemma thm_tprv T phi : Std_iface.thm T phi <-> T ⊢TC phi.
Proof. split; intros H; exact H. Qed.

Theorem regularity_relcon_thm :
  Std_iface.thm (fun phi => Std_iface.ZFc phi \/ phi = ax_reg') ⊥ -> Std_iface.thm Std_iface.ZFc ⊥.
Proof. rewrite !thm_tprv. apply regularity_relcon_std. Qed.
