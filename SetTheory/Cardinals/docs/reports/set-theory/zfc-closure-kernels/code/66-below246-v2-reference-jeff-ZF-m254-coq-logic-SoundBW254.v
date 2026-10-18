(** * SoundBW254: the bundle wffs are valid in SIR.

    [V a] := Fvalid SIR a  (one fixed list of SIR axioms proves dB rho a for every environment rho).
    Main lemma:  c <> a -> c <> b -> fr c phi = false -> V (BW a b c phi),
    using CP (container), IR and the closed GIC instance for the matrix dB sigma phi
    (and GIC for falsity, i.e. an empty set, in the collision case a = b). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd Std_brrep.
From M254S Require Import S_def.
From M254L Require Import Bundle254.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma SIR_EqAx psi : In psi EqAx -> SIR psi.
Proof.
  intros H. left. apply S0_base. unfold Sbase. unfold EqAx in H. simpl in H |- *. tauto.
Qed.

Definition V (a : wff) : Prop := Fvalid SIR a.

Lemma V_mp a b : V (Wim a b) -> V a -> V b.
Proof.
  intros [A1 [G1 H1]] [A2 [G2 H2]]. exists (A1 ++ A2). split.
  - intros psi [Hp|Hp]%in_app_iff; auto.
  - intro rho. eapply IE.
    + eapply Weak; [apply (H1 rho) | apply incl_appl, incl_refl].
    + eapply Weak; [apply (H2 rho) | apply incl_appr, incl_refl].
Qed.

Lemma V_gen x a : V a -> V (Wal x a).
Proof.
  intros [A [G H]]. exists A. split; [exact G|]. intro rho. cbn [dB]. apply AllI_named. intro t.
  rewrite dB_inst. apply H.
Qed.

Lemma V_lprov a : lprov a -> V a.
Proof.
  induction 1 as [a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | x y z Hxz Hyz
                  | x y a | x a | x y | x y z | x y z | x y z].
  - exact (V_mp _ _ IH1 IH2).
  - now apply V_gen.
  - apply (@Fvalid_nil SIR SIR_EqAx). intro; apply nd_B1.
  - apply (@Fvalid_nil SIR SIR_EqAx). intro; apply nd_B2.
  - apply (@Fvalid_nil SIR SIR_EqAx). intro; apply nd_B3.
  - apply (@Fvalid_nil SIR SIR_EqAx). intro; apply nd_B4.
  - apply (@Fvalid_nil SIR SIR_EqAx). intro; now apply nd_B6a.
  - apply (@Fvalid_nil SIR SIR_EqAx). intro; apply nd_B6b.
  - apply (@Fvalid_nil SIR SIR_EqAx). intro; apply nd_B6c.
  - apply (@Fvalid_EqAx SIR SIR_EqAx). intro; apply nd_B7.
  - apply (@Fvalid_EqAx SIR SIR_EqAx). intro; apply nd_B8a.
  - apply (@Fvalid_EqAx SIR SIR_EqAx). intro; apply nd_B8b.
  - apply (@Fvalid_EqAx SIR SIR_EqAx). intro; apply nd_B8c.
Qed.

Lemma V_ir : V (Wal 1 (Wn (Wel 1 1))).
Proof.
  exists [ax_ir]. split; [intros psi [<-|[]]; now right|].
  intro rho. apply Ctx. left. reflexivity.
Qed.

(** ** Helpers *)
Lemma dB_el (rho : nat -> term) x y : dB rho (Wel x y) = rho x ∈' rho y.
Proof. reflexivity. Qed.
Lemma dB_eqq (rho : nat -> term) x y : dB rho (Weq x y) = rho x ≡' rho y.
Proof. reflexivity. Qed.

Ltac envs := repeat first [ rewrite upd_eq | rewrite upd_neq by lia ].
Ltac envs_in H := repeat first [ rewrite upd_eq in H | rewrite upd_neq in H by lia ].

(** ** Atomic vacuity *)
Lemma VBV a b c rho : c <> a -> c <> b -> [] ⊢C dB rho (BV a b c).
Proof.
  intros H1 H2. unfold BV. apply dB_andI.
  - apply dB_impI. ctx_push H. apply dB_allI. intros t. rewrite dB_el in *. envs. exact H.
  - apply dB_impI. ctx_push H. apply dB_allI. intros t. rewrite dB_eqq in *. envs. exact H.
Qed.

(** ** Instances of CP and IR (keeping the context folded) *)
Lemma cp_inst G p : In ax_cp G ->
  G ⊢C ∃ (p`[↑] ∈' $0 ∧ ∀ ($0 ∈' $1 →
        (∀ ($0 ∈' $1 → $0 ∈' $2)) ∧
        ∃ ($0 ∈' $2 ∧ ∀ ((∀ ($0 ∈' $1 → $0 ∈' $3)) → $0 ∈' $1)))).
Proof. intros H. exact (AllE p (Ctx H)). Qed.

Lemma ir_inst G x : In ax_ir G -> G ⊢C ¬ x ∈' x.
Proof. intros H. exact (AllE x (Ctx H)). Qed.

(** ** Container *)
Lemma VBC_ne a b c rho G : a <> b -> c <> a -> c <> b -> In ax_cp G -> G ⊢C dB rho (BC a b c).
Proof.
  intros Hab Hca Hcb HG. unfold BC.
  fobtain (cp_inst G (rho c) HG) as Vv HV. fdestr HV H1 H2.
  apply (dB_exI _ _ _ Vv). apply dB_andI.
  - apply dB_allI. intros x. apply dB_impI. ctx_push Hx. rewrite dB_el in Hx. envs_in Hx.
    finst H2 x. fmp H2 Hx. fdestr H2 HT HW. apply dB_andI.
    + fex HW W HW'. fdestr HW' HW1 HW2. apply (dB_exI _ _ _ W). apply dB_andI.
      * apply dB_allI. intros z. apply dB_impI. ctx_push Hs.
        rewrite dB_el. envs. finst HW2 z. apply (IE HW2).
        apply AllI_named. intros u. simp. apply II. ctx_push Hu. simp_in Hu.
        apply (dB_allE _ _ _ u) in Hs. cbn [dB] in Hs. envs_in Hs.
        exact (IE Hs Hu).
      * rewrite dB_el. envs. exact HW1.
    + apply dB_allI. intros z. apply dB_impI. ctx_push Hz. rewrite dB_el in *. envs_in Hz. envs.
      finst HT z. exact (IE HT Hz).
  - rewrite dB_el. envs. exact H1.
Qed.

Lemma VBC_eq a c rho G : c <> a -> In ax_cp G -> In ax_ir G -> G ⊢C dB rho (BC a a c).
Proof.
  intros Hca HG HI. unfold BC.
  fobtain (cp_inst G (rho c) HG) as Vv HV. fdestr HV H1 H2.
  apply (dB_exI _ _ _ Vv). apply dB_andI.
  - apply dB_allI. intros x. apply dB_impI. ctx_push Hx. rewrite dB_el in Hx. envs_in Hx.
    fabsurd. exact (IE (ir_inst _ x HI) Hx).
  - rewrite dB_el. envs. exact H1.
Qed.

(** ** Global-image collection: collision case a = b (empty output set) *)
Lemma empty_inst G B : In (gic falsity) G ->
  G ⊢C ∃ ((∀ ($0 ∈' B`[↑]`[↑] → ∀ (⊥ → ∃ (⊥ ∧ $0 ∈' $3)))) ∧ ∀ ($0 ∈' $1 → ∃ ⊥)).
Proof. intros H. exact (AllE B (Ctx H)). Qed.

Lemma VBG_eq a c phi rho G : c <> a -> In (gic falsity) G -> In ax_ir G -> G ⊢C dB rho (BG a a c phi).
Proof.
  intros Hca HG HI. unfold BG.
  fobtain (empty_inst G (rho 0) HG) as C HC. fdestr HC H0 HE.
  apply (dB_exI _ _ _ C). apply dB_andI.
  - apply dB_allI. intros x. apply dB_impI. ctx_push Hx. rewrite dB_el in Hx. envs_in Hx.
    fabsurd. exact (IE (ir_inst _ x HI) Hx).
  - apply dB_allI. intros y. apply dB_impI. ctx_push Hy. rewrite dB_el in Hy. envs_in Hy.
    finst HE y. fmp HE Hy. fex HE z Hz. fabsurd. exact Hz.
Qed.

(** ** Global-image collection: distinct names *)
Definition sab (a b : nat) (v : nat) : term :=
  if Nat.eqb v a then $0 else if Nat.eqb v b then $1 else $(2 + v).
Definition thetaW (a b : nat) (phi : wff) : form := dB (sab a b) phi.

Lemma fb_theta a b phi : fb (maxfr phi + 3) (thetaW a b phi).
Proof.
  apply fb_dB. intros v Hv. apply fr_maxfr in Hv. unfold sab.
  destruct (Nat.eqb v a); [cbn; lia|]. destruct (Nat.eqb v b); cbn; lia.
Qed.

Lemma fb_gic n (th : form) : fb (n + 2) th -> fb n (gic th).
Proof.
  intros H. unfold gic. cbn. repeat split; try lia;
    (eapply fb_subst; [exact H|]; intros [|[|k]] Hk; cbn; lia).
Qed.

Lemma closed_gic n (th : form) : fb (n + 2) th -> closedf (forall_times n (gic th)).
Proof.
  intros H. unfold closedf. apply (fb_forall_times_inv n (gic th) 0). rewrite Nat.add_0_r.
  now apply fb_gic.
Qed.

Lemma theta_inst a b phi (tau e : nat -> term) : a <> b ->
  tau 0 = e a -> tau 1 = e b -> (forall v, fr v phi = true -> v <> a -> v <> b -> tau (2 + v) = e v) ->
  (thetaW a b phi)[tau] = dB e phi.
Proof.
  intros Hab E0 E1 Ev. unfold thetaW. rewrite dB_subst. apply dB_ext_fr. intros v Hv.
  unfold sab, funcomp. destruct (Nat.eqb_spec v a) as [->|Ha]; [exact E0|].
  destruct (Nat.eqb_spec v b) as [->|Hb]; [exact E1|]. cbn. now apply Ev.
Qed.

Ltac tcase := repeat match goal with |- context [?t`[_]] => is_var t; destruct t as [?|[]] end.

(* normalize a stacked substitution instance of thetaW to dB e phi *)
Ltac thw_eq Hab c Hfr rho := rewrite ?subst_comp; apply theta_inst; [exact Hab | | |];
  [ unfold funcomp; cbn; envs; tcase; cbn; reflexivity
  | unfold funcomp; cbn; envs; tcase; cbn; reflexivity
  | let v := fresh "v" in let Hv := fresh "Hv" in let H1 := fresh in let H2 := fresh in
    intros v Hv H1 H2;
    assert (v <> c) by (intros ->; rewrite Hfr in Hv; discriminate);
    unfold funcomp; cbn; envs; unfold funcomp; destruct (rho v) as [?|[]]; cbn; reflexivity ].

Lemma VBG_ne a b c phi rho G : a <> b -> c <> a -> c <> b -> fr c phi = false ->
  In (forall_times (maxfr phi + 1) (gic (thetaW a b phi))) G -> G ⊢C dB rho (BG a b c phi).
Proof.
  intros Hab Hca Hcb Hfr Hin.
  assert (Hc : closedf (forall_times (maxfr phi + 1) (gic (thetaW a b phi))))
    by (apply closed_gic; replace (maxfr phi + 1 + 2) with (maxfr phi + 3) by lia; apply fb_theta).
  pose proof (closed_inst G _ _ rho Hc (Ctx Hin)) as H. unfold gic in H. cbn in H.
  finst H (rho b). fex H C HC. fdestr HC H1 H2.
  unfold BG. apply (dB_exI _ _ _ C). apply dB_andI.
  - apply dB_allI. intros x. apply dB_impI. ctx_push Hx. rewrite dB_el in Hx. envs_in Hx.
    apply dB_allI. intros y. apply dB_impI. ctx_push Hy.
    finst H1 x. fmp H1 Hx. finst H1 y.
    match type of H1 with _ ⊢C ?A → _ =>
      assert (E : A = dB (upd (upd (upd rho c C) a x) b y) phi) by (thw_eq Hab c Hfr rho) end.
    rewrite E in H1. clear E. fmp H1 Hy. fex H1 y' Hy'. fdestr Hy' Hp Hm.
    apply (dB_exI _ _ _ y'). apply dB_andI.
    + match type of Hp with _ ⊢C ?A =>
        assert (E : A = dB (upd (upd (upd (upd rho c C) a x) b y) b y') phi) by (thw_eq Hab c Hfr rho) end.
      rewrite E in Hp. exact Hp.
    + rewrite dB_el. envs. exact Hm.
  - apply dB_allI. intros y. apply dB_impI. ctx_push Hy. rewrite dB_el in Hy. envs_in Hy.
    finst H2 y. fmp H2 Hy. fex H2 x Hx.
    apply (dB_exI _ _ _ x).
    match type of Hx with _ ⊢C ?A =>
      assert (E : A = dB (upd (upd (upd rho c C) b y) a x) phi) by (thw_eq Hab c Hfr rho) end.
    rewrite E in Hx. exact Hx.
Qed.

(** ** The bundle wffs are valid in SIR *)
Lemma SIR_cp : SIR ax_cp.
Proof. left. apply S0_base. unfold Sbase. simpl. tauto. Qed.

Lemma SIR_gic n th : closedf (forall_times n (gic th)) -> SIR (forall_times n (gic th)).
Proof. intros H. left. now apply S0_gic. Qed.

Theorem V_BW a b c phi : c <> a -> c <> b -> fr c phi = false -> V (BW a b c phi).
Proof.
  intros Hca Hcb Hfr. destruct (Nat.eq_dec a b) as [<-|Hab].
  - assert (Hc0 : closedf (forall_times 0 (gic falsity))) by (apply closed_gic; exact I).
    exists [ax_cp; ax_ir; gic falsity]. split.
    { intros psi [<-|[<-|[<-|[]]]]; [exact SIR_cp | now right | exact (SIR_gic 0 _ Hc0)]. }
    intros rho. unfold BW. apply dB_andI; [apply dB_andI|].
    + apply VBC_eq; [exact Hca | simpl; tauto | simpl; tauto].
    + apply VBG_eq; [exact Hca | simpl; tauto | simpl; tauto].
    + eapply Weak; [apply (VBV a a c rho Hca Hcb) | intros ? []].
  - set (n := maxfr phi + 1).
    assert (Hc : closedf (forall_times n (gic (thetaW a b phi))))
      by (apply closed_gic; unfold n; replace (maxfr phi + 1 + 2) with (maxfr phi + 3) by lia; apply fb_theta).
    exists [ax_cp; forall_times n (gic (thetaW a b phi))]. split.
    { intros psi [<-|[<-|[]]]; [exact SIR_cp | exact (SIR_gic _ _ Hc)]. }
    intros rho. unfold BW. apply dB_andI; [apply dB_andI|].
    + apply VBC_ne; [exact Hab | exact Hca | exact Hcb | simpl; tauto].
    + apply VBG_ne; [exact Hab | exact Hca | exact Hcb | exact Hfr | simpl; tauto].
    + eapply Weak; [apply (VBV a b c rho Hca Hcb) | intros ? []].
Qed.
