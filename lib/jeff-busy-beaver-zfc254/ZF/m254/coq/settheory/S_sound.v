(** * S_sound: SIR is consistent relative to ZF + Reg (direction (A))

    Every SIR derivation is relativized to Gödel's L (as in zf/zfc Z_main), and every axiom of
    SIR is proved relativized to L inside ZF + Reg:
    - equality axioms: Z_axL;
    - IR: regularity (Z_ord.no_self_g);
    - CP: V := L_β where β reflects (Z_refl) the formula
        θ(x,W,s,t) := (s∈t ∧ ∃W' ζ(x,W')) ∨ (¬ s∈t ∧ ζ(x,W)),   ζ(x,W) := ∀z (z⊆x → z∈W),
      a selector trick that reflects ∃W ζ and ζ at once; the constructible power set (Z_axL)
      then puts a W ∈ L_β above every constructible subset of x;
    - GIC: least-stage collection over the L_δ (ord_collect), then separation in L (Z_axL) from
      the bounding level L_β with the formula ∃x φ(x,y).
    No ranks, transitive closures or V_α are needed: L comes with its own hierarchy. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase.
From RegCon Require Import Rel.
From RegCon Require MinZF Link.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl Z_axL.
From M254S Require Import S_def S_qt S_gic.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

#[local] Arguments Lform : simpl never.
#[local] Arguments InL : simpl never.
#[local] Hint Rewrite Lform_up Lform_inst InL_subst relL_subst relS_subst' : fsub.

Lemma ZFR_closed a : ZFR a -> closedf a.
Proof.
  intros [[[a' H | phi n H | phi n H] | ->] | ->].
  - now apply ZF0base_closed.
  - exact H.
  - exact H.
  - apply ax_om'_closed.
  - cbn. lia.
Qed.

(** the shape of the statement for one axiom *)
Definition holdsL (a : form) : Prop := exists A, (forall b, In b A -> ZFR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G -> incl A G -> G ⊢C rel Lform a.

Lemma Sbase_cases a : In a Sbase -> a = ax_cp \/ In a ZF0base.
Proof.
  intros Ha. repeat (destruct Ha as [<-|Ha]; [first [now left | right; cbn; tauto] |]). destruct Ha.
Qed.

Lemma L_ir : holdsL ax_ir.
Proof.
  exists []. split; [intros b []|]. intros G HG HR HOm HL _.
  unfold ax_ir. cbn. fall x. fintro HxL. fintro H. exact (no_self_g HG HR x H).
Qed.

(** ** CP in L, by reflection *)
(** ζ(x,W) = ∀z (z ⊆ x → z ∈ W) ($0 = x, $1 = W); ρ(x) = ∃W ζ(x,W);
    θ(x,W,s,t) = (s∈t ∧ ρ(x)) ∨ (¬ s∈t ∧ ζ(x,W)) *)
Definition cp_zeta : form := ∀ ((∀ ($0 ∈' $1 → $0 ∈' $2)) → $0 ∈' $2).
Definition cp_rho : form := ∃ (∀ ((∀ ($0 ∈' $1 → $0 ∈' $3)) → $0 ∈' $1)).
Definition cp_theta : form := ($2 ∈' $3 ∧ cp_rho) ∨ ((¬ ($2 ∈' $3)) ∧ cp_zeta).

Lemma fb_cp_theta : fb 4 cp_theta.
Proof. fbcomp. Qed.

Lemma L_cp : holdsL ax_cp.
Proof.
  exists (powL_insts ++ refl_insts 4 cp_theta). split.
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb].
    - exact (oc_insts_ok 0 Qpow b fb_Qpow Hb).
    - exact (refl_insts_ok 4 cp_theta b fb_cp_theta Hb). }
  intros G HG HR HOm HL HA.
  assert (Hpw : incl powL_insts G) by (intros b Hb; apply HA, in_or_app; now left).
  assert (Hri : incl (refl_insts 4 cp_theta) G) by (intros b Hb; apply HA, in_or_app; now right).
  clear HA. pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  pose proof (axL_power HG HR HOm HL Hpw) as Hpow.
  unfold ax_cp. cbn [rel]. fall p. fintro Hp.
  fassert He : (∃ Emp0 $0). { eapply emp0_ex; eassumption. } fex He e He0.
  fassert Ho : (Ord0 e). { eapply ord_emp; eassumption. }
  fobtain (L_above HG HR HOm HL p e Hp Ho) as a Ha0. fex Ha0 Ya HYa.
  fdestr HYa HYa1 HpYa. fdestr HYa1 HYa2 HYaL. fdestr HYa2 Hao Hea.
  pose proof fb_cp_theta as Hfbt.
  fassert Hr : (∃ ((Ord0 $0 ∧ a`[↑] ∈' $0) ∧ Refl 4 cp_theta $0)). { eapply reflection; eassumption. }
  fex_raw Hr b Hb. fdestr Hb Hb1 HRf. fdestr Hb1 Hbo Hab. simp_in Hbo. simp_in Hab.
  let GG := ctxof in assert (HRf2 : GG ⊢C Refl 4 cp_theta b).
  { replace (Refl 4 cp_theta b) with ((Refl 4 cp_theta $0)[b..]); [exact HRf|].
    rewrite (Refl_subst _ _ _ _ Hfbt). reflexivity. }
  clear HRf. rename HRf2 into HRf.
  fassert HYb : (∃ LL b`[↑] $0). { eapply LL_ex; eassumption. } fex HYb Yb HYb0.
  fassert HYY : (Ya ∈' Yb ∧ Sub0 Ya Yb). { eapply LL_mono with (b := a); eassumption. }
  fdestr HYY HYaYb HYsub.
  fassert HpYb : (p ∈' Yb). { eapply sub0_use; eassumption. }
  fassert HT : (Trans0 Yb). { eapply LL_trans with (a := b); eassumption. }
  fexists Yb. fsplit; [eapply L_LL; eassumption|]. fsplit; [exact HpYb|].
  fall x. fintro HxL. fintro HxV. fsplit.
  { fall z. fintro HzL. fintro Hzx. eapply trans0_use; eassumption. }
  pose proof Hpow as T. unfold ax_power' in T. cbn [rel] in T. finst T x. fmp T HxL. fex T P HP0.
  fdestr HP0 HPL HPp. rewrite rel_is_power in HPp.
  fassert HYbL : (InL Yb). { eapply L_LL; eassumption. }
  fassert Hrho : (rel Lform (cp_rho[x..])).
  { unfold cp_rho. simp. fexists P. fsplit; [exact HPL|]. fall z. fintro HzL. fintro Hsub.
    finst HPp z. fmp HPp HzL. apply (iff_r _ _ _ HPp). rewrite rel_sub'. fconv_h Hsub. }
  fassert R1 : (rel Lform (cp_theta[x .: x .: p .: Ya .: var]) ↔ relS Yb (cp_theta[x .: x .: p .: Ya .: var])).
  { eapply (refl_use HG HR HOm HL); [exact Hfbt | exact HRf | exact HYb0 |].
    intros [|[|[|[|k]]]] Hk; cbn; [exact HxV|exact HxV|exact HpYb|exact HYaYb|lia]. }
  fassert L1 : (rel Lform (cp_theta[x .: x .: p .: Ya .: var])).
  { unfold cp_theta. simp. fleft. fsplit; [exact HpYa | fconv_h Hrho]. }
  fhave S1 : (iff_l _ _ _ R1 L1). unfold cp_theta in S1. simp_in S1. fcases S1 S1a S1b.
  2: { fdestr S1b S1c S1d. fabsurd. exact (IE S1c HpYa). }
  fdestr S1a S1c S1d. unfold cp_rho in S1d. simp_in S1d. fex S1d W HW. fdestr HW HWY HWz.
  fassert R2 : (rel Lform (cp_theta[x .: W .: x .: x .: var]) ↔ relS Yb (cp_theta[x .: W .: x .: x .: var])).
  { eapply (refl_use HG HR HOm HL); [exact Hfbt | exact HRf | exact HYb0 |].
    intros [|[|[|[|k]]]] Hk; cbn; [exact HxV|exact HWY|exact HxV|exact HxV|lia]. }
  fassert S2 : (relS Yb (cp_theta[x .: W .: x .: x .: var])).
  { unfold cp_theta, cp_zeta. simp. fright. fsplit; [fintro Hxx; exact (no_self_g HG HR x Hxx) | fconv_h HWz]. }
  fhave L2 : (iff_r _ _ _ R2 S2). unfold cp_theta, cp_zeta in L2. simp_in L2. fcases L2 L2a L2b.
  { fdestr L2a L2c L2d. fabsurd. exact (no_self_g HG HR x L2c). }
  fdestr L2b L2c L2d.
  fexists W. fsplit; [exact (inL_el HG HR HOm HL Yb W HYbL HWY)|]. fsplit; [exact HWY | fconv_h L2d].
Qed.

(** ** GIC in L *)
Lemma fb_gic_inv n phi : closedf (forall_times n (gic phi)) -> fb (S (S n)) phi.
Proof.
  intros H. apply fb_forall_times in H. rewrite Nat.add_0_r in H. unfold gic in H. cbn in H.
  destruct H as [_ [_ H]]. eapply fb_ren_inv; [exact H|].
  intros [|[|i]] Hi; cbn in Hi |- *; lia.
Qed.

(** instantiating a relativized universal closure *)
Lemma rel_ft_inst (M : form) (HM : bounded 1 M) G n : forall (theta : form) (sg : nat -> term),
  G ⊢C rel M (forall_times n theta) -> (forall k, k < n -> G ⊢C M[(sg k)..]) ->
  G ⊢C (rel M theta)[fun k => if k <? n then sg k else $(k - n)].
Proof.
  induction n as [|n IH]; intros theta sg H Hs.
  - cbn. erewrite subst_ext; [rewrite subst_var; exact H|]. intros k; cbn. f_equal; lia.
  - unfold forall_times in H. cbn [iter] in H. rewrite iter_switch in H.
    apply (IH (∀ theta) (fun k => sg (S k))) in H; [|intros k Hk; apply Hs; lia].
    cbn [rel subst_form] in H. rewrite (M_up' M HM) in H. apply (AllE (sg 0)) in H. cbn [subst_form] in H.
    pose proof (IE H (Hs 0 ltac:(lia))) as H'.
    rewrite subst_comp in H'. erewrite subst_ext; [exact H'|].
    intros [|k]; [reflexivity|]. cbn -[Nat.ltb]. unfold funcomp.
    change (match n with 0 => false | S m' => k <=? m' end) with (k <? n).
    destruct (Nat.ltb_spec k n), (Nat.ltb_spec (S k) (S n)); try lia;
      rewrite subst_term_comp; symmetry; apply subst_term_id; intros; reflexivity.
Qed.

(** Q(δ, u): if u has an L-witness y with φ^L(u, y), one lies in L_δ ($0 = δ, $1 = u, $(k+2) = param k) *)
Definition gicQ (phi : form) : form :=
  (∃ (InL $0 ∧ rel Lform (phi[$2 .: $0 .: (fun k => $(3 + k))]))) →
  ∃ (LL $1 $0 ∧ ∃ ($0 ∈' $1 ∧ rel Lform (phi[$3 .: $0 .: (fun k => $(4 + k))]))).
(** separation formula: ∃x φ(x, y) ($0 = y, $(k+1) = param k) *)
Definition gicS (phi : form) : form := ∃ phi[$0 .: $1 .: (fun k => $(2 + k))].

Lemma fb_InL x N : idx x < N -> fb N (InL x).
Proof.
  intros H. unfold InL. eapply fb_subst; [exact fb_Lform|]. intros [|i] Hi; cbn; [exact H|lia].
Qed.

Lemma fb_gicQ n phi : fb (S (S n)) phi -> fb (S (S n)) (gicQ phi).
Proof.
  intros H. unfold gicQ. cbn [fb]. split; [split|split; [|split; [cbn; split; lia|]]].
  - apply fb_InL. cbn. lia.
  - apply fb_rel. eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia.
  - apply fb_LL; cbn; lia.
  - apply fb_rel. eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma fb_gicS n phi : fb (S (S n)) phi -> fb (S n) (gicS phi).
Proof.
  intros H. unfold gicS. cbn. eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia.
Qed.

#[local] Arguments gicQ : simpl never.

Lemma gicQ_subst phi s : (gicQ phi)[s] =
  ((∃ (InL $0 ∧ rel Lform (phi[(s 1)`[↑] .: $0 .: (fun k => (s (2 + k))`[↑])]))) →
   ∃ (LL (s 0)`[↑] $0 ∧ ∃ ($0 ∈' $1 ∧ rel Lform (phi[(s 1)`[↑]`[↑] .: $0 .: (fun k => (s (2 + k))`[↑]`[↑])])))).
Proof.
  unfold gicQ. cbn [subst_form]. rewrite ?InL_subst, ?LL_subst, ?relL_subst. cbn. feq_form.
Qed.

(** least-stage collection: one level L_β holds an L-witness for every u ∈ B that has one *)
Lemma collect_L {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  n phi tau B : fb (S (S n)) phi -> incl (oc_insts n (gicQ phi)) G ->
  G ⊢C ∃ (∃ ((Ord0 $1 ∧ LL $1 $0) ∧ ∀ ($0 ∈' B`[↑]`[↑]`[↑] → ∀ (InL $0 →
          rel Lform (phi[$1 .: $0 .: (fun k => (tau k)`[↑]`[↑]`[↑]`[↑])]) →
          ∃ ($0 ∈' $3 ∧ rel Lform (phi[$2 .: $0 .: (fun k => (tau k)`[↑]`[↑]`[↑]`[↑]`[↑])])))))).
Proof.
  intros Hphi HI. pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO. pose proof (Ax_ord_prim _ HO) as HP.
  pose proof (fb_gicQ n phi Hphi) as HQ.
  fassert He : (∃ Emp0 $0). { eapply emp0_ex; eassumption. } fex He e He0.
  fassert Ho : (Ord0 e). { eapply ord_emp; eassumption. }
  fassert H1 : (∀ ($0 ∈' B`[↑] → ∃ (Ord0 $0 ∧ (gicQ phi)[up (up tau)]))).
  { fall u. fintro Hu.
    apply (XM_rule _ (∃ (InL $0 ∧ rel Lform (phi[u`[↑] .: $0 .: (fun k => (tau k)`[↑])])))).
    - fintro Hy. fex Hy y Hyy. fdestr Hyy HyL Hth. pose proof HyL as H'. rewrite InL_eq in H'.
      fex H' a Ha. fex Ha Y HY. fdestr HY HY12 HyY. fdestr HY12 Hao HaY.
      fexists a. fsplit; [exact Hao|]. rewrite !subst_comp, gicQ_subst. cbn. fintro Hd.
      fexists Y. fsplit; [exact HaY|]. fexists y. fsplit; [exact HyY | fconv_h Hth].
    - fintro Hn. fexists e. fsplit; [exact Ho|]. rewrite !subst_comp, gicQ_subst. cbn. fintro Hy.
      fabsurd. apply (IE Hn). fconv_h Hy. }
  fassert H2 : (∀ (∀ (∀ (Ord0 $1 → Ord0 $0 → Sub0 $1 $0 →
      (gicQ phi)[$1 .: $2 .: (fun k => (tau k)`[↑]`[↑]`[↑])] →
      (gicQ phi)[$0 .: $2 .: (fun k => (tau k)`[↑]`[↑]`[↑])])))).
  { fall u. fall d. fall d'. fintro Hd. fintro Hd'. fintro Hs. fintro HQd.
    rewrite ?subst_comp, ?gicQ_subst in HQd. cbn in HQd. rewrite ?subst_comp, ?gicQ_subst. cbn.
    fintro Hy. fmp_conv HQd Hy. fex HQd Y HY. fdestr HY HY1 HY2.
    fassert HY' : (∃ LL d'`[↑] $0). { eapply LL_ex; eassumption. } fex HY' Y' HY'0.
    fexists Y'. fsplit; [exact HY'0|]. fex HY2 y Hy'. fdestr Hy' HyY Hth. fexists y. fsplit.
    - eapply sub0_use; [|exact HyY]. eapply LL_sub with (a := d') (b := d); eassumption.
    - fconv_h Hth. }
  fassert Hc : (∃ (Ord0 $0 ∧ ∀ ($0 ∈' B`[↑]`[↑] → (gicQ phi)[$1 .: $0 .: (fun k => (tau k)`[↑]`[↑])]))).
  { exact (ord_collect_g HG HR HO n (gicQ phi) tau B HQ HI H1 H2). }
  fex Hc g Hg. fdestr Hg Hg1 Hg2.
  fassert HYg : (∃ LL g`[↑] $0). { eapply LL_ex; eassumption. } fex HYg Yg HYg0.
  fexists g. fexists Yg. fsplit; [fsplit; assumption|].
  fall u. fintro Hu. fall y. fintro HyL. fintro Hth.
  finst Hg2 u. fmp Hg2 Hu. rewrite ?subst_comp, ?gicQ_subst in Hg2. cbn in Hg2.
  fassert A : (∃ (InL $0 ∧ rel Lform (phi[u`[↑] .: $0 .: (fun k => (tau k)`[↑])]))).
  { fexists y. fsplit; [exact HyL | fconv_h Hth]. }
  fmp_conv Hg2 A. fex Hg2 Y HY. fdestr HY HY1 HY2. fex HY2 y' Hy'. fdestr Hy' Hy'Y Hth'.
  fassert E : (Y ≡' Yg). { eapply LL_unique with (a := g); eassumption. }
  fexists y'. fsplit; [exact (elem_cong HG y' Y y' Yg (eq_refl' HG y') E Hy'Y) | fconv_h Hth'].
Qed.

Lemma L_gic n phi : closedf (forall_times n (gic phi)) -> holdsL (forall_times n (gic phi)).
Proof.
  intros Hc. pose proof (fb_gic_inv n phi Hc) as Hphi.
  exists (oc_insts n (gicQ phi) ++ sepL_insts n (gicS phi)). split.
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb].
    - exact (oc_insts_ok n _ b (fb_gicQ n phi Hphi) Hb).
    - exact (sepL_insts_ok n _ b (fb_gicS n phi Hphi) Hb). }
  intros G HG HR HOm HL HA.
  assert (HAq : incl (oc_insts n (gicQ phi)) G) by (intros b Hb; apply HA, in_or_app; now left).
  assert (HAs : incl (sepL_insts n (gicS phi)) G) by (intros b Hb; apply HA, in_or_app; now right).
  pose proof (axL_sep HG HR HOm HL n (gicS phi) (fb_gicS n phi Hphi) HAs) as Hsep.
  clear HA.
  enough (H : G ⊢C (rel Lform (forall_times n (gic phi)))[var]) by (rewrite subst_var in H; exact H).
  apply (rel_ft Lform bounded_Lform). intros G' tau HGG' Htau _. lift HGG'.
  assert (Htau' : forall k, k < n -> G' ⊢C InL (tau k)) by exact Htau. clear Htau.
  assert (Hs : G' ⊢C (rel Lform (ax_sep' (gicS phi)))[tau]).
  { pose proof (rel_ft_inst Lform bounded_Lform G' n (ax_sep' (gicS phi)) tau Hsep Htau') as T.
    erewrite subst_ext_fb; [exact T| |].
    - apply fb_rel. pose proof (sep_closed n _ (fb_gicS n phi Hphi)) as Hcl. apply fb_forall_times in Hcl.
      rewrite Nat.add_0_r in Hcl. exact Hcl.
    - intros k Hk. cbv beta. destruct (Nat.ltb_spec k n); [reflexivity | lia]. }
  rewrite relL_subst, rel_sep_eq in Hs.
  rewrite relL_subst. unfold gic. cbn [subst_form rel].
  fall B. fintro HB.
  fobtain (collect_L HG HR HOm HL n phi tau B Hphi HAq) as g Hg0. fex Hg0 Yg HYg.
  fdestr HYg HYg12 HYcov. fdestr HYg12 Hgo HgY.
  fassert HYL : (InL Yg). { eapply L_LL; eassumption. }
  finst Hs Yg. fmp Hs HYL. fex Hs C HC0. fdestr HC0 HCL HC.
  fexists C. fsplit; [exact HCL|]. fsplit.
  - fall u. fintro HuL. fintro HuB. fall y. fintro HyL. fintro Hth.
    pose proof HYcov as T. finst T u. fmp T HuB. finst T y. fmp T HyL. fmp_conv T Hth.
    fex T y' Hy'. fdestr Hy' Hy'Y Hth'.
    fassert Hy'L : (InL y'). { eapply InL_intro; eassumption. }
    fassert Hy'C : (y' ∈' C).
    { finst HC y'. fmp HC Hy'L. apply (iff_r _ _ _ HC). fsplit; [exact Hy'Y|].
      unfold gicS. simp. fexists u. fsplit; [exact HuL | fconv_h Hth']. }
    fexists y'. fsplit; [exact Hy'L | fsplit; [fconv_h Hth' | exact Hy'C]].
  - fall y. fintro HyL. fintro HyC. finst HC y. fmp HC HyL. fhave T : (iff_l _ _ _ HC HyC).
    fdestr T T1 T2. unfold gicS in T2. simp_in T2. fconv_h T2.
Qed.

Theorem SIR_L a : SIR a -> holdsL a.
Proof.
  intros [[a' Ha | phi n Hc] | ->].
  - destruct (Sbase_cases a' Ha) as [-> | Hb]; [exact L_cp | exact (axL_ZFR a' (ZFR_base a' Hb))].
  - now apply L_gic.
  - exact L_ir.
Qed.

Theorem S_to_ZFR : SIR ⊢TC ⊥ -> ZFR ⊢TC ⊥.
Proof.
  intros [A [HA H]].
  destruct (MinZF.collect (R := fun L (a : form) => forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G ->
               incl Ax_L G -> incl L G -> G ⊢C rel Lform a) (Q := ZFR) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL G H1 H2 H3 H4 H5. apply Hx; trivial. intros b Hb. now apply H5, HL.
  - intros a Ha. now apply SIR_L, HA.
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
      * intros a Ha. exact (SIR_closed a (HA a Ha)).
      * intros a Ha. apply weak_cons. apply HL2; trivial.
      * apply Ctx. now left.
Qed.

Theorem S_to_ZF : SIR ⊢TC ⊥ -> ZFc ⊢TC ⊥.
Proof. intros H. apply Link.regularity_relcon_std. exact (S_to_ZFR H). Qed.
