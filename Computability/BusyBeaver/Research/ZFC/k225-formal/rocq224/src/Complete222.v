(** * Complete222: completeness of the seed-K 222's numerical calculus.

    [StandardZFC ⊢TC ⊥ -> thm222 1].  The route is Elliot Glazer's lower chain to the ordinary
    theory K0 ([K0_ZFc_inconsistent] after Choice and Foundation are discharged), and K0 is
    interpreted in the calculus:

    - a wff [a] counts when [thm222 (tau (th a))], with [th] the equality interpretation of
      [L224E] (equality as membership indiscernibility).  Jeff's pure logic [lprov], and with it
      every natural-deduction derivation, interprets by [Interp222.lprov_thm222];
    - every K0 instance [kp0 phi] follows (by [KPrimeCore.seeded_core_to_kp0]) from the seed core
      [seeded_core phi], and that follows from one named seed bundle, whose private label is
      the bundle's own interpreted matrix code [seed_code phi = tau (th (Wn (Wn (tr source_names
      phi))))].  That code exceeds 3 and is not free in the matrix, so the bundle is enabled and
      its label is fresh.  This replaces [named_source_to_kprime] of [KDecodeCore]. *)
From Stdlib Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd.
From RegCon Require Import Rel.
From ZFC Require Import Z_prim Z_wo Z_main.
From K230S Require Import KCode230 KP0 KP0Use KPRaw KPSeed KPrimeCore KPrimeTheory KDecodeBundle
  KDecodeTranslate KDecodeBridge KDecodeEnv KDecodeLogic KQuotZFC KQuotZFTransfer.
From K230L Require Import Codes230 Comp_Prop230.
From K224 Require Import Codes222 Thm222 CD222 Prop222 L224E Interp222 Sound222.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** The interpreted proof predicate *)
Definition Q (a : wff) : Prop := thm222 (tau (th a)).

Lemma Q_of_lprov a : lprov a -> Q a.
Proof. apply lprov_thm222. Qed.

Lemma Q_lprov a b : lprov (Wim a b) -> Q a -> Q b.
Proof. intros H Ha. pose proof (Q_of_lprov _ H) as H'. unfold Q in *. cbn [th tau] in H'.
  exact (W_mp _ _ Ha H'). Qed.

Lemma Q_genall n a : Q a -> Q (genall n a).
Proof. induction n; cbn [genall]; [auto|]. intro H. unfold Q. cbn [th tau]. apply W_gen, IHn, H. Qed.

Lemma Q_tr_cl eta n a : Q a -> maxfr a < n -> Q (tr eta (dB var (genall n a))).
Proof.
  intros Ha Hn. set (t := dB var (genall n a)).
  assert (Hfb : fb 0 t) by now apply fb_cl.
  assert (E : dB var (tr eta t) = dB var (genall n a)).
  { rewrite (dB_tr t 0 eta var (frag_dB _ _) Hfb) by (intros; lia).
    rewrite (subst_ext_fb _ 0 _ var Hfb) by (intros; lia). apply subst_var. }
  destruct (alpha_dB _ _ var injective_var E) as [_ H2].
  exact (Q_lprov _ _ H2 (Q_genall n a Ha)).
Qed.

Lemma Q_discharge G c : lprov (foldi G c) -> (forall h, In h G -> Q h) -> Q c.
Proof.
  intros H HG. revert c H; induction G as [|h G IH]; intros c H; [exact (Q_of_lprov _ H)|].
  cbn [foldi fold_left] in H. specialize (IH (fun h' Hh' => HG h' (or_intror Hh')) _ H).
  unfold Q in IH. cbn [th tau] in IH. exact (W_mp _ _ (HG h (or_introl eq_refl)) IH).
Qed.

Definition TB (t : form) : Prop := exists a n, Q a /\ maxfr a < n /\ t = Lib n a.

Lemma TB_Lib a n : Q a -> maxfr a < n -> TB (Lib n a).
Proof. intros H1 H2. now exists a, n. Qed.

Theorem TB_to_thm : thm TB falsity -> thm222 1.
Proof.
  intros [C [HC Dv]].
  pose proof (nd_sound C falsity Dv eta0 oddenv_eta0) as S. cbn [tr] in S.
  apply der_foldi in S.
  assert (Hb : Q botw).
  { apply (Q_discharge _ _ S). intros h Hh. apply in_map_iff in Hh as [t [<- Ht]].
    destruct (HC t Ht) as (a & n & Ha & Hn & ->). exact (Q_tr_cl eta0 n a Ha Hn). }
  assert (H0 : Q (Wal 0 (Weq 0 0))) by (apply Q_of_lprov, LGEN, leq_refl).
  unfold Q in Hb, H0. unfold botw in Hb. cbn [th tau] in Hb, H0. exact (W_mp _ _ H0 Hb).
Qed.

(** ** Equality axioms *)
Lemma lprov_trans_eq : lprov (Wim (Weq 2 1) (Wim (Weq 1 0) (Weq 2 0))).
Proof.
  apply der_lprov. do 2 apply L1_LMeta.ded.
  apply (L1_LMeta.dmp _ (Weq 1 0)); [|apply L1_LMeta.dhyp; simpl; tauto].
  apply (L1_LMeta.dmp _ (Weq 1 2)); [apply L1_LMeta.dthm, LB8a|].
  apply (L1_LMeta.dmp _ (Weq 2 1)); [apply L1_LMeta.dthm, leq_sym | apply L1_LMeta.dhyp; simpl; tauto].
Qed.

Lemma TB_EqAx_mem psi : In psi EqAx -> TB psi.
Proof.
  intros H. repeat destruct H as [<-|H]; [| | | | destruct H].
  - exists (Weq 0 0), 1. repeat split; [apply Q_of_lprov, leq_refl | cbv; lia].
  - exists (Wim (Weq 1 0) (Weq 0 1)), 2. repeat split; [apply Q_of_lprov, leq_sym | cbv; lia].
  - exists (Wim (Weq 2 1) (Wim (Weq 1 0) (Weq 2 0))), 3. repeat split; [apply Q_of_lprov, lprov_trans_eq | cbv; lia].
  - exists (Wim (Weq 3 1) (Wim (Weq 2 0) (Wim (Wel 3 2) (Wel 1 0)))), 4.
    repeat split; [apply Q_of_lprov, leq_tr_el | cbv; lia].
Qed.

(** ** Codes: the interpreted matrix code exceeds every free name *)
Lemma tau_fr v a : fr v a = true -> v < tau a.
Proof.
  induction a as [x y|x y|a IHa b IHb|a IHa|x a IHa]; cbn [fr tau]; intros H.
  - unfold weq. pose proof (P_ge_l x y). pose proof (P_ge_r x y).
    apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; lia.
  - unfold wel. pose proof (P_ge_l x y). pose proof (P_ge_r x y).
    apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; lia.
  - unfold wim. apply orb_true_iff in H as [H|H];
      [pose proof (IHa H); pose proof (P_ge_l (tau a) (tau b))
      |pose proof (IHb H); pose proof (P_ge_r (tau a) (tau b))]; lia.
  - unfold wim. pose proof (IHa H). pose proof (P_ge_l (tau a) 1). lia.
  - destruct (Nat.eqb x v); [discriminate|]. unfold wal.
    pose proof (IHa H). pose proof (P_ge_r x (tau a)). lia.
Qed.

Lemma th_fr v a : fr v a = true -> fr v (th a) = true.
Proof.
  induction a as [x y|x y|a IHa b IHb|a IHa|x a IHa]; cbn [fr th]; intros H.
  - unfold Eind, Ev, Ein, Eout, Wiff, Wa, aux. cbn [fr].
    destruct (Nat.eqb_spec (S (x + y)) v); destruct (Nat.eqb_spec x v);
      destruct (Nat.eqb_spec y v); cbn in *; try lia; try reflexivity; try discriminate.
  - exact H.
  - apply orb_true_iff in H as [H|H]; [rewrite (IHa H)|rewrite (IHb H), orb_true_r]; reflexivity.
  - exact (IHa H).
  - destruct (Nat.eqb x v); [discriminate|]. exact (IHa H).
Qed.

Definition seed_matrix (phi : form) : wff := Wn (Wn (tr source_names phi)).
Definition seed_code (phi : form) : nat := tau (th (seed_matrix phi)).

Lemma seed_code_gt3 phi : 3 < seed_code phi.
Proof.
  unfold seed_code, seed_matrix. cbn [th tau]. unfold wim.
  pose proof (P_ge_r (4 * P (tau (th (tr source_names phi))) 1) 1). lia.
Qed.

Lemma seed_code_fresh phi : fr (seed_code phi) (tr source_names phi) = false.
Proof.
  destruct (fr (seed_code phi) (tr source_names phi)) eqn:E; [|reflexivity].
  exfalso. assert (H : fr (seed_code phi) (seed_matrix phi) = true) by exact E.
  apply th_fr, tau_fr in H. unfold seed_code in H at 1. lia.
Qed.

(** the named seed bundle at the frozen roles a = 1, b = 3, label = its own matrix code *)
Local Opaque KCode230.P KCode230.wim KCode230.wal KCode230.wel KCode230.weq.

Lemma tau_th_SeedN a b c q : tau (th (SeedN a b c q)) =
  wn (wim (vrel a b c) (wal c (wim (wal b (wim (wel b c) (wim (wal a (wim (tau (th q))
    (wim (wal a (wim (wal c (wim (wel c a) (wel c b)))
      (wal b (wim (tau (th q)) (wim (wal b (wim (tau (th q)) (wim (wel b c) F))) F))))) F))) F)))
    (wim (wal b (wim (tau (th q)) (wim (wal b (wim (tau (th q)) (wim (wel b c) F))) F))) F)))).
Proof.
  unfold SeedN, KRV, ClosN, ReqN, KSubset, vrel, wn, F. cbn [th tau]. reflexivity.
Qed.

Lemma Q_seed phi : Q (SeedN 1 3 (seed_code phi) (seed_matrix phi)).
Proof.
  unfold Q. rewrite tau_th_SeedN.
  change (thm222 (bundle222 1 3 (seed_code phi))).
  pose proof (seed_code_gt3 phi). apply W_bundle; lia.
Qed.

Local Transparent KCode230.P KCode230.wim KCode230.wal KCode230.wel KCode230.weq.

(** ** Normalizing the named bundle *)
Lemma L_dn p : leqv (Wn (Wn p)) p.
Proof. split; [apply lpc_nn_elim|apply lpc_nn_intro]. Qed.
Lemma L_sym p q : leqv p q -> leqv q p.
Proof. intros [H1 H2]. now split. Qed.

Lemma L_req b k q : leqv (ReqN b k (Wn (Wn q))) (KRequest b k q).
Proof.
  unfold ReqN, KRequest, Wex, Wa.
  apply kleqv_all, kleqv_imp; [apply L_dn|]. apply kleqv_neg, kleqv_all.
  eapply kleqv_trans; [|apply L_sym, L_dn].
  apply kleqv_imp; [apply L_dn|apply kleqv_refl].
Qed.

Lemma L_clos a b k q : leqv (ClosN a b k (Wn (Wn q))) (KClosE a b k q).
Proof.
  unfold ClosN, KClosE, Wex, Wa.
  apply kleqv_all, kleqv_imp; [apply kleqv_refl|]. apply kleqv_neg, kleqv_all.
  eapply kleqv_trans; [|apply L_sym, L_dn].
  apply kleqv_imp; [apply L_dn|]. apply kleqv_neg, kleqv_all, kleqv_imp; [apply kleqv_refl|].
  apply L_req.
Qed.

Lemma L_seed a b c q : leqv (SeedN a b c (Wn (Wn q))) (SeedY a b c q).
Proof.
  unfold SeedN, SeedY. apply kleqv_neg, kleqv_imp; [apply kleqv_refl|].
  apply kleqv_all, kleqv_imp; [apply L_clos|]. apply kleqv_neg, L_req.
Qed.

(** ** The named seed bundle gives the seed core *)
Lemma dB_impI G rho a b : (dB rho a :: G) ⊢C dB rho b -> G ⊢C dB rho (Wim a b).
Proof. intros H. cbn [dB]. now apply II. Qed.
Lemma dB_negI G rho a : (dB rho a :: G) ⊢C ⊥ -> G ⊢C dB rho (Wn a).
Proof. intros H. cbn [dB]. now apply II. Qed.

Theorem named_seed_to_seeded G (phi : form) N c :
  incl EqAx G -> fb N phi -> 3 < c ->
  fr c (tr source_names phi) = false ->
  (forall rho, G ⊢C dB rho (SeedY 1 3 c (tr source_names phi))) ->
  G ⊢C seeded_core phi.
Proof.
  intros HE Hfb Hc Hfresh Hsource.
  unfold seeded_core, seed_root. fall a.
  pose proof (Hsource (source_env var a a)) as H. unfold SeedY in H.
  fcontra Hno.
  apply (dB_neg _ _ H). apply dB_impI. ctx_push HRV. clear HRV.
  apply dB_allI. intros C. apply dB_impI. ctx_push HC. apply dB_negI. ctx_push HR.
  fold (private_env var a a c C) in HC, HR.
  apply (IE Hno). fexists C. fsplit.
  - (* the seed request *)
    fintro Hsome. fex Hsome y Hy.
    unfold KRequest in HR.
    pose proof (dB_allE _ _ _ y HR) as HyReq.
    rewrite private_env_output in HyReq by exact Hc.
    fassert HyNamed : (dB (private_env var y a c C) (tr source_names phi)).
    { apply (iff_r _ _ _ (private_env_matrix _ phi N var y a c C HE Hfb Hfresh)).
      kconv Hy. }
    pose proof (dB_imp _ _ _ HyReq HyNamed) as Hfound.
    apply (dB_exE _ _ _ _ Hfound). intros z. apply II. ctx_push Hz.
    rewrite private_env_output in Hz by exact Hc.
    pose proof (dB_andE1 _ _ _ Hz) as HzPhi.
    pose proof (dB_andE2 _ _ _ Hz) as HzMem.
    fexists z. fsplit.
    + rewrite private_env_member in HzMem by exact Hc. exact HzMem.
    + pose proof (iff_l _ _ _
        (private_env_matrix _ phi N var z a c C HE Hfb Hfresh) HzPhi) as T.
      kconv T.
  - (* the closure, as in KDecodeCore.named_source_to_kprime *)
    unfold KClosE in HC. rename HC into Hclosure.
    unfold emitted_closure. simp. fall u. fintro Hu.
    pose proof (dB_allE _ _ _ u Hclosure) as HuReq.
    rewrite private_env_output in HuReq by exact Hc.
    fassert HuNamed : (dB (private_env var u a c C) (Wel 3 c)).
    { rewrite private_env_member by exact Hc. exact Hu. }
    pose proof (dB_imp _ _ _ HuReq HuNamed) as Hsome.
    apply (dB_exE _ _ _ _ Hsome). intros v. apply II. ctx_push Hv.
    rewrite private_env_input in Hv by exact Hc.
    pose proof (dB_andE1 _ _ _ Hv) as HvPhi.
    pose proof (dB_andE2 _ _ _ Hv) as HvReq.
    fexists v. fsplit.
    + pose proof (iff_l _ _ _
        (private_env_matrix _ phi N var u v c C HE Hfb Hfresh) HvPhi) as T.
      kconv T.
    + fall p. fintro Hsub.
      pose proof (dB_allE _ _ _ p HvReq) as HpReq.
      rewrite private_env_input in HpReq by exact Hc.
      fassert HsubNamed : (dB (private_env var u p c C) (KSubset 1 3 c)).
      { rewrite private_env_subset by exact Hc. kconv Hsub. }
      pose proof (dB_imp _ _ _ HpReq HsubNamed) as Hrequest.
      unfold KRequest in Hrequest. fall z. fintro Hz.
      pose proof (dB_allE _ _ _ z Hrequest) as HzReq.
      rewrite private_env_output in HzReq by exact Hc.
      fassert HzNamed : (dB (private_env var z p c C) (tr source_names phi)).
      { apply (iff_r _ _ _ (private_env_matrix _ phi N var z p c C HE Hfb Hfresh)).
        kconv Hz. }
      pose proof (dB_imp _ _ _ HzReq HzNamed) as Hfound.
      apply (dB_exE _ _ _ _ Hfound). intros y. apply II. ctx_push Hy.
      rewrite private_env_output in Hy by exact Hc.
      pose proof (dB_andE1 _ _ _ Hy) as HyPhi.
      pose proof (dB_andE2 _ _ _ Hy) as HyMem.
      fexists y. fsplit.
      * pose proof (iff_l _ _ _
          (private_env_matrix _ phi N var y p c C HE Hfb Hfresh) HyPhi) as T.
        kconv T.
      * rewrite private_env_member in HyMem by exact Hc. exact HyMem.
Qed.

(** ** K0 in the interpreted calculus *)
Lemma TB_closed a : TB a -> closedf a.
Proof. intros (p & n & Hp & Hn & ->). apply Lib_closed, Hn. Qed.

Lemma TB_kp0 n phi : TB ⊢TC forall_times n (kp0 phi).
Proof.
  set (c := seed_code phi).
  set (p := SeedN 1 3 c (seed_matrix phi)).
  set (N := S (maxfr p)).
  set (B := EqAx ++ [Lib N p]).
  assert (HE : incl EqAx B) by (intros a Ha; apply in_or_app; now left).
  assert (HB : forall a, In a B -> TB a).
  { intros a Ha. apply in_app_or in Ha as [Ha|[<-|[]]].
    - apply TB_EqAx_mem, Ha.
    - apply TB_Lib; [apply Q_seed|unfold N; lia]. }
  destruct (fb_exists phi) as [m Hm]. exists B. split; [exact HB|].
  apply forall_times_intro_closed; [intros a Ha; apply TB_closed, HB, Ha|].
  apply (seeded_core_to_kp0 B HE phi).
  apply (named_seed_to_seeded B phi m c HE Hm (seed_code_gt3 phi) (seed_code_fresh phi)).
  intros rho. apply (iff_l _ _ _ (leqv_dB230 B rho _ _ HE (L_seed 1 3 c (tr source_names phi)))).
  apply (Lib_inst B N p rho); [unfold N; lia|].
  apply Ctx, in_or_app. right. now left.
Qed.

Lemma K0_TB a : K0 a -> TB ⊢TC a.
Proof.
  intros [b Ha|phi n Hc].
  - exists [b]. split; [intros x [<-|[]]; apply TB_EqAx_mem, Ha|]. apply Ctx. now left.
  - apply TB_kp0.
Qed.

Theorem K0_to_thm222 : K0 ⊢TC ⊥ -> thm222 1.
Proof.
  intros H. apply TB_to_thm. apply (theory_derivation_map K0 TB ⊥ K0_TB H).
Qed.

Theorem thm222_complete : StandardZFC ⊢TC ⊥ -> thm222 1.
Proof.
  intros H. apply K0_to_thm222, K0_ZFc_inconsistent. exact (ac_reg_relcon H).
Qed.

Theorem thm222_iff_standardZFC : thm222 1 <-> StandardZFC ⊢TC ⊥.
Proof. split; [apply thm222_sound|apply thm222_complete]. Qed.

Print Assumptions thm222_iff_standardZFC.
