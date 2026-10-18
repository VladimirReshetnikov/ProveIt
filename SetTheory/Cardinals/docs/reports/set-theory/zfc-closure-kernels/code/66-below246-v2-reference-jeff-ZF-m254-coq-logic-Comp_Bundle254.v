(** * Comp_Bundle254: SIR inconsistent -> thm254 1.

    TB = the universal closures [Lib n a] of the named wffs a with thm254 (tau a).
      (1) TB ⊢ ⊥ -> thm254 1    (ND soundness for S2 [nd_sound], as Std_glue.TPset_to_prov)
      (2) every SIR axiom is derivable from TB:
          equality axioms and IR are closures of tau-theorems; CP and every closed GIC instance follow
          from closures of bundle wffs  BW a b c phi  with c = tau phi (Bundle254). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd Std_brrep.
From M254S Require Import S_def.
From M254L Require Import Codes254 Thm254 CD254 Comp_Prop254 Wff254 Bundle254.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition Q (a : wff) : Prop := thm254 (tau a).

Lemma Q_lprov a b : lprov (Wim a b) -> Q a -> Q b.
Proof. intros H Ha. pose proof (lprov_thm _ H) as H'. cbn [tau] in H'. exact (T_mp _ _ Ha H'). Qed.

Lemma Q_of_lprov a : lprov a -> Q a.
Proof. apply lprov_thm. Qed.

Lemma Q_genall n a : Q a -> Q (genall n a).
Proof. induction n; cbn; [auto|]. intro H. apply T_gen, IHn, H. Qed.

Lemma Q_tr_cl eta n a : Q a -> maxfr a < n -> Q (tr eta (dB var (genall n a))).
Proof.
  intros Ha Hn. set (th := dB var (genall n a)).
  assert (Hfb : fb 0 th) by now apply fb_cl.
  assert (E : dB var (tr eta th) = dB var (genall n a)).
  { rewrite (dB_tr th 0 eta var (frag_dB _ _) Hfb) by (intros; lia).
    rewrite (subst_ext_fb _ 0 _ var Hfb) by (intros; lia). apply subst_var. }
  destruct (alpha_dB _ _ var injective_var E) as [_ H2].
  exact (Q_lprov _ _ H2 (Q_genall n a Ha)).
Qed.

Lemma Q_discharge G c : lprov (foldi G c) -> (forall h, In h G -> Q h) -> Q c.
Proof.
  intros H HG. revert c H; induction G as [|h G IH]; intros c H; [exact (Q_of_lprov _ H)|].
  cbn [foldi fold_left] in H. specialize (IH (fun h' Hh' => HG h' (or_intror Hh')) _ H).
  unfold Q in IH. cbn [tau] in IH. exact (T_mp _ _ (HG h (or_introl eq_refl)) IH).
Qed.

Definition TB (th : form) : Prop := exists a n, Q a /\ maxfr a < n /\ th = Lib n a.

Lemma TB_Lib a n : Q a -> maxfr a < n -> TB (Lib n a).
Proof. intros H1 H2. now exists a, n. Qed.

Theorem TB_to_thm : thm TB falsity -> thm254 1.
Proof.
  intros [C [HC Dv]].
  pose proof (nd_sound C falsity Dv eta0 oddenv_eta0) as S. cbn [tr] in S.
  apply der_foldi in S.
  assert (Hb : Q botw).
  { apply (Q_discharge _ _ S). intros h Hh. apply in_map_iff in Hh as [th [<- Hth]].
    destruct (HC th Hth) as (a & n & Ha & Hn & ->). exact (Q_tr_cl eta0 n a Ha Hn). }
  assert (H0 : Q (Wal 0 (Weq 0 0))) by (apply Q_of_lprov, LGEN, leq_refl).
  unfold Q in Hb, H0. cbn [tau botw] in Hb, H0. exact (T_mp _ _ H0 Hb).
Qed.

(** ** Equality axioms and IR *)
Lemma Lib_eq_thm a n psi : Q a -> maxfr a < n -> Lib n a = psi -> thm TB psi.
Proof. intros H1 H2 <-. apply thm_ax. now apply TB_Lib. Qed.

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

Lemma TB_EqAx psi : In psi EqAx -> thm TB psi.
Proof. intro H. apply thm_ax. now apply TB_EqAx_mem. Qed.

(** IR is the closure of  -. v0 e. v0, whose code is F -> F *)
Lemma TB_IR : thm TB ax_ir.
Proof.
  apply (Lib_eq_thm (Wn (Wel 0 0)) 1); [unfold Q; cbn [tau]; apply thm_I | cbv; lia | reflexivity].
Qed.

(** ** CP from a bundle closure *)
Lemma occ_tau v a : occ v a = true -> v < tau a.
Proof.
  induction a as [x y|x y|a IHa b IHb|a IHa|x a IHa]; cbn [occ tau]; intro H.
  - apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; subst; unfold weq;
      [pose proof (P_ge_l v y) | pose proof (P_ge_r x v)]; lia.
  - apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; subst; unfold wel;
      [pose proof (P_ge_l v y) | pose proof (P_ge_r x v)]; lia.
  - unfold wim. apply orb_true_iff in H as [H|H];
      [specialize (IHa H); pose proof (P_ge_l (tau a) (tau b)) | specialize (IHb H); pose proof (P_ge_r (tau a) (tau b))]; lia.
  - unfold wim. specialize (IHa H). pose proof (P_ge_l (tau a) 1). lia.
  - unfold wal. apply orb_true_iff in H as [H|H].
    + apply Nat.eqb_eq in H; subst. pose proof (P_ge_l v (tau a)). lia.
    + specialize (IHa H). pose proof (P_ge_r x (tau a)). lia.
Qed.

Local Opaque wim wel wal weq P.

Lemma tau_BW a b phi : tau (BW a b (tau phi) phi) = bundle a b (tau phi).
Proof. reflexivity. Qed.

Lemma dB_el (rho : nat -> term) x y : dB rho (Wel x y) = rho x ∈' rho y.
Proof. reflexivity. Qed.

Ltac envs := repeat first [ rewrite upd_eq | rewrite upd_neq by lia ].

Lemma Q_BW a b phi : tau phi <> a -> tau phi <> b -> Q (BW a b (tau phi) phi).
Proof. intros H1 H2. unfold Q. rewrite tau_BW. now apply T_bundle. Qed.

Lemma tau_eq00 : tau (Weq 0 0) = 3.
Proof. reflexivity. Qed.

Lemma TB_CP : thm TB ax_cp.
Proof.
  pose proof (Q_BW 1 2 (Weq 0 0)) as HQ. rewrite tau_eq00 in HQ. specialize (HQ ltac:(lia) ltac:(lia)).
  set (W := BW 1 2 3 (Weq 0 0)) in *.
  assert (Hm : maxfr W < 4) by (unfold W; cbn; lia).
  exists [Lib 4 W]. split; [intros psi [<-|[]]; now apply TB_Lib|].
  assert (HL : [Lib 4 W] ⊢C Lib 4 W) by (apply Ctx; now left).
  unfold ax_cp. apply AllI_named. intros p. cbn.
  pose proof (Lib_inst _ _ _ (fun v => if Nat.eqb v 3 then p else var v) Hm HL) as H.
  unfold W, BW in H. apply dB_andE1, dB_andE1 in H. unfold BC in H.
  apply (dB_exE _ _ _ _ H). intros t. apply II. ctx_push Ht.
  apply (ExI t). simp. fsplit.
  - pose proof (dB_andE2 _ _ _ Ht) as H1. rewrite dB_el in H1. envs. exact H1.
  - fall x. apply II. ctx_push Hx. simp_in Hx.
    pose proof (dB_andE1 _ _ _ Ht) as H1. apply (dB_allE _ _ _ x) in H1.
    fassert Hx' : (dB (upd (upd (fun v => if v =? 3 then p else $v) 2 t) 1 x) (Wel 1 2));
       [rewrite dB_el; envs; exact Hx|].
    pose proof (dB_imp _ _ _ H1 Hx') as H2. clear H1 Hx'. fsplit.
    + fall z. apply II. ctx_push Hz. simp_in Hz.
      pose proof (dB_andE2 _ _ _ H2) as H3. apply (dB_allE _ _ _ z) in H3.
      fassert Hz' : (dB (upd (upd (upd (fun v => if v =? 3 then p else $v) 2 t) 1 x) 3 z) (Wel 3 1));
         [rewrite dB_el; envs; exact Hz|].
      pose proof (dB_imp _ _ _ H3 Hz') as H4. rewrite dB_el in H4. envs. exact H4.
    + pose proof (dB_andE1 _ _ _ H2) as H3. apply (dB_exE _ _ _ _ H3). intros w. apply II. ctx_push Hw.
      apply (ExI w). simp. fsplit.
      * pose proof (dB_andE2 _ _ _ Hw) as H4. rewrite dB_el in H4. envs. exact H4.
      * fall z. apply II. ctx_push Hs. simp_in Hs.
        pose proof (dB_andE1 _ _ _ Hw) as H4. apply (dB_allE _ _ _ z) in H4.
        fassert Hs' : (dB (upd (upd (upd (upd (fun v => if v =? 3 then p else $v) 2 t) 1 x) 3 w) 2 z)
                                (Wal 3 (Wim (Wel 3 2) (Wel 3 1)))).
        { apply dB_allI. intros u. cbn [dB]. envs. apply (AllE u) in Hs. simp_in Hs. exact Hs. }
        pose proof (dB_imp _ _ _ H4 Hs') as H5. rewrite dB_el in H5. envs. exact H5.
Qed.

(** ** GIC instances from bundle closures *)
Lemma phi_eqv (th : form) N (HN : fb N th) q (Hq : occ q (tr (fun k => 2 * k + 1) th) = false)
  (G : list form) (HE : incl EqAx G) (e : nat -> term) (x y : term) (sg : nat -> term) :
  (forall k, k < N -> (fun k => 2 * k + 1) k <> q) ->
  e 1 = x -> e 3 = y -> (forall k, k + 2 < N -> e (2 * k + 5) = sg k) ->
  G ⊢C dB e (Wal q (tr (fun k => 2 * k + 1) th)) ↔ th[x .: y .: sg].
Proof.
  intros Hnq E1 E3 Ek.
  assert (Hfr : forall t, dB (upd e q t) (tr (fun k => 2 * k + 1) th) = dB e (tr (fun k => 2 * k + 1) th)).
  { intros t. apply dB_ext_fr. intros v Hv. apply upd_neq. intros ->. rewrite fr_occ in Hv; [discriminate | exact Hq]. }
  assert (Hb : forall n k, n < N -> k < qd th -> (fun k => 2 * k + 1) n <> bname k).
  { intros n k _ _. unfold bname. lia. }
  pose proof (tr_equiv th N (fun k => 2 * k + 1) e G HE HN Hb) as T. cbv beta in T.
  assert (Es : th[fun n => e (2 * n + 1)] = th[x .: y .: sg]).
  { apply (subst_ext_fb _ N); [exact HN|]. intros [|[|k]] Hk; cbn - [Nat.mul].
    - exact E1.
    - exact E3.
    - replace (2 * S (S k) + 1) with (2 * k + 5) by lia. apply Ek. lia. }
  rewrite Es in T. fsplit.
  - fintro H. apply (iff_l _ _ _ T). apply (dB_allE _ _ _ $0) in H. rewrite Hfr in H. exact H.
  - fintro H. apply dB_allI. intros t. rewrite Hfr. apply (iff_r _ _ _ T). exact H.
Qed.

Ltac tcase := repeat match goal with |- context [?t`[_]] => is_var t; destruct t as [?|[]] end.

Ltac thnorm HN sg :=
  rewrite ?subst_comp; apply (subst_ext_fb _ _ _ _ HN);
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros [|[|k]] Hk; unfold funcomp; cbn; unfold funcomp;
  try (destruct (sg k) as [?|[]]); cbn; tcase; cbn; reflexivity.

Ltac thnorm_in H th HN sg x y :=
  match type of H with _ ⊢C ?f =>
    let E := fresh "E" in assert (E : f = th[x .: y .: sg]) by thnorm HN sg; rewrite E in H; clear E end.

Ltac thnorm_goal th HN sg x y :=
  match goal with |- _ ⊢C ?f =>
    let E := fresh "E" in assert (E : f = th[x .: y .: sg]) by thnorm HN sg; rewrite E; clear E end.

Ltac envs_in H := repeat first [ rewrite upd_eq in H | rewrite upd_neq in H by lia ].

Lemma half k : (2 * k + 5 - 5) / 2 = k.
Proof. replace (2 * k + 5 - 5) with (k * 2) by lia. apply Nat.div_mul. lia. Qed.

Local Opaque Lib EqAx.

Lemma TB_gic (th : form) n : closedf (forall_times n (gic th)) -> thm TB (forall_times n (gic th)).
Proof.
  intros Hcl.
  destruct (fb_exists th) as [N HN].
  set (eta := fun k => 2 * k + 1).
  set (q := 2 * N + 5).
  set (phi0 := tr eta th). set (phi := Wal q phi0). set (c := tau phi).
  assert (Hq : occ q phi0 = false).
  { eapply occ_tr; [exact HN | intros k Hk; unfold eta, q; lia | apply notbinder_odd; unfold q;
      rewrite Nat.odd_add, Nat.odd_mul; reflexivity]. }
  assert (Hqc : q < c) by (apply occ_tau; cbn [occ phi]; now rewrite Nat.eqb_refl).
  assert (Hcf : fr c phi = false).
  { apply fr_occ. destruct (occ c phi) eqn:E; [|reflexivity]. apply occ_tau in E. unfold c in E. lia. }
  pose proof (Q_BW 1 3 phi) as HQ. fold c in HQ. specialize (HQ ltac:(unfold q in Hqc; lia) ltac:(unfold q in Hqc; lia)).
  assert (Hc1 : c <> 1) by (unfold q in Hqc; lia). assert (Hc3 : c <> 3) by (unfold q in Hqc; lia).
  clearbody c.
  set (W := BW 1 3 c phi) in *.
  set (m := S (maxfr W)). assert (Hm : maxfr W < m) by (unfold m; lia). clearbody m.
  exists (Lib m W :: EqAx). split.
  { intros psi [<-|H]; [apply TB_Lib; [exact HQ | exact Hm] | now apply TB_EqAx_mem]. }
  assert (HL : (Lib m W :: EqAx) ⊢C Lib m W) by (apply Ctx; now left).
  assert (HE : incl EqAx (Lib m W :: EqAx)) by (intros x Hx; now right).
  apply ft_intro. intros sg. unfold gic. cbn. apply AllI_named. intros B.
  set (rho := fun v => if Nat.eqb v 3 then B else sg ((v - 5) / 2)).
  assert (Hnq : forall k, k < N -> (fun k => 2 * k + 1) k <> q) by (intros k Hk; unfold q; lia).
  assert (R3 : rho 3 = B) by reflexivity.
  assert (Rk : forall k, rho (2 * k + 5) = sg k).
  { intros k. unfold rho. replace (Nat.eqb (2 * k + 5) 3) with false by (symmetry; apply Nat.eqb_neq; lia).
    now rewrite half. }
  pose proof (Lib_inst _ _ _ rho Hm HL) as H.
  change (dB rho W) with (dB rho (BW 1 3 c phi)) in H. unfold BW in H. apply dB_andE1, dB_andE2 in H. unfold BG in H.
  apply (dB_exE _ _ _ _ H). intros C. apply II. ctx_push HC.
  cbn. apply (ExI C). cbn. fsplit.
  - apply AllI_named. intros x. simp. apply II. ctx_push Hx. simp_in Hx.
    apply AllI_named. intros y. simp. apply II. ctx_push Hy. simp_in Hy.
    thnorm_in Hy th HN sg x y.
    pose proof (dB_andE1 _ _ _ HC) as H1. apply (dB_allE _ _ _ x) in H1.
    fassert Hx' : (dB (upd (upd rho c C) 1 x) (Wel 1 3)); [rewrite dB_el; envs; rewrite R3; exact Hx|].
    pose proof (dB_imp _ _ _ H1 Hx') as H2. clear H1 Hx'. apply (dB_allE _ _ _ y) in H2.
    set (e2 := upd (upd (upd rho c C) 1 x) 3 y) in *.
    assert (Ek2 : forall k, k + 2 < N -> e2 (2 * k + 5) = sg k).
    { intros k Hk. unfold e2. unfold q in Hqc. envs. apply Rk. }
    fassert Hp : (dB e2 phi);
      [apply (iff_r _ _ _ (phi_eqv th N HN q Hq _ HE e2 x y sg Hnq ltac:(unfold e2; envs; reflexivity)
                              ltac:(unfold e2; envs; reflexivity) Ek2)); exact Hy|].
    pose proof (dB_imp _ _ _ H2 Hp) as H3. clear H2 Hp.
    apply (dB_exE _ _ _ _ H3). intros y'. apply II. ctx_push Hy'.
    apply (ExI y'). simp. fsplit.
    + thnorm_goal th HN sg x y'.
      apply (iff_l _ _ _ (phi_eqv th N HN q Hq _ HE (upd e2 3 y') x y' sg Hnq
                              ltac:(unfold e2; envs; reflexivity) ltac:(envs; reflexivity)
                              ltac:(intros k Hk; envs; apply Ek2; lia))).
      exact (dB_andE1 _ _ _ Hy').
    + pose proof (dB_andE2 _ _ _ Hy') as H4. rewrite dB_el in H4. unfold e2 in H4. envs_in H4. exact H4.
  - apply AllI_named. intros y. simp. apply II. ctx_push Hy. simp_in Hy.
    pose proof (dB_andE2 _ _ _ HC) as H1. apply (dB_allE _ _ _ y) in H1.
    unfold q in Hqc.
    fassert Hy2 : (dB (upd (upd rho c C) 3 y) (Wel 3 c)); [rewrite dB_el; envs; exact Hy|].
    pose proof (dB_imp _ _ _ H1 Hy2) as H2. clear H1 Hy2.
    apply (dB_exE _ _ _ _ H2). intros x. apply II. ctx_push Hx.
    apply (ExI x). thnorm_goal th HN sg x y.
    apply (iff_l _ _ _ (phi_eqv th N HN q Hq _ HE (upd (upd (upd rho c C) 3 y) 1 x) x y sg Hnq
                            ltac:(envs; reflexivity) ltac:(envs; reflexivity)
                            ltac:(intros k Hk; envs; apply Rk))).
    exact Hx.
Qed.

(** ** SIR from TB *)
Local Transparent EqAx Lib.

Lemma SIR_TB psi : SIR psi -> thm TB psi.
Proof.
  intros [[phi Hb | phi n Hc] | ->].
  - unfold Sbase in Hb. destruct Hb as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply TB_EqAx. unfold EqAx. simpl. tauto.
    + apply TB_EqAx. unfold EqAx. simpl. tauto.
    + apply TB_EqAx. unfold EqAx. simpl. tauto.
    + apply TB_EqAx. unfold EqAx. simpl. tauto.
    + exact TB_CP.
  - now apply TB_gic.
  - exact TB_IR.
Qed.

Theorem SIR_to_thm : @tprv _ _ falsity_on class SIR falsity -> thm254 1.
Proof. intro H. apply TB_to_thm. exact (thm_trans _ _ _ H SIR_TB). Qed.
