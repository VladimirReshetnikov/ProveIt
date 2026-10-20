(** * Sound222: soundness of the seed-K 222's numerical calculus.

    [thm222 n] implies that the decoded formula [D n] is valid in Elliot Glazer's decoded K230
    theory plus IR ([Sound230.V]).  The retained rows are Sound230's.  The merged equality row G
    is a pure-logic theorem (Euclid's law and equality vacuity at the binder [wel a b], which is
    neither [a] nor [b]).  Each decoded seed bundle is derived from the universally closed K230
    bundle at the same roles: membership vacuity is its first vacuity conjunct, and the seed core
    follows from the output-root core by the classical case split of [KPSeed.output_root_to_seed]
    (an output exists or it does not).  Hence [thm222 1] gives [StandardZFC ⊢TC ⊥]. *)
From Stdlib Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd.
From K230S Require Import KCode230 KP0 KPrimeTheory KDecodeTheory KDecoder230 KDecodeBundle
  KQuotZFC KUpperConsistency.
From K230L Require Import Codes230 Thm230 Sound230 Bridge230.
From K224 Require Import Codes222 Thm222.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** The merged equality row *)
Lemma wel_gt_l a b : a < wel a b.
Proof. unfold wel. pose proof (P_ge_l a b). lia. Qed.
Lemma wel_gt_r a b : b < wel a b.
Proof. unfold wel. pose proof (P_ge_r a b). lia. Qed.

Lemma lprov_G a b c : lprov (Wim (Weq c a) (Wim (Weq c b) (Wal (wel a b) (Weq a b)))).
Proof.
  assert (Hv : lprov (Wim (Weq a b) (Wal (wel a b) (Weq a b)))).
  { apply (LDET _ _ (lpc_andl _ (Wim (Wel a b) (Wal (wel a b) (Wel a b))))). apply LB6a.
    - pose proof (wel_gt_l a b). lia.
    - pose proof (wel_gt_r a b). lia. }
  apply der_lprov. do 2 apply ded.
  apply (dmp _ (Weq a b)); [apply dthm, Hv|].
  apply (dmp _ (Weq c b)); [|apply dhyp; simpl; tauto].
  apply (dmp _ (Weq c a)); [apply dthm, LB8a|apply dhyp; simpl; tauto].
Qed.

Local Opaque wim wel wal weq P.

Lemma V_rG a b c : V (D (growG a b c)).
Proof.
  unfold growG.
  assert (Ea : E (D (wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))))
                 (Wim (Weq c a) (Wim (Weq c b) (Wal (wel a b) (Weq a b))))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)). apply V_lprov, lprov_G.
Qed.

Local Transparent wim wel wal weq P.

(** ** The decoded seed bundle *)
Definition KClosE (a b k : nat) (q : wff) : wff :=
  Wal b (Wim (Wel b k) (Wex a (Wa q (Wal a (Wim (KSubset a b k) (KRequest b k q)))))).
Definition KRV (a b c : nat) : wff := Wim (Wel a b) (Wal c (Wel a b)).
Definition SeedY (a b c : nat) (q : wff) : wff :=
  Wn (Wim (KRV a b c) (Wal c (Wim (KClosE a b c q) (Wn (KRequest b c q))))).

(** the exact decoding, before double-negation normalization *)
Definition ReqN (b k : nat) (q : wff) : wff := Wal b (Wim q (Wn (Wal b (Wim q (Wn (Wel b k)))))).
Definition ClosN (a b k : nat) (q : wff) : wff :=
  Wal b (Wim (Wel b k) (Wn (Wal a (Wim q (Wn (Wal a (Wim (KSubset a b k) (ReqN b k q)))))))).
Definition SeedN (a b c : nat) (q : wff) : wff :=
  Wn (Wim (KRV a b c) (Wal c (Wim (ClosN a b c q) (Wn (ReqN b c q))))).

Lemma D_wimF a : D (wim a F) = Wn (D a).
Proof. exact (D_wn a). Qed.

Ltac kside := first
  [ assumption | congruence | apply wel_nonzero | apply wal_nonzero | apply wn_nonzero
  | apply wal_ne_F | apply wim_ne_F | apply wel_nonone; congruence
  | apply pair_nonzero_r; kside ].
Ltac kdec := repeat first
  [ rewrite D_wimF | rewrite D_wal | rewrite D_wel | rewrite D_weq
  | rewrite D_wim by kside ].

Lemma D_bundle222 a b c : c <> b -> D (bundle222 a b c) = SeedN a b c (D c).
Proof.
  intros Hcb. unfold bundle222, nks222, vrel, wn. kdec. reflexivity.
Qed.

Lemma E_dn p : E (Wn (Wn p)) p.
Proof. split; apply V_lprov; [apply lpc_nn_elim | apply lpc_nn_intro]. Qed.

Lemma E_req b k q : E (ReqN b k q) (KRequest b k q).
Proof.
  unfold ReqN, KRequest, Wex, Wa.
  apply E_al, E_im; [apply E_refl|]. apply E_n, E_al. apply E_sym, E_dn.
Qed.

Lemma E_clos a b k q : E (ClosN a b k q) (KClosE a b k q).
Proof.
  unfold ClosN, KClosE, Wex, Wa.
  apply E_al, E_im; [apply E_refl|]. apply E_n, E_al.
  eapply E_trans; [|apply E_sym, E_dn].
  apply E_im; [apply E_refl|]. apply E_n, E_al, E_im; [apply E_refl|]. apply E_req.
Qed.

Lemma E_seed a b c q : E (SeedN a b c q) (SeedY a b c q).
Proof.
  unfold SeedN, SeedY. apply E_n, E_im; [apply E_refl|]. apply E_al, E_im.
  - apply E_clos.
  - apply E_n, E_req.
Qed.

(** ** The seed bundle from the closed output-root bundle, in natural deduction *)
Lemma fr_wal_self x a : fr x (Wal x a) = false.
Proof. cbn [fr]. now rewrite Nat.eqb_refl. Qed.

Lemma dB_upd_irrel rho x t a : fr x a = false -> dB (upd rho x t) a = dB rho a.
Proof.
  intros H. apply dB_ext_fr. intros v Hv. unfold upd.
  destruct (Nat.eqb_spec v x) as [->|]; [congruence|reflexivity].
Qed.

Lemma upd_comm rho x y s t : x <> y -> forall v, upd (upd rho x s) y t v = upd (upd rho y t) x s v.
Proof.
  intros H v. unfold upd. destruct (Nat.eqb_spec v y), (Nat.eqb_spec v x); subst; congruence.
Qed.

Lemma upd_upd rho x s t : forall v, upd (upd rho x s) x t v = upd rho x t v.
Proof. intros v. unfold upd. destruct (Nat.eqb_spec v x); reflexivity. Qed.

Section SeedFromCore.
Variables (a b c : nat) (q : wff).
Hypothesis Hcb : c <> b.
Hypothesis Hfresh : fr c q = false.

(** q does not see the container label *)
Lemma q_container rho C t :
  dB (upd (upd rho c C) b t) q = dB (upd rho b t) q.
Proof.
  rewrite (dB_ext (rho := (upd (upd rho c C) b t)) (rho' := (upd (upd rho b t) c C)) q) by (apply upd_comm; congruence).
  apply dB_upd_irrel, Hfresh.
Qed.

(** The closure does not see the output variable (it binds it). *)
Lemma clos_output rho t C :
  dB (upd (upd rho b t) c C) (KClosE a b c q) = dB (upd rho c C) (KClosE a b c q).
Proof.
  rewrite (dB_ext (rho := (upd (upd rho b t) c C)) (rho' := (upd (upd rho c C) b t)) (KClosE a b c q)) by (apply upd_comm; congruence).
  apply dB_upd_irrel. unfold KClosE. apply fr_wal_self.
Qed.

Lemma member_value rho t C :
  dB (upd (upd rho b t) c C) (Wel b c) = (t ∈' C).
Proof.
  cbn [dB]. rewrite upd_eq, upd_neq by congruence. now rewrite upd_eq.
Qed.

(** the seed request holds at a container that receives one output witness *)
Lemma request_from_witness G rho t C :
  G ⊢C dB (upd rho b t) q -> G ⊢C (t ∈' C) ->
  G ⊢C dB (upd rho c C) (KRequest b c q).
Proof.
  intros Hq HtC. unfold KRequest. apply dB_allI. intros s. apply II.
  apply (dB_exI _ b _ t).
  rewrite (dB_ext (rho := (upd (upd (upd rho c C) b s) b t)) (rho' := (upd (upd rho c C) b t)) (Wa q (Wel b c))) by apply upd_upd.
  apply dB_andI.
  - rewrite (q_container rho C t). apply weak_cons, Hq.
  - rewrite (dB_ext (rho := (upd (upd rho c C) b t)) (rho' := (upd (upd rho b t) c C)) (Wel b c)) by (apply upd_comm; congruence).
    rewrite member_value. apply weak_cons, HtC.
Qed.

(** the seed request holds vacuously when no output exists *)
Lemma request_vacuous G rho C :
  G ⊢C ¬ dB rho (Wex b q) -> G ⊢C dB (upd rho c C) (KRequest b c q).
Proof.
  intros Hnone. unfold KRequest. apply dB_allI. intros s. apply II. apply Exp.
  eapply IE; [apply weak_cons, Hnone|].
  apply (dB_exI _ b _ s). rewrite <- (q_container rho C s). apply Ctx. now left.
Qed.

Lemma seed_from_core G :
  (forall rho, G ⊢C dB rho (KBundle a b c q)) -> forall rho, G ⊢C dB rho (SeedY a b c q).
Proof.
  intros Hb rho. unfold SeedY.
  change (G ⊢C dB rho (Wim (KRV a b c) (Wal c (Wim (KClosE a b c q) (Wn (KRequest b c q))))) → ⊥).
  apply II.
  set (G1 := dB rho (Wim (KRV a b c) (Wal c (Wim (KClosE a b c q) (Wn (KRequest b c q))))) :: G).
  assert (Hb1 : forall r, G1 ⊢C dB r (KBundle a b c q)) by (intros r; apply weak_cons, Hb).
  assert (HRV : G1 ⊢C dB rho (KRV a b c)).
  { pose proof (dB_andE2 _ _ _ (Hb1 rho)) as Hv. unfold KVacuity in Hv.
    exact (dB_andE1 _ _ _ Hv). }
  assert (HNK : G1 ⊢C dB rho (Wal c (Wim (KClosE a b c q) (Wn (KRequest b c q))))).
  { apply (dB_imp _ (KRV a b c)); [apply Ctx; now left|exact HRV]. }
  (* a container with the closure and the seed request refutes the hypothesis *)
  assert (Hkill : forall G2 C, incl G1 G2 -> G2 ⊢C dB (upd rho c C) (KClosE a b c q) ->
            G2 ⊢C dB (upd rho c C) (KRequest b c q) -> G2 ⊢C ⊥).
  { intros G2 C HG Hcl Hrq. pose proof (dB_allE _ _ _ C (Weak HNK HG)) as H.
    exact (dB_neg _ _ (dB_imp _ _ _ H Hcl) Hrq). }
  apply (XM_rule G1 (dB rho (Wex b q))).
  - (* an output exists *)
    apply II. apply (dB_exE rho b q ⊥); [apply Ctx; now left|]. intros t. apply II.
    set (G2 := dB (upd rho b t) q :: dB rho (Wex b q) :: G1).
    assert (HG : incl G1 G2) by (intros f Hf; right; right; exact Hf).
    pose proof (Weak (Hb1 (upd rho b t)) HG) as Hk.
    pose proof (dB_andE1 _ _ _ Hk) as Hcore. unfold KCore in Hcore.
    apply (dB_exE _ c _ ⊥ Hcore). intros C. apply II.
    set (G3 := dB (upd (upd rho b t) c C) (Wa (Wim q (Wel b c)) (KClosE a b c q)) :: G2).
    assert (HG3 : incl G1 G3) by (intros f Hf; right; apply HG, Hf).
    assert (HC : G3 ⊢C dB (upd (upd rho b t) c C) (Wa (Wim q (Wel b c)) (KClosE a b c q)))
      by (apply Ctx; now left).
    apply (Hkill G3 C HG3).
    + rewrite <- (clos_output rho t C). exact (dB_andE2 _ _ _ HC).
    + apply (request_from_witness G3 rho t C).
      * apply Ctx. right. now left.
      * rewrite <- (member_value rho t C).
        apply (dB_imp _ q); [exact (dB_andE1 _ _ _ HC)|].
        rewrite (dB_ext (rho := (upd (upd rho b t) c C)) (rho' := (upd (upd rho c C) b t)) q) by (apply upd_comm; congruence).
        rewrite (q_container rho C t). apply Ctx. right. now left.
  - (* no output: any container from the core works *)
    apply II.
    set (G2 := (¬ dB rho (Wex b q)) :: G1).
    assert (HG : incl G1 G2) by (intros f Hf; right; exact Hf).
    pose proof (Weak (Hb1 rho) HG) as Hk.
    pose proof (dB_andE1 _ _ _ Hk) as Hcore. unfold KCore in Hcore.
    apply (dB_exE _ c _ ⊥ Hcore). intros C. apply II.
    set (G3 := dB (upd rho c C) (Wa (Wim q (Wel b c)) (KClosE a b c q)) :: G2).
    assert (HG3 : incl G1 G3) by (intros f Hf; right; apply HG, Hf).
    apply (Hkill G3 C HG3).
    + apply (dB_andE2 _ (Wim q (Wel b c))). apply Ctx. now left.
    + apply request_vacuous. apply Ctx. right. now left.
Qed.

End SeedFromCore.

(** ** Validity of the decoded seed bundle in the decoded K230 theory *)
Lemma V_bundle222 a b c : c <> a -> c <> b -> V (D (bundle222 a b c)).
Proof.
  intros Hca Hcb. rewrite (D_bundle222 a b c Hcb).
  apply (E_V _ _ (E_sym _ _ (E_seed a b c (D c)))).
  set (n := S (maxfr (D (gated230 a b c)))).
  exists [Lib n (D (gated230 a b c))]. split.
  - intros psi [<-|[]]. left. apply DecodedK230Ord_bundle. unfold n. lia.
  - apply (seed_from_core a b c (D c) Hcb (D_fr_self c)). intros rho.
    rewrite <- (D_gated230_enabled a b c Hca Hcb).
    apply (Lib_inst _ n _ rho); [unfold n; lia|]. apply Ctx. now left.
Qed.

(** ** Soundness *)
Theorem thm222_V n : thm222 n -> V (D n).
Proof.
  induction 1 as [| t b _ IH1 _ IH2 | a hh _ IH | a b | a b c | a b c | a b c | a b c | a b
                  | a b c | a b c u | a b c H1 H2].
  - rewrite D_0. apply V_lprov, T0_prov.
  - destruct (D_wim_E t b) as [H _]. exact (V_mp _ _ (V_mp _ _ H IH2) IH1).
  - rewrite D_wal. now apply V_gen.
  - apply V_r1.
  - apply V_r2.
  - apply V_r3.
  - apply V_r4.
  - apply V_r5.
  - apply V_r6.
  - apply V_rG.
  - apply V_r8.
  - exact (V_bundle222 a b c H1 H2).
Qed.

Theorem thm222_to_DecodedK230IR : thm222 1 -> @tprv _ _ falsity_on class DecodedK230IR falsity.
Proof.
  intro H. apply thm222_V in H. change 1 with (wel 0 0) in H. rewrite D_wel in H.
  destruct H as [A [HA Hd]]. exists (irreflexivity :: A). split.
  - intros psi [<-|Hp]; [now right | exact (HA psi Hp)].
  - specialize (Hd var). cbn [dB] in Hd.
    eapply IE; [|eapply Weak; [exact Hd | intros z Hz; now right]].
    change (¬ $0 ∈' $0) with ((¬ $0 ∈' $0)[($0)..]). apply AllE. apply Ctx. now left.
Qed.

Theorem thm222_sound : thm222 1 -> StandardZFC ⊢TC ⊥.
Proof.
  intros H. apply KPrimeOrdIR_standardZFC_inconsistent.
  apply decodedIR_to_KPrimeOrdIR, thm222_to_DecodedK230IR, H.
Qed.

Print Assumptions thm222_sound.

