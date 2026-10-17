(** * Std_brrep: the library's replacement and separation instances (closed over their
    parameters) are derivable from O'Rear's replacement scheme REP, for an ARBITRARY library
    formula [phi], using only the equality axioms.

    For [phi] with [fb (S (S k)) phi] ($0 = domain element, $1 = image, $2.. = parameters) take
    the named wff [phR phi := (v1 = v2 -> tr etaR phi)], where [etaR] sends $0 to v3, $1 to v1 and
    parameter j to v(5+2j) (all odd, so no clash with [tr]'s binder names).  Inside REP,
    [A. v1 phR] is then equivalent to [phi(v3, v2, params)] ([R_equiv]). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen Std_F Std_H Std_iface Std_iface2.
From ZF Require Import Std_setnd Std_setbase Std_breq Std_brnd.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Generic facts about replacement / separation instances *)
Lemma funrel_intro G phi sg : (forall a b b', G ⊢C phi[a .: b .: sg] → phi[a .: b' .: sg] → b ≡' b') ->
  G ⊢C (fun_rel' phi)[sg].
Proof.
  intros Hfun. unfold fun_rel'. cbn. apply AllI_named; intros a. apply AllI_named; intros b. apply AllI_named; intros b'.
  cbn. specialize (Hfun a b b').
  replace (phi[a .: b .: sg]) with (phi[$2 .: $1 .: Nat.add 3 >> var][up (up (up sg))][up (up a..)][up b..][b'..]) in Hfun by form_subst_eq.
  replace (phi[a .: b' .: sg]) with (phi[$2 .: $0 .: Nat.add 3 >> var][up (up (up sg))][up (up a..)][up b..][b'..]) in Hfun by form_subst_eq.
  rewrite subst_term_shift. exact Hfun.
Qed.

Lemma funrel_inst G phi sg a b b' : G ⊢C (fun_rel' phi)[sg] -> G ⊢C phi[a .: b .: sg] -> G ⊢C phi[a .: b' .: sg] ->
  G ⊢C b ≡' b'.
Proof.
  intros H H1 H2. unfold fun_rel' in H. cbn [subst_form] in H.
  apply (AllE a) in H. cbn [subst_form] in H. apply (AllE b) in H. cbn [subst_form] in H.
  apply (AllE b') in H. cbn [subst_form] in H.
  replace (phi[a .: b .: sg]) with (phi[$2 .: $1 .: Nat.add 3 >> var][up (up (up sg))][up (up a..)][up b..][b'..]) in H1 by form_subst_eq.
  replace (phi[a .: b' .: sg]) with (phi[$2 .: $0 .: Nat.add 3 >> var][up (up (up sg))][up (up a..)][up b..][b'..]) in H2 by form_subst_eq.
  pose proof (IE (IE H H1) H2) as H3. cbn in H3. rewrite subst_term_shift in H3. exact H3.
Qed.

Lemma inst_eq (phi : form) w z (sg : nat -> term) :
  phi[w`[↑] .: $0 .: (fun k => (sg k)`[↑])][z..] = phi[w .: z .: sg].
Proof. form_subst_eq. Qed.

(** ** The named formula for a library relation *)
Definition etaR (n : nat) : nat := match n with 0 => 3 | 1 => 1 | S (S j) => 5 + 2 * j end.
Definition phR (phi : form) : wff := Wim (Weq 1 2) (tr etaR phi).
Definition nR (phi : form) : nat := S (maxfr (REP (phR phi))).
Definition repTP (phi : form) : form := Lib (nR phi) (REP (phR phi)).

Lemma repTP_TPset phi : TPset (repTP phi).
Proof. apply TPset_Lib; [apply AX_REP | unfold nR; lia]. Qed.

Lemma etaR_odd n k : etaR n <> bname k.
Proof. unfold bname. destruct n as [|[|j]]; cbn; lia. Qed.

Definition penv (x : term) (sg : nat -> term) (v : nat) : term :=
  if Nat.even v then x else if v <? 5 then x else sg (Nat.div2 (v - 5)).
#[global] Arguments penv : simpl never.

Lemma penv_odd x sg j : penv x sg (5 + 2 * j) = sg j.
Proof.
  unfold penv. assert (E : Nat.even (5 + 2 * j) = false) by (rewrite Nat.even_add, Nat.even_mul; reflexivity).
  rewrite E. destruct (Nat.ltb_spec (5 + 2 * j) 5); [lia|].
  replace (5 + 2 * j - 5) with (2 * j) by lia. now rewrite Nat.div2_double.
Qed.

Lemma penv_0 x sg : penv x sg 0 = x.
Proof. reflexivity. Qed.

Lemma R_equiv G phi k (sg env : nat -> term) w z : incl EqAx G -> fb (S (S k)) phi ->
  env 3 = w -> env 2 = z -> (forall j, j < k -> env (5 + 2 * j) = sg j) ->
  G ⊢C dB env (Wal 1 (phR phi)) ↔ phi[w .: z .: sg].
Proof.
  intros HE Hfb E3 E2 Ej.
  assert (Eu : forall u, phi[fun n => upd env 1 u (etaR n)] = phi[w .: u .: sg]).
  { intros u. apply (subst_ext_fb _ (S (S k))); [exact Hfb|]. intros [|[|j]] Hlt.
    - change (upd env 1 u 3 = w). rewrite upd_neq by lia. exact E3.
    - change (upd env 1 u 1 = u). apply upd_eq.
    - change (upd env 1 u (5 + 2 * j) = sg j). rewrite upd_neq by lia. apply Ej. lia. }
  assert (HT : forall u G', incl EqAx G' -> G' ⊢C dB (upd env 1 u) (tr etaR phi) ↔ phi[w .: u .: sg]).
  { intros u G' HE'. rewrite <- Eu. apply (tr_equiv phi (S (S k))); auto. intros; apply etaR_odd. }
  fsplit.
  - apply II. ctx_push H. pose proof (dB_allE _ _ _ z H) as H1. unfold phR in H1.
    assert (Hzz : Γ ⊢C dB (upd env 1 z) (Weq 1 2)).
    { cbn [dB]. rewrite upd_eq, upd_neq by lia. rewrite E2. apply (eqE_refl HE). }
    exact (iff_l _ _ _ (HT z _ HE) (dB_imp _ _ _ H1 Hzz)).
  - apply II. ctx_push H. apply dB_allI. intros u. unfold phR. apply II. ctx_push Hu.
    cbn [dB] in Hu. rewrite upd_eq, upd_neq in Hu by lia. rewrite E2 in Hu.
    apply (iff_r _ _ _ (HT u _ HE)).
    eapply leibE_gen; [exact HE| |exact H]. intros [|[|n]]; cbn; try apply (eqE_refl HE). apply (eqE_sym HE), Hu.
Qed.

Lemma R_to G phi k (sg env : nat -> term) w z : incl EqAx G -> fb (S (S k)) phi ->
  G ⊢C dB env (Wal 1 (phR phi)) ->
  env 3 = w -> env 2 = z -> (forall j, j < k -> env (5 + 2 * j) = sg j) -> G ⊢C phi[w .: z .: sg].
Proof. intros HE Hfb H E3 E2 Ej. exact (iff_l _ _ _ (R_equiv G phi k sg env w z HE Hfb E3 E2 Ej) H). Qed.

Lemma R_from G phi k (sg env : nat -> term) w z : incl EqAx G -> fb (S (S k)) phi ->
  env 3 = w -> env 2 = z -> (forall j, j < k -> env (5 + 2 * j) = sg j) ->
  G ⊢C phi[w .: z .: sg] -> G ⊢C dB env (Wal 1 (phR phi)).
Proof. intros HE Hfb E3 E2 Ej H. exact (iff_r _ _ _ (R_equiv G phi k sg env w z HE Hfb E3 E2 Ej) H). Qed.

Lemma dB_impI G rho a b : (dB rho a :: G) ⊢C dB rho b -> G ⊢C dB rho (Wim a b).
Proof. intros H. now apply II. Qed.

Definition repH (ph : wff) : wff := Wal 3 (Wex 1 (Wal 2 (Wim (Wal 1 ph) (Weq 2 1)))).
Definition repE (ph : wff) : wff := Wex 3 (Wa (Wel 3 0) (Wal 1 ph)).
Definition repC (ph : wff) : wff := Wex 1 (Wal 2 (Wa (Wim (Wel 2 1) (repE ph)) (Wim (repE ph) (Wel 2 1)))).
Lemma REP_eq ph : REP ph = Wim (repH ph) (repC ph).
Proof. reflexivity. Qed.

Ltac env_eq := intros; repeat (rewrite upd_eq || rewrite upd_neq by lia); first [reflexivity | apply penv_odd].

(** ** Replacement *)
Theorem rep_from_REP G k phi : incl EqAx G -> fb (S (S k)) phi -> G ⊢C repTP phi -> G ⊢C forall_times k (ax_rep' phi).
Proof.
  intros HE Hfb HR. apply ft_intro. intros sg.
  unfold ax_rep'. cbn [subst_form]. apply II. ctx_push Hfr.
  apply AllI_named. intros x.
  assert (Hn : maxfr (REP (phR phi)) < nR phi) by (unfold nR; lia).
  pose proof (Lib_inst _ (nR phi) _ (penv x sg) Hn HR) as H. rewrite REP_eq in H.
  fassert HA : (dB (penv x sg) (repH (phR phi))).
  { unfold repH. apply dB_allI. intros w.
    apply (XM_rule _ (∃ phi[w`[↑] .: $0 .: (fun k => (sg k)`[↑])])).
    - apply II. ctx_push Hex. apply (ExE_named Hex). intros z0. ctx_push Hz0. rewrite inst_eq in Hz0.
      apply (dB_exI _ _ _ z0). apply dB_allI. intros z. apply dB_impI. ctx_push HR1.
      pose proof (R_to _ phi k sg _ w z HE Hfb HR1) as T. specialize (T ltac:(env_eq) ltac:(env_eq) ltac:(env_eq)).
      clear HR1. rename T into HR1.
      cbn [dB]. rewrite upd_eq. rewrite upd_neq by lia. rewrite upd_eq.
      exact (funrel_inst _ phi sg w z z0 Hfr HR1 Hz0).
    - apply II. ctx_push Hnex. apply (dB_exI _ _ _ w). apply dB_allI. intros z. apply dB_impI. ctx_push HR1.
      pose proof (R_to _ phi k sg _ w z HE Hfb HR1) as T. specialize (T ltac:(env_eq) ltac:(env_eq) ltac:(env_eq)).
      clear HR1. rename T into HR1.
      apply Exp. apply (IE Hnex). apply (ExI z). rewrite inst_eq. exact HR1. }
  pose proof (dB_imp _ _ _ H HA) as HC. clear H HA. unfold repC in HC.
  apply (dB_exE _ _ _ _ HC). intros Y. apply II. ctx_push HY.
  apply (ExI Y). cbn [subst_form]. apply AllI_named. intros z.
  simp. rewrite ?subst_comp.
  match goal with |- context [phi[?s]] => replace (phi[s]) with (phi[up (z .: sg)]) by form_subst_eq end.
  fsplit.
  - fintro Hz. pose proof (dB_allE _ _ _ z HY) as H1. apply dB_andE1 in H1.
    pose proof (dB_imp _ _ _ H1 Hz) as H2. unfold repE in H2. apply (dB_exE _ _ _ _ H2). intros w.
    apply II. ctx_push H3. pose proof (dB_andE1 _ _ _ H3) as H4. apply dB_andE2 in H3.
    pose proof (R_to _ phi k sg _ w z HE Hfb H3) as T. specialize (T ltac:(env_eq) ltac:(env_eq) ltac:(env_eq)).
    clear H3. rename T into H3.
    fexists w. fsplit; [exact H4|exact H3].
  - fintro Hz. fex Hz w Hw. fdestr Hw Hw1 Hw2.
    pose proof (dB_allE _ _ _ z HY) as H1. apply dB_andE2 in H1. apply (dB_imp _ _ _ H1).
    unfold repE. apply (dB_exI _ _ _ w). apply dB_andI; [exact Hw1|].
    apply (R_from _ phi k sg _ w z HE Hfb); [env_eq|env_eq|env_eq|exact Hw2].
Qed.

(** ** Separation from replacement *)
Definition sep2rep (phi : form) : form := $0 ≡' $1 ∧ phi[$0 .: (fun k => $(S (S k)))].

Lemma fb_sep2rep k phi : fb (S k) phi -> fb (S (S k)) (sep2rep phi).
Proof.
  intros H. unfold sep2rep. cbn. repeat split; try lia. eapply fb_subst; [exact H|]. intros [|i] Hi; cbn; lia.
Qed.

Theorem sep_from_rep G k phi : incl EqAx G -> fb (S k) phi ->
  G ⊢C forall_times k (ax_rep' (sep2rep phi)) -> G ⊢C forall_times k (ax_sep' phi).
Proof.
  intros HE Hfb H. apply ft_intro. intros sg.
  apply (closed_inst _ _ _ sg (rep_closed _ _ (fb_sep2rep _ _ Hfb))) in H.
  unfold ax_rep' in H. cbn [subst_form] in H.
  assert (Hfr : G ⊢C (fun_rel' (sep2rep phi))[sg]).
  { apply funrel_intro. intros a b b'. unfold sep2rep. cbn [subst_form]. fintro H1. fintro H2.
    fdestr H1 H11 H12. fdestr H2 H21 H22. simp_in H11. simp_in H21. feqE. }
  pose proof (IE H Hfr) as H'. clear H Hfr.
  unfold ax_sep'. cbn [subst_form]. apply AllI_named. intros x. apply (AllE x) in H'.
  apply (ExE_named H'). intros Y. ctx_push HY. apply (ExI Y). apply AllI_named. intros z.
  apply (AllE z) in HY. unfold sep2rep in HY. simp_in HY. simp. rewrite ?subst_comp in HY |- *.
  match goal with |- context [phi[?s]] =>
    assert (EE : phi[z .: sg] = phi[s]) by (rewrite ?subst_comp; apply subst_ext; intros [|[|[|[|[|[|kk]]]]]]; term_eq);
    rewrite <- EE; clear EE end.
  rewrite !subst_comp in HY.
  match type of HY with context [phi[?s]] =>
    assert (EE : phi[up sg] = phi[s]) by (rewrite ?subst_comp; apply subst_ext; intros [|[|[|[|[|[|kk]]]]]]; term_eq);
    rewrite <- EE in HY; clear EE end.
  fsplit.
  - fintro Hz. fhave T : (iff_l _ _ _ HY Hz). fex T w Hw. fdestr Hw Hw1 Hw2. fdestr Hw2 Hwz Hw3.
    fsplit; [fmemE|]. eapply leibE_gen; [exact HE| |exact Hw3]. intros [|n]; cbn; [exact Hwz|apply (eqE_refl HE)].
  - fintro Hz. fdestr Hz Hz1 Hz2. apply (iff_r _ _ _ HY). fexists z. fsplit; [exact Hz1|]. fsplit; [apply (eqE_refl HE)|exact Hz2].
Qed.
