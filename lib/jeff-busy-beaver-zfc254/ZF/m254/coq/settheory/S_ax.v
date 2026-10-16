(** * S_ax: S0 proves the translation of every axiom of ZF0 + INF_lib

    ZF0 is Std_iface's ZF without infinity (equality axioms, extensionality, empty set, pairing,
    union, power set, closed separation and replacement instances); INF_lib is O'Rear's
    Zermelo-style infinity axiom (every x lies in a set closed under singletons), from which ZF0
    derives the library's [ax_om'] (Std_setinf.inf_or_to_zf).

    Fixed instances: [Sq] (S_quot) and [Sq_ax] (raw subsets of a set, raw trace of an interpreted
    subset).  Each separation / replacement instance uses one more GIC closure, built from the
    translated formula. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_rel Z_base.
From M254S Require Import S_def S_qt S_gic S_raw S_quot.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

(** raw subsets of a ($1): Sub0 r a;  raw trace of X ($1): Mem u X *)
Definition psi_sub : form := Sub0 $0 $1.
Definition psi_trace : form := Mem $0 $1.
Definition Sq_ax : list form :=
  [forall_times 2 (gic (sep_th psi_sub)); forall_times 2 (gic (sep_th psi_trace))].

Lemma Sq_ax_ok a : In a Sq_ax -> S0 a.
Proof.
  intros [<-|[<-|[]]]; apply S0_gic, gic_closed, (fb_sep_th 1);
    unfold psi_sub, psi_trace, Sub0, Mem, Eqv, Bisim, App0, OP0, Sing0, Pair0; cbn; lia.
Qed.

Definition B0 : list form := Sbase ++ Sq ++ Sq_ax.

Lemma B0_ok a : In a B0 -> S0 a.
Proof.
  intros H. apply in_app_or in H as [H|H]; [now constructor|].
  apply in_app_or in H as [H|H]; [now apply Sq_ok | now apply Sq_ax_ok].
Qed.

Lemma B0_closed a : In a B0 -> closedf a.
Proof. intros H. now apply S0_closed, B0_ok. Qed.

Lemma B0_base : incl Sbase B0.
Proof. intros a Ha. apply in_or_app. now left. Qed.

Lemma B0_q : incl Sq B0.
Proof. intros a Ha. apply in_or_app. right. apply in_or_app. now left. Qed.

Lemma B0_ax : incl Sq_ax B0.
Proof. intros a Ha. apply in_or_app. right. apply in_or_app. now right. Qed.

(** prove a translated axiom from an abstract closed context containing B0 *)
Lemma by_B0 phi : (forall G, incl Sbase G -> incl Sq G -> (forall a, In a G -> closedf a) -> G ⊢C phi) ->
  S0 ⊢TC phi.
Proof.
  intros H. exists B0. split; [exact B0_ok|]. apply H; [exact B0_base | exact B0_q | exact B0_closed].
Qed.

Lemma by_B0x phi : (forall G, incl Sbase G -> incl Sq G -> incl Sq_ax G -> (forall a, In a G -> closedf a) ->
  G ⊢C phi) -> S0 ⊢TC phi.
Proof.
  intros H. exists B0. split; [exact B0_ok|].
  apply H; [exact B0_base | exact B0_q | exact B0_ax | exact B0_closed].
Qed.

Ltac fb_solve2 := unfold psi_sub, psi_trace, Sub0, Mem, Eqv, Bisim, App0, OP0, Sing0, Pair0; cbn; lia.

(** one more closed instance on top of B0 *)
Lemma by_B0i inst phi : S0 inst ->
  (forall G, incl Sbase G -> incl Sq G -> In inst G -> G ⊢C phi) -> S0 ⊢TC phi.
Proof.
  intros Hi H. exists (inst :: B0). split.
  - intros a [<-|Ha]; [exact Hi | now apply B0_ok].
  - apply H; [intros a Ha; right; now apply B0_base | intros a Ha; right; now apply B0_q | now left].
Qed.

Ltac gen_closed := apply AllI_closed; [assumption|].

Lemma S_refl : S0 ⊢TC qtS ax_refl'.
Proof. apply by_B0. intros G HB HQ HC. cbn. gen_closed. apply (eqv_refl HB HQ). Qed.

Lemma S_sym : S0 ⊢TC qtS ax_sym'.
Proof.
  apply by_B0. intros G HB HQ HC. cbn. gen_closed. gen_closed.
  fintro H1. exact (eqv_sym HB HQ _ _ H1).
Qed.

Lemma S_trans : S0 ⊢TC qtS ax_trans'.
Proof.
  apply by_B0. intros G HB HQ HC. cbn. gen_closed. gen_closed. gen_closed.
  fintro H1. fintro H2. exact (eqv_trans HB HQ _ _ _ H1 H2).
Qed.

Lemma S_eq_elem : S0 ⊢TC qtS ax_eq_elem'.
Proof.
  apply by_B0. intros G HB HQ HC. cbn. gen_closed. gen_closed. gen_closed. gen_closed.
  fintro H1. fintro H2. fintro H3.
  apply (mem_l HB HQ $3); [exact H1|]. exact (mem_r HB HQ _ _ _ H2 H3).
Qed.

Lemma S_ext : S0 ⊢TC qtS ax_ext'.
Proof.
  apply by_B0. intros G HB HQ HC. cbn. gen_closed. gen_closed.
  fintro H1. fintro H2. exact (eqv_ext HB HQ _ _ H1 H2).
Qed.

(** a raw empty set has no interpreted members *)
Lemma S_eset : S0 ⊢TC qtS ax_eset'.
Proof.
  apply by_B0. intros G HB HQ HC. pose proof (Sq_raw_of HQ) as HR.
  unfold qtS, ax_eset', is_eset. cbn.
  fobtain (emp_ex HB HR) as e He. fexists e. fall z. fintro H. unfold Mem in H.
  fex H u Hu. fdestr Hu Hue Hzu. exact (emp_not e u He Hue).
Qed.

(** an exact raw pair *)
Lemma S_pair : S0 ⊢TC qtS ax_pair'.
Proof.
  apply by_B0. intros G HB HQ HC. pose proof (Sq_raw_of HQ) as HR. pose proof (HE HB) as HE.
  unfold qtS, ax_pair', is_pair. cbn. gen_closed. gen_closed.
  fobtain (pair_ex HB HR $1 $0) as p Hp. fexists p. fall z. fsplit.
  - fintro H. unfold Mem in H. fex H u Hu. fdestr Hu Hup Hzu.
    fhave E : (pair0_el HE $1 $0 p u Hp Hup). fcases E E1 E2.
    + fleft. exact (eqv_trans HB HQ _ _ _ Hzu (eqv_of_eq HB HQ _ _ E1)).
    + fright. exact (eqv_trans HB HQ _ _ _ Hzu (eqv_of_eq HB HQ _ _ E2)).
  - fintro H. unfold Mem. fcases H H1 H2.
    + fexists $1. fsplit; [exact (pair0_inl HE _ _ p Hp) | exact H1].
    + fexists $0. fsplit; [exact (pair0_inr HE _ _ p Hp) | exact H2].
Qed.

(** raw union *)
Lemma S_union : S0 ⊢TC qtS ax_union'.
Proof.
  apply by_B0. intros G HB HQ HC. pose proof (Sq_raw_of HQ) as HR. pose proof (HE HB) as HE.
  unfold qtS, ax_union', is_union. cbn. gen_closed.
  fobtain (union_ex HB HR $0) as U HU. fexists U. fall z. fsplit.
  - fintro H. unfold Mem in H. fex H v Hv. fdestr Hv HvU Hzv.
    fhave T : (union0_el $0 U v HU HvU). fex T w Hw. fdestr Hw Hw0 Hvw.
    fexists w. fsplit; [exact (mem_raw HB HQ w $0 Hw0)|]. unfold Mem. fexists v. fsplit; [exact Hvw | exact Hzv].
  - fintro H. fex H w Hw. fdestr Hw Hw0 Hzw.
    unfold Mem in Hw0. fex Hw0 w' Hw'. fdestr Hw' Hw'0 Eww'.
    fhave Hzw' : (mem_r HB HQ z w w' Eww' Hzw).
    unfold Mem in Hzw'. fex Hzw' v Hv. fdestr Hv Hvw' Hzv.
    unfold Mem. fexists v. fsplit; [exact (union0_in $0 U w' v HU Hw'0 Hvw') | exact Hzv].
Qed.

(** raw subsets of a collected by CP + separation; an interpreted subset X is ≈ its raw trace
    {u ∈ a | Mem u X} (quotient extensionality) *)
Lemma S_power : S0 ⊢TC qtS ax_power'.
Proof.
  apply by_B0x. intros G HB HQ HA HC. pose proof (Sq_raw_of HQ) as HR. pose proof (HE HB) as HE.
  unfold qtS, ax_power', is_power, sub'. cbn. gen_closed.
  fobtain (cp_ex HB $0) as V HV0. fdestr HV0 HaV HV.
  fobtain (cp_pow V $0 HV HaV) as W HW0. fdestr HW0 HWV HW.
  pose proof (HA (forall_times 2 (gic (sep_th psi_sub))) ltac:(cbn; tauto)) as Hin.
  pose proof (sepS_use _ 1 psi_sub ($0 .: var) W HE Hin ltac:(fb_solve2)) as T.
  fex T P HP. unfold psi_sub in HP. simp_in HP.
  fexists P. fall X. fsplit.
  - fintro H. unfold Mem in H. fex H r Hr. fdestr Hr HrP HXr. finst HP r.
    fhave T : (iff_l _ _ _ HP HrP). fdestr T HrW Hra.
    fall z. fintro Hz. fhave Hzr : (mem_r HB HQ z X r HXr Hz). unfold Mem in Hzr. fex Hzr u Hu.
    fdestr Hu Hur Hzu. unfold Mem. fexists u. fsplit; [|exact Hzu].
    unfold Sub0 in Hra. finst Hra u. exact (IE Hra Hur).
  - fintro Hsub.
    pose proof (HA (forall_times 2 (gic (sep_th psi_trace))) ltac:(cbn; tauto)) as Hin2.
    pose proof (sepS_use _ 1 psi_trace (X .: var) $0 HE Hin2 ltac:(fb_solve2)) as T.
    fex T r Hr. unfold psi_trace in Hr. simp_in Hr.
    fassert Hra : (Sub0 r $0).
    { unfold Sub0. fall u. fintro Hu. finst Hr u. exact (CE1 (iff_l _ _ _ Hr Hu)). }
    fassert HrP : (r ∈' P).
    { finst HP r. apply (iff_r _ _ _ HP). fsplit; [finst HW r; exact (IE HW Hra) | exact Hra]. }
    fassert HXr : (Eqv X r).
    { apply (eqv_ext HB HQ).
      - fall z. fintro Hz. pose proof Hsub as T. finst T z. fmp T Hz. unfold Mem in T. fex T u Hu.
        fdestr Hu Hua Hzu. unfold Mem. fexists u. fsplit; [|exact Hzu].
        finst Hr u. apply (iff_r _ _ _ Hr). fsplit; [exact Hua | exact (mem_l HB HQ z u X Hzu Hz)].
      - fall z. fintro Hz. unfold Mem in Hz. fex Hz u Hu. fdestr Hu Hur Hzu. finst Hr u.
        fhave T : (iff_l _ _ _ Hr Hur). fdestr T Hua HuX.
        exact (mem_l HB HQ u z X (eqv_sym HB HQ _ _ Hzu) HuX). }
    unfold Mem. fexists r. fsplit; [exact HrP | exact HXr].
Qed.

(** the CP container of x is raw-closed under singletons *)
Lemma S_inf : S0 ⊢TC qtS INF_lib.
Proof.
  apply by_B0. intros G HB HQ HC. pose proof (Sq_raw_of HQ) as HR. pose proof (HE HB) as HE.
  unfold qtS, INF_lib. cbn. gen_closed.
  fobtain (cp_ex HB $0) as V HV0. fdestr HV0 HxV HV.
  fexists V. fsplit; [exact (mem_raw HB HQ $0 V HxV)|].
  fall u. fintro Hu. unfold Mem in Hu. fex Hu u' Hu'. fdestr Hu' Hu'V Huu'.
  fobtain (pair_ex HB HR u' u') as s Hs.
  fobtain (cp_pow V u' HV Hu'V) as W1 HW10. fdestr HW10 HW1V HW1.
  fassert Hu'W1 : (u' ∈' W1).
  { finst HW1 u'. apply (IE HW1). unfold Sub0. fall z. fintro Hz. exact Hz. }
  fobtain (cp_pow V W1 HV HW1V) as W2 HW20. fdestr HW20 HW2V HW2.
  fassert HsW2 : (s ∈' W2).
  { finst HW2 s. apply (IE HW2). unfold Sub0. fall z. fintro Hz.
    fhave E : (pair0_el HE u' u' s z Hs Hz). fcases E E1 E2; fmemE. }
  fhave HsV : (cp_trans V W2 s HV HW2V HsW2).
  fexists s. fsplit; [exact (mem_raw HB HQ s V HsV)|].
  fall w. fsplit.
  - fintro Hw. unfold Mem in Hw. fex Hw v Hv. fdestr Hv Hvs Hwv.
    fhave E : (pair0_el HE u' u' s v Hs Hvs).
    fassert Evu : (v ≡' u'); [fcases E E1 E2; [exact E1 | exact E2]|].
    apply (eqv_trans HB HQ _ v); [exact Hwv|].
    apply (eqv_trans HB HQ _ u'); [exact (eqv_of_eq HB HQ _ _ Evu) | exact (eqv_sym HB HQ _ _ Huu')].
  - fintro Hw. unfold Mem. fexists u'.
    fsplit; [exact (pair0_inl HE u' u' s Hs) | exact (eqv_trans HB HQ _ _ _ Hw Huu')].
Qed.

(** raw separation by qtS phi (one GIC instance), invariance qt_inv *)
Lemma sep_core G N phi : incl Sbase G -> incl Sq G ->
  In (forall_times (S N) (gic (sep_th (qtS phi)))) G -> fb (S N) (qtS phi) ->
  G ⊢C qtS (ax_sep' phi).
Proof.
  intros HB HQ Hin Hfb. pose proof (HE HB) as HE.
  unfold ax_sep'. unfold qtS at 1. cbn. rewrite <- (qt_subst _ _ Eqv_subst Mem_subst). fold (qtS phi).
  fall a.
  pose proof (sepS_use _ N (qtS phi) var a HE Hin Hfb) as T. fex T b Hb.
  fexists b. fall z. fsplit.
  - fintro H. unfold Mem in H. fex H u Hu. fdestr Hu Hub Hzu. finst Hb u.
    fhave T : (iff_l _ _ _ Hb Hub). fdestr T Hua Hpu. fsplit.
    + unfold Mem. fexists u. fsplit; [exact Hua | exact Hzu].
    + fassert Hpu' : ((qtS phi)[u .: var]); [fconv_h Hpu|].
      pose proof (qt_inv phi _ (u .: var) (z .: var) HB HQ) as I.
      specialize (I ltac:(intros [|n]; cbn; [exact (eqv_sym HB HQ _ _ Hzu) | apply (eqv_refl HB HQ)]) Hpu').
      fconv_h I.
  - fintro H. fdestr H Hza Hpz. unfold Mem in Hza. fex Hza u Hu. fdestr Hu Hua Hzu.
    fassert Hpz' : ((qtS phi)[z .: var]); [fconv_h Hpz|].
    pose proof (qt_inv phi _ (z .: var) (u .: var) HB HQ) as I.
    specialize (I ltac:(intros [|n]; cbn; [exact Hzu | apply (eqv_refl HB HQ)]) Hpz').
    fassert Hub : (u ∈' b).
    { finst Hb u. apply (iff_r _ _ _ Hb). fsplit; [exact Hua | fconv_h I]. }
    unfold Mem. fexists u. fsplit; [exact Hub | exact Hzu].
Qed.

Lemma S_sep_open phi : S0 ⊢TC qtS (ax_sep' phi).
Proof.
  destruct (fb_exists (qtS phi)) as [N HN].
  assert (Hfb : fb (S N) (qtS phi)) by (eapply fb_mono; [exact HN | lia]).
  apply (by_B0i (forall_times (S N) (gic (sep_th (qtS phi))))).
  - apply S0_gic, gic_closed, fb_sep_th, Hfb.
  - intros G HB HQ Hin. exact (sep_core G N phi HB HQ Hin Hfb).
Qed.

(** GIC with the raw domain guard u ∈ a, invariance, functionality modulo ≈ *)
Definition th_rep (psi : form) : form := $0 ∈' $2 ∧ psi[$0 .: $1 .: (fun k => $(3 + k))].

Lemma fb_th_rep N psi : fb (S (S N)) psi -> fb (S (S (S N))) (th_rep psi).
Proof.
  intros H. unfold th_rep. cbn. repeat split; try lia.
  eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma rep_core G N phi : incl Sbase G -> incl Sq G ->
  In (forall_times (S N) (gic (th_rep (qtS phi)))) G -> fb (S (S N)) (qtS phi) ->
  G ⊢C qtS (ax_rep' phi).
Proof.
  intros HB HQ Hin Hfb. pose proof (HE HB) as HE.
  unfold ax_rep', fun_rel'. unfold qtS at 1. cbn. rewrite <- !(qt_subst _ _ Eqv_subst Mem_subst). fold (qtS phi).
  fintro Hfun. fall a.
  pose proof (gic_use _ (S N) (th_rep (qtS phi)) (a .: var) a Hin (fb_th_rep N _ Hfb)) as T.
  fex T C HC. fdestr HC Hcov Hnx. unfold th_rep in Hcov, Hnx. simp_in Hcov. simp_in Hnx.
  fexists C. fall z. fsplit.
  - fintro H. unfold Mem in H. fex H v Hv. fdestr Hv HvC Hzv. finst Hnx v. fmp Hnx HvC.
    fex Hnx u Hu. fdestr Hu Hua Hpuv. fexists u. fsplit; [exact (mem_raw HB HQ u a Hua)|].
    fassert Hp1 : ((qtS phi)[u .: v .: var]); [fconv_h Hpuv|].
    pose proof (qt_inv phi _ (u .: v .: var) (u .: z .: var) HB HQ) as I.
    specialize (I ltac:(intros [|[|n]]; cbn; [apply (eqv_refl HB HQ) | exact (eqv_sym HB HQ _ _ Hzv) | apply (eqv_refl HB HQ)]) Hp1).
    fconv_h I.
  - fintro H. fex H u Hu. fdestr Hu Hua Hpuz. unfold Mem in Hua. fex Hua u' Hu'. fdestr Hu' Hu'a Huu'.
    fassert Hp1 : ((qtS phi)[u .: z .: var]); [fconv_h Hpuz|].
    pose proof (qt_inv phi _ (u .: z .: var) (u' .: z .: var) HB HQ) as I.
    specialize (I ltac:(intros [|[|n]]; cbn; [exact Huu' | apply (eqv_refl HB HQ) | apply (eqv_refl HB HQ)]) Hp1).
    finst Hcov u'. fmp Hcov Hu'a. finst Hcov z.
    fassert Hth : (u' ∈' a ∧ (qtS phi)[u' .: z .: var]); [fsplit; [exact Hu'a | exact I]|].
    fmp_conv Hcov Hth. fex Hcov y Hy. fdestr Hy Hy1 HyC. fdestr Hy1 Hu'a' Hpy.
    finst Hfun u' z y. fmp_conv Hfun I. fmp_conv Hfun Hpy.
    unfold Mem. fexists y. fsplit; [exact HyC | exact Hfun].
Qed.

Lemma S_rep_open phi : S0 ⊢TC qtS (ax_rep' phi).
Proof.
  destruct (fb_exists (qtS phi)) as [N HN].
  assert (Hfb : fb (S (S N)) (qtS phi)) by (eapply fb_mono; [exact HN | lia]).
  apply (by_B0i (forall_times (S N) (gic (th_rep (qtS phi))))).
  - apply S0_gic, gic_closed, fb_th_rep, Hfb.
  - intros G HB HQ Hin. exact (rep_core G N phi HB HQ Hin Hfb).
Qed.

Lemma S_sep n phi : S0 ⊢TC qtS (forall_times n (ax_sep' phi)).
Proof.
  unfold qtS. rewrite qt_forall_times. apply tprv_forall_times; [exact S0_closed|]. apply S_sep_open.
Qed.

Lemma S_rep n phi : S0 ⊢TC qtS (forall_times n (ax_rep' phi)).
Proof.
  unfold qtS. rewrite qt_forall_times. apply tprv_forall_times; [exact S0_closed|]. apply S_rep_open.
Qed.

Theorem S_ZF0inf a : (ZF0 a \/ a = INF_lib) -> S0 ⊢TC qtS a.
Proof.
  intros [[a' H | phi n _ | phi n _] | ->].
  - repeat (destruct H as [<-|H];
      [first [apply S_refl | apply S_sym | apply S_trans | apply S_eq_elem | apply S_ext
             | apply S_eset | apply S_pair | apply S_union | apply S_power] |]).
    destruct H.
  - apply S_sep.
  - apply S_rep.
  - apply S_inf.
Qed.
