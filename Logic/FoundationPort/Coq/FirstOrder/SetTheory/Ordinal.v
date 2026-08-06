(**
    Transitive sets and ordinals, ported from
    [Foundation/FirstOrder/SetTheory/Ordinal.lean].

    The source presents these predicates through the concrete first-order
    universe and a large notation/type-class layer.  This file isolates the
    mathematical content over an arbitrary membership structure equipped with
    the explicit Zermelo operations from [Z.v].  In particular, no syntax or
    definability witness is needed by any theorem below.
*)

From Stdlib Require Import Logic.Classical_Prop Logic.ClassicalEpsilon
  Logic.ProofIrrelevance.
From Foundation.FirstOrder.SetTheory Require Import Basic Z.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** A set is transitive when all of its members are subsets of it. *)
Definition z_is_transitive {m : membership_structure}
    (x : membership_carrier m) : Prop :=
  forall y, membership_rel y x -> set_model_subset y x.

Lemma z_is_transitive_def : forall m (x : membership_carrier m),
  z_is_transitive x <->
  forall y, membership_rel y x -> set_model_subset y x.
Proof. intros; split; trivial. Qed.

Lemma z_is_transitive_mem_trans : forall m
    (x y z : membership_carrier m),
  z_is_transitive z -> membership_rel x y -> membership_rel y z ->
  membership_rel x z.
Proof.
  intros m x y z Hz Hxy Hyz. exact (Hz y Hyz x Hxy).
Qed.

Lemma z_is_transitive_empty : forall m (O : zermelo_operations m),
  z_is_transitive (z_empty O).
Proof.
  intros m O y Hy z Hz. exfalso. now apply (z_not_mem_empty O y Hy).
Qed.

Lemma z_is_transitive_successor : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  z_is_transitive x -> z_is_transitive (z_successor O x).
Proof.
  intros m O x H y Hy z Hz. apply z_successor_mem_iff in Hy.
  destruct Hy as [-> | Hy].
  - apply z_successor_mem_iff. now right.
  - apply z_successor_mem_iff. right. exact (H y Hy z Hz).
Qed.

Lemma z_is_transitive_union : forall m (O : zermelo_operations m)
    (x y : membership_carrier m),
  z_is_transitive x -> z_is_transitive y ->
  z_is_transitive (z_union O x y).
Proof.
  intros m O x y Hx Hy z Hz w Hw.
  apply z_union_mem_iff in Hz.
  destruct Hz as [Hz | Hz].
  - apply z_union_mem_iff. now left; apply Hx with z.
  - apply z_union_mem_iff. now right; apply Hy with z.
Qed.

Lemma z_is_transitive_sunion : forall m (O : zermelo_operations m)
    (X : membership_carrier m),
  (forall x, membership_rel x X -> z_is_transitive x) ->
  z_is_transitive (z_sunion O X).
Proof.
  intros m O X H y Hy z Hz. apply z_sunion_mem_iff in Hy.
  destruct Hy as [x [HxX Hyx]].
  apply z_sunion_mem_iff. exists x. split; [exact HxX |].
  exact (H x HxX y Hyx z Hz).
Qed.

Lemma z_is_transitive_sinter : forall m (O : zermelo_operations m)
    (X : membership_carrier m),
  (forall x, membership_rel x X -> z_is_transitive x) ->
  z_is_transitive (z_sinter O X).
Proof.
  intros m O X H y Hy z Hz. apply z_sinter_mem_iff in Hy.
  destruct Hy as [HX HyX]. apply z_sinter_mem_iff. split; [exact HX |].
  intros x HxX. exact (H x HxX y (HyX x HxX) z Hz).
Qed.

Lemma z_is_transitive_omega : forall m (O : zermelo_operations m),
  z_is_transitive (z_omega O).
Proof.
  intros m O y Hy z Hz.
  pose proof (@z_omega_induction m O
    (fun x => set_model_subset x (z_omega O))
    (@z_empty_subset m O (z_omega O))
    (fun x Hx IH w Hw =>
      match (proj1 (@z_successor_mem_iff m O x w) Hw) with
      | or_introl Heq => eq_ind x (fun q => membership_rel q (z_omega O)) Hx _ (eq_sym Heq)
      | or_intror Hwx => IH w Hwx
      end) y Hy) as HySubset.
  exact (HySubset z Hz).
Qed.

(** An ordinal is transitive and its members are linearly ordered by
    membership. *)
Definition z_is_ordinal {m : membership_structure}
    (x : membership_carrier m) : Prop :=
  z_is_transitive x /\
  forall y, membership_rel y x -> forall z, membership_rel z x ->
    membership_rel y z \/ y = z \/ membership_rel z y.

Lemma z_is_ordinal_iff : forall m (x : membership_carrier m),
  z_is_ordinal x <->
  z_is_transitive x /\
  forall y, membership_rel y x -> forall z, membership_rel z x ->
    membership_rel y z \/ y = z \/ membership_rel z y.
Proof. intros; split; trivial. Qed.

Lemma z_ordinal_of_mem : forall m (O : zermelo_operations m)
    (alpha beta : membership_carrier m),
  z_is_ordinal alpha -> membership_rel beta alpha ->
  z_is_ordinal beta.
Proof.
  intros m O alpha beta [Htrans Htri] Hbeta.
  split.
  - intros gamma Hgamma delta Hdelta.
    pose proof (Htrans beta Hbeta gamma Hgamma) as HgammaA.
    pose proof (Htrans gamma HgammaA delta Hdelta) as HdeltaA.
    destruct (Htri beta Hbeta delta HdeltaA) as [Hbdelta | [Heq | Hdbeta]].
    + exfalso. eapply (@z_mem_asym3 m O gamma beta delta); eauto.
    + subst delta. exfalso. eapply (@z_mem_asym m O gamma beta); eauto.
    + exact Hdbeta.
  - intros gamma Hgamma delta Hdelta.
    apply Htri; [apply Htrans with beta | apply Htrans with beta]; assumption.
Qed.

Lemma z_is_ordinal_empty : forall m (O : zermelo_operations m),
  z_is_ordinal (z_empty O).
Proof.
  intros m O. split; [apply z_is_transitive_empty |].
  intros y Hy. exfalso. now apply (z_not_mem_empty O y Hy).
Qed.

Lemma z_is_ordinal_successor : forall m (O : zermelo_operations m)
    (alpha : membership_carrier m),
  z_is_ordinal alpha -> z_is_ordinal (z_successor O alpha).
Proof.
  intros m O alpha [Htrans Htri]. split.
  - apply z_is_transitive_successor. exact Htrans.
  - intros beta Hbeta gamma Hgamma.
    apply z_successor_mem_iff in Hbeta, Hgamma.
    destruct Hbeta as [-> | Hbeta].
    + destruct Hgamma as [-> | Hgamma].
      * right; left; reflexivity.
      * right; right; exact Hgamma.
    + destruct Hgamma as [-> | Hgamma].
      * left; exact Hbeta.
      * exact (Htri beta Hbeta gamma Hgamma).
Qed.

Lemma z_ordinal_nat : forall m (O : zermelo_operations m)
    (x : membership_carrier m),
  membership_rel x (z_omega O) -> z_is_ordinal x.
Proof.
  intros m O x Hx.
  exact (@z_omega_induction m O z_is_ordinal
    (@z_is_ordinal_empty m O)
    (fun y _ IH => @z_is_ordinal_successor m O y IH) x Hx).
Qed.

(** A strict inclusion between ordinals is witnessed by membership.  The
    proof chooses a membership-minimal element of the difference and uses
    transitivity plus the ordinal trichotomy to identify it with the smaller
    ordinal. *)
Lemma z_ordinal_mem_of_strict_subset : forall m (O : zermelo_operations m)
    (alpha beta : membership_carrier m),
  z_is_ordinal alpha -> z_is_ordinal beta ->
  set_model_strict_subset alpha beta -> membership_rel alpha beta.
Proof.
  intros m O alpha beta [Halpha_trans Halpha_tri]
    [Hbeta_trans Hbeta_tri] [Halpha_beta Halpha_neq].
  pose proof (@z_sdiff_nonempty_of_strict_subset
    (fun P : Prop => classic P) m O alpha beta
    (conj Halpha_beta Halpha_neq)) as Hdiff.
  destruct (@z_foundation_spec m O (z_sdiff O beta alpha) Hdiff)
    as [gamma [Hgamma Hminimal]].
  apply z_sdiff_mem_iff in Hgamma.
  destruct Hgamma as [Hgamma_beta Hgamma_not_alpha].
  assert (Hgamma_subset_alpha : set_model_subset gamma alpha).
  {
    intros xi Hxi.
    pose proof (Hbeta_trans gamma Hgamma_beta xi Hxi) as Hxi_beta.
    destruct (classic (membership_rel xi alpha)) as [Hxi_alpha | Hxi_not_alpha].
    - exact Hxi_alpha.
    - exfalso. apply (Hminimal xi).
      + apply z_sdiff_mem_iff. now split.
      + exact Hxi.
  }
  assert (Halpha_subset_gamma : set_model_subset alpha gamma).
  {
    intros xi Hxi_alpha.
    pose proof (Halpha_beta xi Hxi_alpha) as Hxi_beta.
    destruct (Hbeta_tri xi Hxi_beta gamma Hgamma_beta)
      as [Hxi_gamma | [Hxi_eq | Hgamma_xi]].
    - exact Hxi_gamma.
    - exfalso. apply Hgamma_not_alpha. now rewrite <- Hxi_eq.
    - exfalso. apply Hgamma_not_alpha.
      exact (Halpha_trans xi Hxi_alpha gamma Hgamma_xi).
  }
  assert (Halpha_gamma : alpha = gamma).
  { apply (@z_subset_antisym m O alpha gamma); assumption. }
  now subst gamma.
Qed.

Lemma z_ordinal_strict_subset_iff : forall m (O : zermelo_operations m)
    (alpha beta : membership_carrier m),
  z_is_ordinal alpha -> z_is_ordinal beta ->
  set_model_strict_subset alpha beta <-> membership_rel alpha beta.
Proof.
  intros m O alpha beta Halpha Hbeta. split.
  - intro H. now apply (@z_ordinal_mem_of_strict_subset m O alpha beta Halpha Hbeta).
  - intro Hmem. split.
    + exact ((proj1 Hbeta) alpha Hmem).
    + intro Heq. subst beta. exact (@z_mem_irrefl m O alpha Hmem).
Qed.

Lemma z_ordinal_subset_iff : forall m (O : zermelo_operations m)
    (alpha beta : membership_carrier m),
  z_is_ordinal alpha -> z_is_ordinal beta ->
  set_model_subset alpha beta <-> alpha = beta \/ membership_rel alpha beta.
Proof.
  intros m O alpha beta Halpha Hbeta. split.
  - intro Hsubset. destruct (classic (alpha = beta)) as [Heq | Hneq].
    + now left.
    + right. apply (@z_ordinal_mem_of_strict_subset m O alpha beta Halpha Hbeta).
      now split.
  - intros [Heq | Hmem].
    + now subst beta; apply set_model_subset_refl.
    + exact ((proj1 Hbeta) alpha Hmem).
Qed.

Lemma z_ordinal_mem_iff_subset_and_not_subset : forall m
    (O : zermelo_operations m) (alpha beta : membership_carrier m),
  z_is_ordinal alpha -> z_is_ordinal beta ->
  membership_rel alpha beta <->
  set_model_subset alpha beta /\ ~ set_model_subset beta alpha.
Proof.
  intros m O alpha beta Halpha Hbeta. split.
  - intro Hmem. apply (proj2 (@z_ordinal_strict_subset_iff m O alpha beta
      Halpha Hbeta)) in Hmem.
    destruct Hmem as [Hsubset Hneq]. split; [exact Hsubset |].
    intro Hreverse. apply Hneq.
    apply (@z_subset_antisym m O alpha beta); assumption.
  - intros [Hsubset Hnot].
    apply (@z_ordinal_mem_of_strict_subset m O alpha beta Halpha Hbeta).
    split; [exact Hsubset |].
    intro Heq. apply Hnot. now subst beta; apply set_model_subset_refl.
Qed.

(** Comparability of ordinals follows from foundation.  The argument is the
    usual least-counterexample proof: among the initial segments of [alpha]
    that are incomparable with some ordinal, choose a membership-minimal one;
    the union with its witness is then an ordinal and must equal one of the
    two. *)
Lemma z_ordinal_subset_or_supset : forall m (O : zermelo_operations m)
    (alpha beta : membership_carrier m),
  z_is_ordinal alpha -> z_is_ordinal beta ->
  set_model_subset alpha beta \/ set_model_subset beta alpha.
Proof.
  intros m O alpha beta Halpha Hbeta.
  destruct Halpha as [Halpha_trans Halpha_tri].
  destruct Hbeta as [Hbeta_trans Hbeta_tri].
  assert (Halpha_ord : z_is_ordinal alpha) by (split; assumption).
  destruct (classic (set_model_subset alpha beta)) as [Halpha_beta | Hnot_alpha_beta].
  - now left.
  - destruct (classic (set_model_subset beta alpha)) as [Hbeta_alpha | Hnot_beta_alpha].
    + now right.
    + exfalso.
      set (C := z_separate O
    (fun a' => exists b, z_is_ordinal b /\
      ~ set_model_subset a' b /\ ~ set_model_subset b a')
    (z_successor O alpha)).
      assert (HalphaC : membership_rel alpha C).
  {
    unfold C. apply z_separate_mem_iff. split.
    - apply z_mem_successor_self.
    - exists beta. repeat split; assumption.
  }
      destruct (@z_foundation_spec m O C (ex_intro _ alpha HalphaC))
    as [alpha0 [Halpha0C Hminimal]].
  apply z_separate_mem_iff in Halpha0C.
  destruct Halpha0C as [Halpha0_succ [beta0 [Hbeta0_ord
    [Hnot_alpha0_beta0 Hnot_beta0_alpha0]]]].
  assert (Halpha0_ord : z_is_ordinal alpha0).
  {
    apply z_successor_mem_iff in Halpha0_succ.
    destruct Halpha0_succ as [Heq | Hmem].
    - now subst alpha0.
    - exact (@z_ordinal_of_mem m O alpha alpha0 Halpha_ord Hmem).
  }
  assert (Halpha_succ_trans :
      z_is_transitive (z_successor O alpha)).
  { apply z_is_transitive_successor. exact Halpha_trans. }
  pose proof (proj2 Halpha0_ord) as Halpha0_tri.
  pose proof (proj2 Hbeta0_ord) as Hbeta0_tri.
  assert (Hcross : forall xi zeta : membership_carrier m,
      membership_rel xi alpha0 -> membership_rel zeta beta0 ->
      membership_rel xi zeta \/ xi = zeta \/ membership_rel zeta xi).
  {
    intros xi zeta Hxi Hzeta.
    pose proof (@z_ordinal_of_mem m O alpha0 xi Halpha0_ord Hxi) as Hxi_ord.
    pose proof (@z_ordinal_of_mem m O beta0 zeta Hbeta0_ord Hzeta) as Hzeta_ord.
    destruct (classic (set_model_subset xi zeta)) as [Hxi_zeta | Hnot_xi_zeta].
    - destruct (proj1 (@z_ordinal_subset_iff m O xi zeta Hxi_ord Hzeta_ord)
        Hxi_zeta) as [Heq | Hmem].
      + right; left; exact Heq.
      + left; exact Hmem.
    - destruct (classic (set_model_subset zeta xi)) as [Hzeta_xi | Hnot_zeta_xi].
      + destruct (proj1 (@z_ordinal_subset_iff m O zeta xi
          Hzeta_ord Hxi_ord) Hzeta_xi) as [Heq | Hmem].
        * right; left; symmetry; exact Heq.
        * right; right; exact Hmem.
      + exfalso.
        apply (Hminimal xi).
        * apply z_separate_mem_iff. split.
          -- apply (Halpha_succ_trans alpha0 Halpha0_succ xi Hxi).
          -- exists zeta. split; [exact Hzeta_ord |].
             split; [exact Hnot_xi_zeta | exact Hnot_zeta_xi].
        * exact Hxi.
  }
  set (gamma0 := z_union O alpha0 beta0).
  assert (Hgamma0_ord : z_is_ordinal gamma0).
  {
    split.
    - apply z_is_transitive_union.
      + exact (proj1 Halpha0_ord).
      + exact (proj1 Hbeta0_ord).
    - intros xi Hxi zeta Hzeta.
      apply z_union_mem_iff in Hxi, Hzeta.
      destruct Hxi as [Hxi_alpha0 | Hxi_beta0];
        destruct Hzeta as [Hzeta_alpha0 | Hzeta_beta0].
      + exact (Halpha0_tri xi Hxi_alpha0 zeta Hzeta_alpha0).
      + exact (Hcross xi zeta Hxi_alpha0 Hzeta_beta0).
      + destruct (Hcross zeta xi Hzeta_alpha0 Hxi_beta0)
          as [Hza | [Heq | Hxi_zeta]].
        * right; right; exact Hza.
        * right; left; symmetry; exact Heq.
        * left; exact Hxi_zeta.
      + exact (Hbeta0_tri xi Hxi_beta0 zeta Hzeta_beta0).
  }
  destruct (classic (gamma0 = alpha0)) as [Hgamma_alpha0 | Hgamma_ne_alpha0].
  * apply Hnot_beta0_alpha0.
    intros z Hz.
    pose proof (@z_subset_union_right m O alpha0 beta0 z Hz) as Hzu.
    change (membership_rel z gamma0) in Hzu.
    now rewrite Hgamma_alpha0 in Hzu.
  * destruct (classic (gamma0 = beta0)) as [Hgamma_beta0 | Hgamma_ne_beta0].
    -- apply Hnot_alpha0_beta0.
    intros z Hz.
    pose proof (@z_subset_union_left m O alpha0 beta0 z Hz) as Hzu.
    change (membership_rel z gamma0) in Hzu.
    now rewrite Hgamma_beta0 in Hzu.
    -- assert (Halpha0_mem_gamma0 : membership_rel alpha0 gamma0).
  {
    apply (@z_ordinal_mem_of_strict_subset m O alpha0 gamma0
      Halpha0_ord Hgamma0_ord).
    split.
      --- apply (@z_subset_union_left m O alpha0 beta0).
      --- intro Heq. apply Hgamma_ne_alpha0. symmetry; exact Heq.
  }
      assert (Hbeta0_mem_gamma0 : membership_rel beta0 gamma0).
  {
    apply (@z_ordinal_mem_of_strict_subset m O beta0 gamma0
      Hbeta0_ord Hgamma0_ord).
    split.
      --- apply (@z_subset_union_right m O alpha0 beta0).
      --- intro Heq. apply Hgamma_ne_beta0. symmetry; exact Heq.
    }
    apply (@z_mem_asym m O alpha0 beta0).
    --- apply z_union_mem_iff in Halpha0_mem_gamma0.
    destruct Halpha0_mem_gamma0 as [Haa | Hab].
      ---- exfalso. exact (@z_mem_irrefl m O alpha0 Haa).
      ---- exact Hab.
    --- apply z_union_mem_iff in Hbeta0_mem_gamma0.
    destruct Hbeta0_mem_gamma0 as [Hba | Hbb].
      ---- exact Hba.
      ---- exfalso. exact (@z_mem_irrefl m O beta0 Hbb).
Qed.

Lemma z_ordinal_mem_trichotomy : forall m (O : zermelo_operations m)
    (alpha beta : membership_carrier m),
  z_is_ordinal alpha -> z_is_ordinal beta ->
  membership_rel alpha beta \/ alpha = beta \/ membership_rel beta alpha.
Proof.
  intros m O alpha beta Halpha Hbeta.
  destruct (@z_ordinal_subset_or_supset m O alpha beta Halpha Hbeta)
    as [Halpha_beta | Hbeta_alpha].
  - destruct (proj1 (@z_ordinal_subset_iff m O alpha beta Halpha Hbeta)
      Halpha_beta) as [Heq | Hmem].
    + right; left; exact Heq.
    + left; exact Hmem.
  - destruct (proj1 (@z_ordinal_subset_iff m O beta alpha Hbeta Halpha)
      Hbeta_alpha) as [Heq | Hmem].
    + right; left; symmetry; exact Heq.
    + right; right; exact Hmem.
Qed.

Lemma z_ordinal_of_transitive : forall m (O : zermelo_operations m)
    (alpha : membership_carrier m),
  z_is_transitive alpha ->
  (forall beta, membership_rel beta alpha -> z_is_ordinal beta) ->
  z_is_ordinal alpha.
Proof.
  intros m O alpha Htrans Hmembers. split; [exact Htrans |].
  intros beta Hbeta gamma Hgamma.
  apply (@z_ordinal_mem_trichotomy m O beta gamma); [apply Hmembers | apply Hmembers];
    assumption.
Qed.

Lemma z_is_ordinal_omega : forall m (O : zermelo_operations m),
  z_is_ordinal (z_omega O).
Proof.
  intros m O.
  apply (@z_ordinal_of_transitive m O (z_omega O)).
  - apply z_is_transitive_omega.
  - intros alpha Halpha. apply (@z_ordinal_nat m O alpha Halpha).
Qed.

Lemma z_ordinal_sunion : forall m (O : zermelo_operations m)
    (X : membership_carrier m),
  (forall alpha, membership_rel alpha X -> z_is_ordinal alpha) ->
  z_is_ordinal (z_sunion O X).
Proof.
  intros m O X H.
  apply (@z_ordinal_of_transitive m O (z_sunion O X)).
  - apply z_is_transitive_sunion. exact (fun x Hx => proj1 (H x Hx)).
  - intros beta Hbeta.
    apply z_sunion_mem_iff in Hbeta.
    destruct Hbeta as [alpha [HalphaX Hbetaalpha]].
    apply (@z_ordinal_of_mem m O alpha beta (H alpha HalphaX) Hbetaalpha).
Qed.

Lemma z_ordinal_sinter : forall m (O : zermelo_operations m)
    (X : membership_carrier m),
  (forall alpha, membership_rel alpha X -> z_is_ordinal alpha) ->
  z_is_ordinal (z_sinter O X).
Proof.
  intros m O X H.
  apply (@z_ordinal_of_transitive m O (z_sinter O X)).
  - apply z_is_transitive_sinter. exact (fun x Hx => proj1 (H x Hx)).
  - intros beta Hbeta.
    apply z_sinter_mem_iff in Hbeta.
    destruct Hbeta as [HX HbetaX].
    destruct HX as [alpha HalphaX].
    apply (@z_ordinal_of_mem m O alpha beta (H alpha HalphaX)).
    exact (HbetaX alpha HalphaX).
Qed.

Lemma z_ordinal_empty_mem_iff_nonempty : forall m (O : zermelo_operations m)
    (alpha : membership_carrier m),
  z_is_ordinal alpha ->
  membership_rel (z_empty O) alpha <->
  set_model_is_nonempty alpha.
Proof.
  intros m O alpha Halpha. split.
  - intro Hmem. now exists (z_empty O).
  - intro Hnonempty.
    destruct (proj1 (@z_ordinal_subset_iff m O (z_empty O) alpha
      (@z_is_ordinal_empty m O) Halpha) (@z_empty_subset m O alpha))
      as [Heq | Hmem].
    + subst alpha. destruct Hnonempty as [x Hx].
      exfalso. now apply (@z_not_mem_empty m O x Hx).
    + exact Hmem.
Qed.

(** Bundled ordinals and the order laws carried by their underlying sets. *)
Record z_ordinal (m : membership_structure) : Type := {
  z_ordinal_val : membership_carrier m;
  z_ordinal_ord : z_is_ordinal z_ordinal_val
}.

Arguments z_ordinal_val {m} _.
Arguments z_ordinal_ord {m} _.
Coercion z_ordinal_val : z_ordinal >-> membership_carrier.

Definition z_ordinal_of_set {m : membership_structure}
    (x : membership_carrier m) (H : z_is_ordinal x) : z_ordinal m :=
  {| z_ordinal_val := x; z_ordinal_ord := H |}.

Lemma z_ordinal_ext : forall m (alpha beta : z_ordinal m),
  z_ordinal_val alpha = z_ordinal_val beta -> alpha = beta.
Proof.
  intros m [x Hx] [y Hy] Heq. simpl in Heq. subst y. f_equal.
  apply proof_irrelevance.
Qed.

Definition z_ordinal_lt {m : membership_structure}
    (alpha beta : z_ordinal m) : Prop :=
  membership_rel (z_ordinal_val alpha) (z_ordinal_val beta).

Definition z_ordinal_le {m : membership_structure}
    (alpha beta : z_ordinal m) : Prop :=
  set_model_subset (z_ordinal_val alpha) (z_ordinal_val beta).

Lemma z_ordinal_lt_def : forall m (alpha beta : z_ordinal m),
  z_ordinal_lt alpha beta <->
  membership_rel (z_ordinal_val alpha) (z_ordinal_val beta).
Proof. intros; split; trivial. Qed.

Lemma z_ordinal_le_def : forall m (alpha beta : z_ordinal m),
  z_ordinal_le alpha beta <->
  set_model_subset (z_ordinal_val alpha) (z_ordinal_val beta).
Proof. intros; split; trivial. Qed.

Lemma z_ordinal_lt_irrefl : forall m (O : zermelo_operations m)
    (alpha : z_ordinal m),
  ~ z_ordinal_lt alpha alpha.
Proof.
  intros m O alpha H. exact (@z_mem_irrefl m O (z_ordinal_val alpha) H).
Qed.

Lemma z_ordinal_lt_trans : forall m (O : zermelo_operations m)
    (alpha beta gamma : z_ordinal m),
  z_ordinal_lt alpha beta -> z_ordinal_lt beta gamma ->
  z_ordinal_lt alpha gamma.
Proof.
  intros m O alpha beta gamma Hab Hbc.
  exact ((proj1 (z_ordinal_ord gamma)) _ Hbc _ Hab).
Qed.

Lemma z_ordinal_le_refl : forall m (alpha : z_ordinal m),
  z_ordinal_le alpha alpha.
Proof. intros m alpha; apply set_model_subset_refl. Qed.

Lemma z_ordinal_le_trans : forall m (alpha beta gamma : z_ordinal m),
  z_ordinal_le alpha beta -> z_ordinal_le beta gamma ->
  z_ordinal_le alpha gamma.
Proof. intros m alpha beta gamma; apply set_model_subset_trans. Qed.

Lemma z_ordinal_le_antisym : forall m (O : zermelo_operations m)
    (alpha beta : z_ordinal m),
  z_ordinal_le alpha beta -> z_ordinal_le beta alpha -> alpha = beta.
Proof.
  intros m O alpha beta Hab Hba. apply z_ordinal_ext.
  apply (@z_subset_antisym m O (z_ordinal_val alpha) (z_ordinal_val beta));
    assumption.
Qed.

Lemma z_ordinal_le_total : forall m (O : zermelo_operations m)
    (alpha beta : z_ordinal m),
  z_ordinal_le alpha beta \/ z_ordinal_le beta alpha.
Proof.
  intros m O alpha beta.
  apply (@z_ordinal_subset_or_supset m O
    (z_ordinal_val alpha) (z_ordinal_val beta)
    (z_ordinal_ord alpha) (z_ordinal_ord beta)).
Qed.

Lemma z_ordinal_lt_iff_le_and_not_ge : forall m (O : zermelo_operations m)
    (alpha beta : z_ordinal m),
  z_ordinal_lt alpha beta <->
  z_ordinal_le alpha beta /\ ~ z_ordinal_le beta alpha.
Proof.
  intros m O alpha beta.
  apply (@z_ordinal_mem_iff_subset_and_not_subset m O
    (z_ordinal_val alpha) (z_ordinal_val beta)
    (z_ordinal_ord alpha) (z_ordinal_ord beta)).
Qed.

Lemma z_ordinal_le_iff_eq_or_lt : forall m (O : zermelo_operations m)
    (alpha beta : z_ordinal m),
  z_ordinal_le alpha beta <->
  alpha = beta \/ z_ordinal_lt alpha beta.
Proof.
  intros m O alpha beta.
  destruct (z_ordinal_ord alpha) as [Hta Hca].
  destruct (z_ordinal_ord beta) as [Htb Hcb].
  split.
  - intro Hab.
    destruct (proj1 (@z_ordinal_subset_iff m O
      (z_ordinal_val alpha) (z_ordinal_val beta)
      (conj Hta Hca) (conj Htb Hcb)) Hab) as [Heq | Hmem].
    + left. apply z_ordinal_ext. exact Heq.
    + right. exact Hmem.
  - intros [Heq | Hlt].
    + subst beta. apply z_ordinal_le_refl.
    + exact ((proj1 (z_ordinal_ord beta)) _ Hlt).
Qed.

Definition z_ordinal_bottom {m : membership_structure}
    (O : zermelo_operations m) : z_ordinal m :=
  @z_ordinal_of_set m (z_empty O) (@z_is_ordinal_empty m O).

Lemma z_ordinal_bottom_val : forall m (O : zermelo_operations m),
  z_ordinal_val (z_ordinal_bottom O) = z_empty O.
Proof. intros; reflexivity. Qed.

Lemma z_ordinal_pos_iff_nonempty : forall m (O : zermelo_operations m)
    (alpha : z_ordinal m),
  z_ordinal_lt (z_ordinal_bottom O) alpha <->
  set_model_is_nonempty (z_ordinal_val alpha).
Proof.
  intros m O alpha.
  apply (@z_ordinal_empty_mem_iff_nonempty m O
    (z_ordinal_val alpha) (z_ordinal_ord alpha)).
Qed.

Lemma z_ordinal_eq_bottom_or_pos : forall m (O : zermelo_operations m)
    (alpha : z_ordinal m),
  alpha = z_ordinal_bottom O \/ z_ordinal_lt (z_ordinal_bottom O) alpha.
Proof.
  intros m O alpha.
  destruct (proj1 (@z_ordinal_subset_iff m O
    (z_empty O) (z_ordinal_val alpha)
    (@z_is_ordinal_empty m O) (z_ordinal_ord alpha))
    (@z_empty_subset m O (z_ordinal_val alpha))) as [Heq | Hmem].
  - left. apply z_ordinal_ext. symmetry; exact Heq.
  - right. exact Hmem.
Qed.

Definition z_ordinal_succ {m : membership_structure}
    (O : zermelo_operations m) (alpha : z_ordinal m) : z_ordinal m :=
  @z_ordinal_of_set m (z_successor O (z_ordinal_val alpha))
    (@z_is_ordinal_successor m O (z_ordinal_val alpha) (z_ordinal_ord alpha)).

Lemma z_ordinal_succ_val : forall m (O : zermelo_operations m)
    (alpha : z_ordinal m),
  z_ordinal_val (z_ordinal_succ O alpha) =
  z_successor O (z_ordinal_val alpha).
Proof. intros; reflexivity. Qed.

Lemma z_ordinal_lt_succ : forall m (O : zermelo_operations m)
    (alpha : z_ordinal m),
  z_ordinal_lt alpha (z_ordinal_succ O alpha).
Proof. intros; apply z_mem_successor_self. Qed.

Definition z_ordinal_omega {m : membership_structure}
    (O : zermelo_operations m) : z_ordinal m :=
  @z_ordinal_of_set m (z_omega O) (@z_is_ordinal_omega m O).

Lemma z_ordinal_separate_member_ord : forall m (O : zermelo_operations m)
    (alpha : z_ordinal m) (P : membership_carrier m -> Prop)
    (x : membership_carrier m),
  membership_rel x (z_separate O P (z_ordinal_val alpha)) ->
  z_is_ordinal x.
Proof.
  intros m O alpha P x Hx.
  apply (@z_ordinal_of_mem m O (z_ordinal_val alpha) x
    (z_ordinal_ord alpha)).
  apply (@z_separate_mem_iff m O P
    (z_ordinal_val alpha) x) in Hx.
  exact (proj1 Hx).
Qed.

Lemma z_ordinal_sinter_mem : forall m (O : zermelo_operations m)
    (X : membership_carrier m),
  (forall x, membership_rel x X -> z_is_ordinal x) ->
  set_model_is_nonempty X ->
  membership_rel (z_sinter O X) X.
Proof.
  intros m O X Hord HX.
  destruct (classic (membership_rel (z_sinter O X) X)) as [Hmem | Hnot].
  - exact Hmem.
  - exfalso.
    destruct HX as [x0 Hx0].
    assert (Hself : membership_rel (z_sinter O X) (z_sinter O X)).
    {
      apply z_sinter_mem_iff. split.
      - exists x0. exact Hx0.
      - intros x HxX.
        pose proof (@z_sinter_subset_of_mem m O
          x X HxX) as Hsub.
        destruct (proj1 (@z_ordinal_subset_iff m O
          (z_sinter O X) x
          (@z_ordinal_sinter m O X Hord) (Hord x HxX)) Hsub)
          as [Heq | Hlt].
        + subst x. exfalso. apply Hnot. exact HxX.
        + exact Hlt.
    }
    exact (@z_mem_irrefl m O (z_sinter O X) Hself).
Qed.

Definition z_ordinal_minimal {m : membership_structure}
    (O : zermelo_operations m) (alpha : z_ordinal m)
    (P : membership_carrier m -> Prop) : z_ordinal m :=
  @z_ordinal_of_set m
    (z_sinter O (z_separate O P (z_ordinal_val alpha)))
    (@z_ordinal_sinter m O (z_separate O P (z_ordinal_val alpha))
      (@z_ordinal_separate_member_ord m O alpha P)).

Lemma z_ordinal_minimal_val : forall m (O : zermelo_operations m)
    (alpha : z_ordinal m) (P : membership_carrier m -> Prop),
  z_ordinal_val (z_ordinal_minimal O alpha P) =
  z_sinter O (z_separate O P (z_ordinal_val alpha)).
Proof. intros; reflexivity. Qed.

Lemma z_ordinal_minimal_bottom_eq : forall m (O : zermelo_operations m)
    (P : membership_carrier m -> Prop),
  z_ordinal_minimal O (z_ordinal_bottom O) P =
  z_ordinal_bottom O.
Proof.
  intros m O P. apply z_ordinal_ext.
  unfold z_ordinal_minimal, z_ordinal_bottom.
  simpl. rewrite z_separate_empty, z_sinter_empty. reflexivity.
Qed.

Lemma z_ordinal_minimal_prop_of_exists_aux :
  forall m (O : zermelo_operations m) (alpha : z_ordinal m)
    (P : membership_carrier m -> Prop),
  (exists beta : z_ordinal m,
    z_ordinal_lt beta alpha /\ P (z_ordinal_val beta)) ->
  z_ordinal_lt (z_ordinal_minimal O alpha P) alpha /\
  P (z_ordinal_val (z_ordinal_minimal O alpha P)) /\
  forall xi : z_ordinal m,
    z_ordinal_lt xi alpha -> P (z_ordinal_val xi) ->
    z_ordinal_le (z_ordinal_minimal O alpha P) xi.
Proof.
  intros m O alpha P H.
  set (X := z_separate O P (z_ordinal_val alpha)).
  assert (HXord : forall x, membership_rel x X -> z_is_ordinal x).
  {
    intros x Hx. unfold X in Hx.
    apply (@z_ordinal_separate_member_ord m O alpha P x Hx).
  }
  assert (HXnonempty : set_model_is_nonempty X).
  {
    destruct H as [beta [Hlt HP]].
    exists (z_ordinal_val beta). unfold X.
    apply z_separate_mem_iff. split; assumption.
  }
  pose proof (@z_ordinal_sinter_mem m O X HXord HXnonempty) as HminX.
  change (membership_rel
    (z_ordinal_val (z_ordinal_minimal O alpha P)) X) in HminX.
  apply z_separate_mem_iff in HminX.
  destruct HminX as [Hmin_alpha HminP].
  split.
  - exact Hmin_alpha.
  - split.
    + exact HminP.
    + intros xi Hxi_lt HxiP.
      change (set_model_subset
        (z_ordinal_val (z_ordinal_minimal O alpha P))
        (z_ordinal_val xi)).
      apply (@z_sinter_subset_of_mem m O
        (z_ordinal_val xi) X).
      apply z_separate_mem_iff. split; assumption.
Qed.

Lemma z_ordinal_minimal_lt_of_exists :
  forall m (O : zermelo_operations m) (alpha : z_ordinal m)
    (P : membership_carrier m -> Prop),
  (exists beta : z_ordinal m,
    z_ordinal_lt beta alpha /\ P (z_ordinal_val beta)) ->
  z_ordinal_lt (z_ordinal_minimal O alpha P) alpha.
Proof.
  intros m O alpha P H.
  exact (proj1 (@z_ordinal_minimal_prop_of_exists_aux m O alpha P H)).
Qed.

Lemma z_ordinal_minimal_prop_of_exists :
  forall m (O : zermelo_operations m) (alpha : z_ordinal m)
    (P : membership_carrier m -> Prop),
  (exists beta : z_ordinal m,
    z_ordinal_lt beta alpha /\ P (z_ordinal_val beta)) ->
  P (z_ordinal_val (z_ordinal_minimal O alpha P)).
Proof.
  intros m O alpha P H.
  exact (proj1 (proj2
    (@z_ordinal_minimal_prop_of_exists_aux m O alpha P H))).
Qed.

Lemma z_ordinal_minimal_le_of_exists_aux :
  forall m (O : zermelo_operations m) (alpha : z_ordinal m)
    (P : membership_carrier m -> Prop),
  (exists beta : z_ordinal m,
    z_ordinal_lt beta alpha /\ P (z_ordinal_val beta)) ->
  forall xi : z_ordinal m,
    z_ordinal_lt xi alpha -> P (z_ordinal_val xi) ->
    z_ordinal_le (z_ordinal_minimal O alpha P) xi.
Proof.
  intros m O alpha P H.
  exact (proj2 (proj2
    (@z_ordinal_minimal_prop_of_exists_aux m O alpha P H))).
Qed.

Lemma z_ordinal_minimal_le_of_exists :
  forall m (O : zermelo_operations m) (alpha : z_ordinal m)
    (P : membership_carrier m -> Prop),
  (exists beta : z_ordinal m,
    z_ordinal_lt beta alpha /\ P (z_ordinal_val beta)) ->
  forall xi : z_ordinal m,
    P (z_ordinal_val xi) ->
    z_ordinal_le (z_ordinal_minimal O alpha P) xi.
Proof.
  intros m O alpha P H xi HPxi.
  destruct (classic (z_ordinal_lt xi alpha)) as [Hlt | Hnotlt].
  - apply (@z_ordinal_minimal_le_of_exists_aux m O alpha P H xi Hlt HPxi).
  - destruct (@z_ordinal_le_total m O xi alpha) as [Hxi_alpha | Halpha_xi].
    + destruct (proj1 (@z_ordinal_le_iff_eq_or_lt m O xi alpha)
        Hxi_alpha) as [Heq | Hlt].
      * subst xi.
        apply (proj1 (@z_ordinal_lt_iff_le_and_not_ge m O
          (z_ordinal_minimal O alpha P) alpha)).
        apply (@z_ordinal_minimal_lt_of_exists m O alpha P H).
      * contradiction.
    + apply z_ordinal_le_trans with alpha; [| exact Halpha_xi].
      apply (proj1 (@z_ordinal_lt_iff_le_and_not_ge m O
        (z_ordinal_minimal O alpha P) alpha)).
      apply (@z_ordinal_minimal_lt_of_exists m O alpha P H).
Qed.

Lemma z_ordinal_exists_minimal :
  forall m (O : zermelo_operations m)
    (P : membership_carrier m -> Prop),
  (exists alpha : z_ordinal m, P (z_ordinal_val alpha)) ->
  exists beta : z_ordinal m,
    P (z_ordinal_val beta) /\
    forall xi : z_ordinal m, P (z_ordinal_val xi) ->
      z_ordinal_le beta xi.
Proof.
  intros m O P H.
  destruct H as [alpha Halpha].
  set (alpha_succ := z_ordinal_succ O alpha).
  assert (Hex : exists beta : z_ordinal m,
      z_ordinal_lt beta alpha_succ /\ P (z_ordinal_val beta)).
  {
    exists alpha. split; [exact (z_ordinal_lt_succ O alpha) | exact Halpha].
  }
  exists (z_ordinal_minimal O alpha_succ P). split.
  - apply (@z_ordinal_minimal_prop_of_exists m O alpha_succ P Hex).
  - apply (@z_ordinal_minimal_le_of_exists m O alpha_succ P Hex).
Qed.

Lemma z_ordinal_transfinite_induction :
  forall m (O : zermelo_operations m)
    (P : membership_carrier m -> Prop),
  (forall alpha : z_ordinal m,
    (forall beta : z_ordinal m,
      z_ordinal_lt beta alpha -> P (z_ordinal_val beta)) ->
    P (z_ordinal_val alpha)) ->
  forall alpha : z_ordinal m, P (z_ordinal_val alpha).
Proof.
  intros m O P IH alpha.
  destruct (classic (P (z_ordinal_val alpha))) as [Halpha | Hnot].
  - exact Halpha.
  - pose proof (@z_ordinal_exists_minimal m O
      (fun x => ~ P x)
      (ex_intro _ alpha Hnot)) as Hbad.
    destruct Hbad as [beta [Hnotbeta Hminimal]].
    exfalso. apply Hnotbeta. apply IH. intros xi Hlt.
    destruct (classic (P (z_ordinal_val xi))) as [Hxi | Hnotxi].
    + exact Hxi.
    + exfalso.
      apply (proj2 (proj1 (@z_ordinal_lt_iff_le_and_not_ge m O xi beta) Hlt)).
      apply Hminimal; exact Hnotxi.
Qed.

(** Well-founded membership and set-like predicate packaging. *)
Record z_is_well_founded_rel {m : membership_structure}
    (D : membership_carrier m -> Prop)
    (R : membership_carrier m -> membership_carrier m -> Prop) : Prop := {
  z_well_founded :
    forall S : membership_carrier m,
      (forall x, membership_rel x S -> D x) ->
      set_model_is_nonempty S ->
      exists z, membership_rel z S /\
        forall x, membership_rel x S -> ~ R x z
}.

Lemma z_membership_well_founded : forall m (O : zermelo_operations m),
  z_is_well_founded_rel (fun _ : membership_carrier m => True)
    (@membership_rel m).
Proof.
  intros m O. constructor. intros S _ HS.
  exact (@z_foundation_spec m O S HS).
Qed.

Record z_set_like {m : membership_structure}
    (R : membership_carrier m -> membership_carrier m -> Prop) : Prop := {
  z_set_like_left :
    forall x, exists y : membership_carrier m,
      forall z, membership_rel z y <-> R z x
}.

Lemma z_set_like_left_exists_unique : forall m (O : zermelo_operations m)
    (R : membership_carrier m -> membership_carrier m -> Prop)
    (H : z_set_like R) (x : membership_carrier m),
  exists! s : membership_carrier m,
    forall z, membership_rel z s <-> R z x.
Proof.
  intros m O R H x.
  destruct (z_set_like_left H x) as [s Hs].
  exists s. split.
  - exact Hs.
  - intros t Ht. apply (@z_extensionality m O s t). intro z. split.
    + intro Hz. apply (proj2 (Ht z)). apply (proj1 (Hs z)). exact Hz.
    + intro Hz. apply (proj2 (Hs z)). apply (proj1 (Ht z)). exact Hz.
Qed.

Lemma z_set_like_left_exists : forall m (O : zermelo_operations m)
    (R : membership_carrier m -> membership_carrier m -> Prop)
    (H : z_set_like R) (x : membership_carrier m),
  exists s : membership_carrier m,
    forall z, membership_rel z s <-> R z x.
Proof.
  intros m O R H x.
  destruct (@z_set_like_left_exists_unique m O R H x) as [s Hs].
  exists s. exact (proj1 Hs).
Qed.

Definition z_set_like_left_set {m : membership_structure}
    (O : zermelo_operations m)
    (R : membership_carrier m -> membership_carrier m -> Prop)
    (H : z_set_like R) (x : membership_carrier m) :
    membership_carrier m :=
  proj1_sig (constructive_indefinite_description
    (fun s => forall z, membership_rel z s <-> R z x)
    (@z_set_like_left_exists m O R H x)).

Lemma z_set_like_mem_left : forall m (O : zermelo_operations m)
    (R : membership_carrier m -> membership_carrier m -> Prop)
    (H : z_set_like R) (x z : membership_carrier m),
  membership_rel z (@z_set_like_left_set m O R H x) <-> R z x.
Proof.
  intros m O R H x z. unfold z_set_like_left_set.
  exact (proj2_sig (constructive_indefinite_description
    (fun s => forall q, membership_rel q s <-> R q x)
    (@z_set_like_left_exists m O R H x)) z).
Qed.
