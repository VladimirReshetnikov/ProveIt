(** Zorn's lemma from classical choice.

    The proof follows the standard tower argument.  It first proves that a
    chain-complete partial order equipped with a chosen immediate strict
    successor at every point is impossible.  Applying that fact to the
    inclusion order on chains removes the immediate-successor hypothesis and
    yields the usual maximal-element theorem.

    This formulation uses predicate sets throughout and is universe
    polymorphic.  In particular, clients do not need an enumeration or a
    decidable equality on the carrier. *)

From Stdlib Require Import Logic.ClassicalChoice Logic.Classical_Prop
  Logic.FunctionalExtensionality Logic.PropExtensionality
  Logic.ProofIrrelevance.
From Foundation.Vorspiel.Set Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record partial_order_laws {A : Type} (R : A -> A -> Prop) : Prop := {
  partial_order_refl : forall x, R x x;
  partial_order_trans : forall x y z, R x y -> R y z -> R x z;
  partial_order_antisym : forall x y, R x y -> R y x -> x = y
}.

Arguments partial_order_refl {A R} _ _.
Arguments partial_order_trans {A R} _ _ _ _ _ _.
Arguments partial_order_antisym {A R} _ _ _ _ _.

Definition order_chain {A} (R : A -> A -> Prop) (C : pred_set A) : Prop :=
  forall x y, C x -> C y -> R x y \/ R y x.

Definition order_maximal {A} (R : A -> A -> Prop) (x : A) : Prop :=
  forall y, R x y -> x = y.

Definition order_upper_bound {A} (R : A -> A -> Prop)
    (C : pred_set A) (x : A) : Prop :=
  forall y, C y -> R y x.

Lemma pred_set_extensionality : forall A (s t : pred_set A),
  set_equiv s t -> s = t.
Proof.
  intros A s t H. apply functional_extensionality. intro x.
  apply propositional_extensionality, H.
Qed.

Section TowerArgument.

  Context {A : Type} {R : A -> A -> Prop}.
  Variable Horder : partial_order_laws R.
  Variable chain_lub : forall C : pred_set A, order_chain R C ->
    {x : A |
      order_upper_bound R C x /\
      forall z, order_upper_bound R C z -> R x z}.
  Variable strict_step : forall x : A,
    {y : A |
      R x y /\ x <> y /\
      forall z, R x z -> R z y -> z = x \/ z = y}.

  Inductive zorn_tower : pred_set A :=
  | zorn_tower_lub : forall C,
      set_subset C zorn_tower ->
      forall HC : order_chain R C,
        zorn_tower (proj1_sig (@chain_lub C HC))
  | zorn_tower_step : forall x,
      zorn_tower x -> zorn_tower (proj1_sig (strict_step x)).

  Lemma zorn_tower_is_chain : order_chain R zorn_tower.
  Proof.
    unfold order_chain. intros x y Hx Hy. revert x Hx.
    induction Hy as [C HC IHC HCorder | y Hy IHHy]; intros x Hx.
    - destruct (classic (order_upper_bound R C x)) as [Hub | Hnot].
      + right. exact (proj2 (proj2_sig (@chain_lub C HCorder)) x Hub).
      + left. unfold order_upper_bound in Hnot.
        apply not_all_ex_not in Hnot. destruct Hnot as [c Hnot].
        apply imply_to_and in Hnot. destruct Hnot as [Hc Hncx].
        eapply (partial_order_trans Horder).
        * destruct (IHC c Hc x Hx) as [Hcx | Hxc]; [exact Hcx |].
          exfalso. apply Hncx. exact Hxc.
        * exact (proj1 (proj2_sig (@chain_lub C HCorder)) c Hc).
    - destruct (proj2_sig (strict_step y)) as [Hyy' [Hneq Himmediate]].
      set (y' := proj1_sig (strict_step y)) in *.
      assert (Hcut : forall z, zorn_tower z -> R z y \/ R y' z).
      { intros z Hz. induction Hz as [C HC IHC HCorder | z Hz IHz].
        - destruct (classic (order_upper_bound R C y)) as [Hub | Hnot].
          + left. exact (proj2 (proj2_sig (@chain_lub C HCorder)) y Hub).
          + right. unfold order_upper_bound in Hnot.
            apply not_all_ex_not in Hnot. destruct Hnot as [c Hnot].
            apply imply_to_and in Hnot. destruct Hnot as [Hc Hncy].
            eapply (partial_order_trans Horder).
            * destruct (IHC c Hc) as [Hcy | Hyc]; [contradiction |].
              exact Hyc.
            * exact (proj1 (proj2_sig (@chain_lub C HCorder)) c Hc).
        - assert (Hy'tower : zorn_tower y').
          { unfold y'. now apply zorn_tower_step. }
          destruct IHz as [Hzy | Hy'z].
          + destruct (IHHy (proj1_sig (strict_step z))
              (zorn_tower_step Hz)) as [Hz'y | Hyz'].
            * left. exact Hz'y.
            * destruct (proj2_sig (strict_step z)) as
                [Hzz' [Hzneq Hzimmediate]].
              destruct (Hzimmediate y Hzy Hyz') as [-> | Heq].
              -- right. apply (partial_order_refl Horder).
              -- left. rewrite <- Heq. apply (partial_order_refl Horder).
          + right. eapply (partial_order_trans Horder); [exact Hy'z |].
            exact (proj1 (proj2_sig (strict_step z))).
      }
      destruct (Hcut x Hx) as [Hxy | Hy'x].
      + left. eapply (partial_order_trans Horder); [exact Hxy | exact Hyy'].
      + now right.
  Qed.

  Lemma chain_complete_with_strict_steps_false : False.
  Proof.
    pose proof (proj2_sig (@chain_lub zorn_tower zorn_tower_is_chain))
      as [Hub Hleast].
    set (top := proj1_sig (@chain_lub zorn_tower zorn_tower_is_chain)) in *.
    assert (Htop : zorn_tower top).
    { unfold top. apply zorn_tower_lub with (C := zorn_tower).
      intros x Hx. exact Hx. }
    set (next := proj1_sig (strict_step top)).
    assert (Hnext : zorn_tower next).
    { unfold next. now apply zorn_tower_step. }
    destruct (proj2_sig (strict_step top)) as [Htn [Hneq _]].
    apply Hneq. apply (partial_order_antisym Horder).
    - exact Htn.
    - exact (Hub next Hnext).
  Qed.

End TowerArgument.

Section Zorn.

  Context {A : Type} {R : A -> A -> Prop}.
  Variable Horder : partial_order_laws R.
  Variable chain_upper_bound : forall C : pred_set A,
    order_chain R C -> exists x, order_upper_bound R C x.

  Record chain_carrier : Type := {
    chain_set : pred_set A;
    chain_set_ordered : order_chain R chain_set
  }.

  Definition chain_included (C D : chain_carrier) : Prop :=
    set_subset (chain_set C) (chain_set D).

  Lemma chain_carrier_ext : forall C D,
    set_equiv (chain_set C) (chain_set D) -> C = D.
  Proof.
    intros [C HC] [D HD] Heq. cbn in Heq. cbn.
    assert (C = D) by now apply pred_set_extensionality.
    subst D. f_equal. apply proof_irrelevance.
  Qed.

  Lemma chain_included_order : partial_order_laws chain_included.
  Proof.
    constructor.
    - intros C x Hx. exact Hx.
    - intros C D E HCD HDE x Hx. now apply HDE, HCD.
    - intros C D HCD HDC. apply chain_carrier_ext. intro x. split;
        [apply HCD | apply HDC].
  Qed.

  Definition chain_union (F : pred_set chain_carrier) : pred_set A :=
    fun x => exists C, F C /\ chain_set C x.

  Lemma chain_union_ordered : forall F,
    order_chain chain_included F -> order_chain R (chain_union F).
  Proof.
    intros F HF x y [C [HFC HCx]] [D [HFD HDy]].
    destruct (HF C D HFC HFD) as [HCD | HDC].
    - exact (@chain_set_ordered D x y (HCD x HCx) HDy).
    - exact (@chain_set_ordered C x y HCx (HDC y HDy)).
  Qed.

  Definition chain_union_carrier F (HF : order_chain chain_included F) :
      chain_carrier :=
    {| chain_set := chain_union F;
       chain_set_ordered := chain_union_ordered HF |}.

  Lemma chain_union_is_lub : forall F (HF : order_chain chain_included F),
    (forall C, F C -> chain_included C (@chain_union_carrier F HF)) /\
    forall D, (forall C, F C -> chain_included C D) ->
      chain_included (@chain_union_carrier F HF) D.
  Proof.
    intros F HF. split.
    - intros C HFC x HCx. exists C. now split.
    - intros D HD x [C [HFC HCx]]. now apply (HD C HFC).
  Qed.

  Definition chain_inclusion_lub : forall F,
      order_chain chain_included F ->
      {C : chain_carrier |
        order_upper_bound chain_included F C /\
        forall D, order_upper_bound chain_included F D ->
          chain_included C D} :=
    fun F HF => exist _ (@chain_union_carrier F HF)
      (@chain_union_is_lub F HF).

  Lemma extend_chain_immediately :
    (forall x, exists y, R x y /\ x <> y) ->
    forall C : chain_carrier,
      exists D : chain_carrier,
        chain_included C D /\ C <> D /\
        forall E, chain_included C E -> chain_included E D ->
          E = C \/ E = D.
  Proof.
    intros Hstep [C HC].
    destruct (@chain_upper_bound C HC) as [u Hu].
    destruct (Hstep u) as [v [Huv Hneq]].
    set (Dset := fun x => C x \/ x = v).
    assert (HDchain : order_chain R Dset).
    { intros x y [HCx | ->] [HCy | ->].
      - exact (HC x y HCx HCy).
      - left. eapply (partial_order_trans Horder);
          [exact (Hu x HCx) | exact Huv].
      - right. eapply (partial_order_trans Horder);
          [exact (Hu y HCy) | exact Huv].
      - left. apply (partial_order_refl Horder). }
    exists {| chain_set := Dset; chain_set_ordered := HDchain |}.
    split.
    - intros x Hx. now left.
    - split.
      + intro Heq.
        assert (HCv : C v).
        { change (chain_set
            {| chain_set := C; chain_set_ordered := HC |} v).
          rewrite Heq. cbn. now right. }
        apply Hneq. apply (partial_order_antisym Horder).
        * exact Huv.
        * exact (Hu v HCv).
      + intros [E HE] HCE HED.
        destruct (classic (E v)) as [HEv | HnEv].
        * right. apply chain_carrier_ext. intro x. split.
          -- intro HDx. exact (HED x HDx).
          -- intros [HCx | ->]; [exact (HCE x HCx) | exact HEv].
        * left. apply chain_carrier_ext. intro x. split.
          -- intro HEx. destruct (HED x HEx) as [HCx | ->];
               [exact HCx | contradiction].
          -- exact (HCE x).
  Qed.

  Theorem zorn_maximal_element : exists x, order_maximal R x.
  Proof.
    apply NNPP. intro Hnone.
    assert (Hstep : forall x, exists y, R x y /\ x <> y).
    { intro x.
      assert (Hnotmax : ~ order_maximal R x).
      { intro Hmax. apply Hnone. now exists x. }
      unfold order_maximal in Hnotmax.
      apply not_all_ex_not in Hnotmax. destruct Hnotmax as [y Hnotmax].
      apply imply_to_and in Hnotmax. exists y. exact Hnotmax. }
    assert (Hextend : forall C : chain_carrier,
      exists D : chain_carrier,
        chain_included C D /\ C <> D /\
        forall E, chain_included C E -> chain_included E D ->
          E = C \/ E = D).
    { exact (extend_chain_immediately Hstep). }
    destruct (@choice chain_carrier chain_carrier
      (fun C D =>
        chain_included C D /\ C <> D /\
        forall E, chain_included C E -> chain_included E D ->
          E = C \/ E = D) Hextend) as [step Hstep_spec].
    exact (@chain_complete_with_strict_steps_false chain_carrier
      chain_included chain_included_order chain_inclusion_lub
      (fun C => exist _ (step C) (Hstep_spec C))).
  Qed.

End Zorn.

Arguments zorn_maximal_element {A R} _ _.
