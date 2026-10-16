(** * S_qt: translating formulas by replacing the two atoms with formulas

    For two binary formula builders [Eqv] and [Mem] (commuting with substitution), [qt phi]
    replaces every atom [x ≡' y] by [Eqv x y] and every atom [x ∈' y] by [Mem x y], and keeps the
    connectives and quantifiers.  Terms of the minimal signature are variables, so [qt] commutes
    with substitution ([qt_subst]).  [qt_prv]: a derivation [A ⊢C phi] becomes a derivation of
    [qt phi] from any context that derives [qt a] for every hypothesis [a] of [A].
    [qt_tprv]: the same for theories. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationFacts ListAutomationHints ListAutomationInstances.
From ZF Require Import Std_tr Std_gen Std_iface.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Theories: cut *)
Lemma tprv_list (T : form -> Prop) (A : list form) (f : form -> form) :
  (forall a, In a A -> T ⊢TC f a) ->
  exists B, (forall b, In b B -> T b) /\ forall a, In a A -> B ⊢C f a.
Proof.
  induction A as [|a A IH]; intros H.
  - exists []. split; [intros b []| intros a []].
  - destruct (H a (or_introl eq_refl)) as [B1 [HB1 D1]].
    destruct IH as [B2 [HB2 D2]]; [intros a' Ha'; apply H; now right|].
    exists (B1 ++ B2). split.
    + intros b Hb. apply in_app_or in Hb as [Hb|Hb]; auto.
    + intros a' [<-|Ha'].
      * eapply Weak; [exact D1|]. intros x Hx. apply in_or_app. now left.
      * eapply Weak; [exact (D2 a' Ha')|]. intros x Hx. apply in_or_app. now right.
Qed.

Lemma ctx_cut (A B : list form) (phi : form) :
  A ⊢C phi -> (forall a, In a A -> B ⊢C a) -> B ⊢C phi.
Proof.
  revert phi B. induction A as [|a A IH]; intros phi B H HB.
  - eapply Weak; [exact H|]. intros x [].
  - apply II in H. eapply IE.
    + apply IH; [exact H|]. intros a' Ha'. apply HB. now right.
    + apply HB. now left.
Qed.

Lemma tprv_cut (T T' : form -> Prop) (phi : form) :
  (forall a, T a -> T' ⊢TC a) -> T ⊢TC phi -> T' ⊢TC phi.
Proof.
  intros HT [A [HA D]].
  destruct (tprv_list T' A (fun a => a)) as [B [HB DB]]; [intros a Ha; apply HT, HA, Ha|].
  exists B. split; [exact HB|]. eapply ctx_cut; [exact D|exact DB].
Qed.

Section QT.
  Variables Eqv Mem : term -> term -> form.
  Hypothesis Eqv_subst : forall x y sg, (Eqv x y)[sg] = Eqv x`[sg] y`[sg].
  Hypothesis Mem_subst : forall x y sg, (Mem x y)[sg] = Mem x`[sg] y`[sg].

  Fixpoint qt {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : form :=
    match phi with
    | falsity => falsity
    | atom P v =>
        match P return Vector.t term (ar_preds P) -> form with
        | elem => fun v => Mem (Vector.hd v) (Vector.hd (Vector.tl v))
        | equal => fun v => Eqv (Vector.hd v) (Vector.hd (Vector.tl v))
        end v
    | bin b phi psi => bin b (qt phi) (qt psi)
    | quant q phi => quant q (qt phi)
    end.

  Lemma qt_subst {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) sigma :
    (qt phi)[sigma] = qt (phi[sigma]).
  Proof.
    induction phi in sigma |- *; cbn; try reflexivity.
    - destruct P; cbn in t |- *; rewrite (vec2 t); cbn; [apply Mem_subst | apply Eqv_subst].
    - now rewrite IHphi1, IHphi2.
    - now rewrite IHphi.
  Qed.

  Lemma qt_forall_times n (phi : form) : qt (forall_times n phi) = forall_times n (qt phi).
  Proof.
    induction n as [|n IH]; [reflexivity|].
    change (forall_times (S n) phi) with (∀ forall_times n phi).
    change (forall_times (S n) (qt phi)) with (∀ forall_times n (qt phi)). cbn. now rewrite IH.
  Qed.

  Ltac spec_refl := repeat match goal with H : ?x = ?x -> _ |- _ => specialize (H eq_refl) end.

  Theorem qt_prv A (phi : form) :
    A ⊢C phi -> forall Gamma, (forall a, In a A -> Gamma ⊢C qt a) -> Gamma ⊢C qt phi.
  Proof.
    intros H. remember class as p eqn:Hp. revert Hp. revert p A phi H.
    apply (prv_ind_full (P := fun p A phi => p = class -> forall Gamma,
      (forall a, In a A -> @prv _ _ falsity_on p Gamma (qt a)) -> @prv _ _ falsity_on p Gamma (qt phi))); cbn.
    - (* II *) intros p A phi psi _ IH Hp Gamma HA. subst p. spec_refl.
      apply II. apply IH. intros a [<-|Ha]; [apply Ctx; auto | apply (Weak (HA a Ha)); auto].
    - (* IE *) intros p A phi psi _ IH1 _ IH2 Hp Gamma HA. subst p. spec_refl.
      eapply IE; [apply IH1 | apply IH2]; trivial.
    - (* AllI *) intros p A phi _ IH Hp Gamma HA. subst p. spec_refl.
      apply AllI. apply IH. intros a' Ha'. apply in_map_iff in Ha' as [a [<- Ha]].
      rewrite <- qt_subst. apply subst_Weak, HA, Ha.
    - (* AllE *) intros p A t phi _ IH Hp Gamma HA. subst p. spec_refl.
      rewrite <- qt_subst. specialize (IH Gamma HA). cbn in IH. now apply AllE.
    - (* ExI *) intros p A t phi _ IH Hp Gamma HA. subst p. spec_refl.
      apply (ExI t). rewrite qt_subst. now apply IH.
    - (* ExE *) intros p A phi psi _ IH1 _ IH2 Hp Gamma HA. subst p. spec_refl.
      specialize (IH1 Gamma HA). cbn in IH1. eapply ExE; [apply IH1 |].
      rewrite qt_subst. apply IH2. intros a' [<-|Ha'].
      + apply Ctx. now left.
      + apply in_map_iff in Ha' as [a [<- Ha]]. rewrite <- qt_subst.
        apply (Weak (subst_Weak ↑ (HA a Ha))). auto.
    - (* Exp *) intros p A phi _ IH Hp Gamma HA. subst p. spec_refl. apply Exp. now apply IH.
    - (* Ctx *) intros p A phi Hphi Hp Gamma HA. subst p. now apply HA.
    - (* CI *) intros p A phi psi _ IH1 _ IH2 Hp Gamma HA. subst p. spec_refl.
      apply CI; [apply IH1 | apply IH2]; trivial.
    - (* CE1 *) intros p A phi psi _ IH Hp Gamma HA. subst p. spec_refl. eapply CE1. now apply IH.
    - (* CE2 *) intros p A phi psi _ IH Hp Gamma HA. subst p. spec_refl. eapply CE2. now apply IH.
    - (* DI1 *) intros p A phi psi _ IH Hp Gamma HA. subst p. spec_refl. apply DI1. now apply IH.
    - (* DI2 *) intros p A phi psi _ IH Hp Gamma HA. subst p. spec_refl. apply DI2. now apply IH.
    - (* DE *) intros p A phi psi theta _ IH1 _ IH2 _ IH3 Hp Gamma HA. subst p. spec_refl.
      eapply DE; [now apply IH1 | apply IH2 | apply IH3].
      all: intros a [<-|Ha]; [apply Ctx; auto | apply (Weak (HA a Ha)); auto].
    - (* Pc *) intros A phi psi Hp Gamma HA. apply Pc.
  Qed.

  Theorem qt_tprv (T T' : form -> Prop) (phi : form) :
    (forall a, T a -> T' ⊢TC qt a) -> T ⊢TC phi -> T' ⊢TC qt phi.
  Proof.
    intros HT [A [HA D]].
    destruct (tprv_list T' A qt) as [B [HB DB]]; [intros a Ha; apply HT, HA, Ha|].
    exists B. split; [exact HB|]. eapply qt_prv; [exact D|exact DB].
  Qed.

  (** a universally closed formula: prove the open matrix from closed hypotheses *)
  Lemma tprv_forall_times (T : form -> Prop) n (phi : form) :
    (forall psi, T psi -> closedf psi) -> T ⊢TC phi -> T ⊢TC forall_times n phi.
  Proof.
    intros HT [A [HA D]]. exists A. split; [exact HA|].
    induction n as [|n IH]; [exact D|].
    change (forall_times (S n) phi) with (∀ forall_times n phi).
    apply AllI_closed; [intros psi Hpsi; apply HT, HA, Hpsi | exact IH].
  Qed.

End QT.
