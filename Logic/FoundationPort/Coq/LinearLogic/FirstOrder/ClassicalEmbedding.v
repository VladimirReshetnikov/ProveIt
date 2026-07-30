(** Forgetful embedding of first-order linear logic into classical LK. *)

From Stdlib Require Import Lists.List Sorting.Permutation Vectors.Fin.
From FoundationModal Require Import GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.
From Foundation.FirstOrder Require Import Polarity.
From Foundation.LinearLogic.FirstOrder Require Import Formula Rew Calculus.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint llfo_forget {L X n} (phi : llfo_semiformula L X n) :
    semiformula L X n :=
  match phi with
  | LLRel R v => Semiformula_rel R v
  | LLNRel R v => Semiformula_nrel R v
  | LLOne | LLVerum => Semiformula_verum _
  | LLFalsum | LLZero => Semiformula_falsum _
  | LLTensor psi chi | LLWith psi chi =>
      Semiformula_and (llfo_forget psi) (llfo_forget chi)
  | LLPar psi chi | LLPlus psi chi =>
      Semiformula_or (llfo_forget psi) (llfo_forget chi)
  | LLBang psi | LLQuest psi => llfo_forget psi
  | LLAll psi => Semiformula_all (llfo_forget psi)
  | LLExs psi => Semiformula_exists (llfo_forget psi)
  end.

Lemma llfo_forget_rel : forall L X n k (R : language_rel L k) v,
  llfo_forget (@LLRel L X n k R v) = Semiformula_rel R v.
Proof. reflexivity. Qed.

Lemma llfo_forget_nrel : forall L X n k (R : language_rel L k) v,
  llfo_forget (@LLNRel L X n k R v) = Semiformula_nrel R v.
Proof. reflexivity. Qed.

Lemma llfo_forget_one : forall L X n,
  llfo_forget (@LLOne L X n) = Semiformula_verum n.
Proof. reflexivity. Qed.

Lemma llfo_forget_verum : forall L X n,
  llfo_forget (@LLVerum L X n) = Semiformula_verum n.
Proof. reflexivity. Qed.

Lemma llfo_forget_falsum : forall L X n,
  llfo_forget (@LLFalsum L X n) = Semiformula_falsum n.
Proof. reflexivity. Qed.

Lemma llfo_forget_zero : forall L X n,
  llfo_forget (@LLZero L X n) = Semiformula_falsum n.
Proof. reflexivity. Qed.

Lemma llfo_forget_tensor : forall L X n (phi psi : llfo_semiformula L X n),
  llfo_forget (LLTensor phi psi) =
  Semiformula_and (llfo_forget phi) (llfo_forget psi).
Proof. reflexivity. Qed.

Lemma llfo_forget_with : forall L X n (phi psi : llfo_semiformula L X n),
  llfo_forget (LLWith phi psi) =
  Semiformula_and (llfo_forget phi) (llfo_forget psi).
Proof. reflexivity. Qed.

Lemma llfo_forget_par : forall L X n (phi psi : llfo_semiformula L X n),
  llfo_forget (LLPar phi psi) =
  Semiformula_or (llfo_forget phi) (llfo_forget psi).
Proof. reflexivity. Qed.

Lemma llfo_forget_plus : forall L X n (phi psi : llfo_semiformula L X n),
  llfo_forget (LLPlus phi psi) =
  Semiformula_or (llfo_forget phi) (llfo_forget psi).
Proof. reflexivity. Qed.

Lemma llfo_forget_bang : forall L X n (phi : llfo_semiformula L X n),
  llfo_forget (LLBang phi) = llfo_forget phi.
Proof. reflexivity. Qed.

Lemma llfo_forget_quest : forall L X n (phi : llfo_semiformula L X n),
  llfo_forget (LLQuest phi) = llfo_forget phi.
Proof. reflexivity. Qed.

Lemma llfo_forget_all : forall L X n (phi : llfo_semiformula L X (S n)),
  llfo_forget (LLAll phi) = Semiformula_all (llfo_forget phi).
Proof. reflexivity. Qed.

Lemma llfo_forget_exs : forall L X n (phi : llfo_semiformula L X (S n)),
  llfo_forget (LLExs phi) = Semiformula_exists (llfo_forget phi).
Proof. reflexivity. Qed.

Theorem llfo_forget_neg : forall L X n (phi : llfo_semiformula L X n),
  llfo_forget (llfo_neg phi) = semiformula_neg (llfo_forget phi).
Proof.
  intros L X n phi. induction phi; simpl; congruence.
Qed.

Theorem llfo_forget_rewrite : forall L X n Y m (w : rew L X n Y m)
    (phi : llfo_semiformula L X n),
  llfo_forget (llfo_rewrite w phi) =
  semiformula_rewrite w (llfo_forget phi).
Proof.
  intros L X n Y m w phi. revert m w.
  induction phi; intros m w; simpl; try reflexivity.
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - apply IHphi.
  - apply IHphi.
  - now rewrite (IHphi (S m) (rew_q w)).
  - now rewrite (IHphi (S m) (rew_q w)).
Qed.

(** Polarity-sensitive Girard translation in the reverse direction. *)
Fixpoint llfo_girard {L X n} (phi : semiformula L X n) :
    llfo_semiformula L X n :=
  match phi with
  | Semiformula_rel R v => LLBang (LLRel R v)
  | Semiformula_nrel R v => LLQuest (LLNRel R v)
  | Semiformula_verum _ => LLOne
  | Semiformula_falsum _ => LLFalsum
  | Semiformula_and psi chi =>
      match semiformula_polarity psi, semiformula_polarity chi with
      | true, true => LLTensor (llfo_girard psi) (llfo_girard chi)
      | true, false => LLTensor (llfo_girard psi) (LLBang (llfo_girard chi))
      | false, true => LLTensor (LLBang (llfo_girard psi)) (llfo_girard chi)
      | false, false => LLWith (llfo_girard psi) (llfo_girard chi)
      end
  | Semiformula_or psi chi =>
      match semiformula_polarity psi, semiformula_polarity chi with
      | true, true => LLPlus (llfo_girard psi) (llfo_girard chi)
      | true, false => LLPar (LLQuest (llfo_girard psi)) (llfo_girard chi)
      | false, true => LLPar (llfo_girard psi) (LLQuest (llfo_girard chi))
      | false, false => LLPar (llfo_girard psi) (llfo_girard chi)
      end
  | Semiformula_all psi =>
      if semiformula_polarity psi
      then LLAll (LLQuest (llfo_girard psi))
      else LLAll (llfo_girard psi)
  | Semiformula_exists psi =>
      if semiformula_polarity psi
      then LLExs (llfo_girard psi)
      else LLExs (LLBang (llfo_girard psi))
  end.

Lemma llfo_girard_rel : forall L X n k (R : language_rel L k) v,
  llfo_girard (@Semiformula_rel L X n k R v) = LLBang (LLRel R v).
Proof. reflexivity. Qed.

Lemma llfo_girard_nrel : forall L X n k (R : language_rel L k) v,
  llfo_girard (@Semiformula_nrel L X n k R v) = LLQuest (LLNRel R v).
Proof. reflexivity. Qed.

Lemma llfo_girard_verum : forall L X n,
  llfo_girard (@Semiformula_verum L X n) = LLOne.
Proof. reflexivity. Qed.

Lemma llfo_girard_falsum : forall L X n,
  llfo_girard (@Semiformula_falsum L X n) = LLFalsum.
Proof. reflexivity. Qed.

Theorem llfo_girard_neg : forall L X n (phi : semiformula L X n),
  llfo_girard (semiformula_neg phi) = llfo_neg (llfo_girard phi).
Proof.
  intros L X n phi. induction phi; simpl; try reflexivity.
  - rewrite semiformula_polarity_neg, semiformula_polarity_neg.
    rewrite IHphi1, IHphi2.
    destruct (semiformula_polarity phi1), (semiformula_polarity phi2);
      reflexivity.
  - rewrite semiformula_polarity_neg, semiformula_polarity_neg.
    rewrite IHphi1, IHphi2.
    destruct (semiformula_polarity phi1), (semiformula_polarity phi2);
      reflexivity.
  - rewrite semiformula_polarity_neg, IHphi.
    destruct (semiformula_polarity phi); reflexivity.
  - rewrite semiformula_polarity_neg, IHphi.
    destruct (semiformula_polarity phi); reflexivity.
Qed.

Theorem llfo_girard_rewrite : forall L X n Y m (w : rew L X n Y m)
    (phi : semiformula L X n),
  llfo_girard (semiformula_rewrite w phi) =
  llfo_rewrite w (llfo_girard phi).
Proof.
  intros L X n Y m w phi. revert m w.
  induction phi; intros m w; simpl; try reflexivity.
  - rewrite !semiformula_polarity_rewrite.
    rewrite (IHphi1 m w), (IHphi2 m w).
    destruct (semiformula_polarity phi1), (semiformula_polarity phi2);
      reflexivity.
  - rewrite !semiformula_polarity_rewrite.
    rewrite (IHphi1 m w), (IHphi2 m w).
    destruct (semiformula_polarity phi1), (semiformula_polarity phi2);
      reflexivity.
  - rewrite semiformula_polarity_rewrite, (IHphi (S m) (rew_q w)).
    destruct (semiformula_polarity phi); reflexivity.
  - rewrite semiformula_polarity_rewrite, (IHphi (S m) (rew_q w)).
    destruct (semiformula_polarity phi); reflexivity.
Qed.

Definition llfo_Girard {L X n} (phi : semiformula L X n) :
    llfo_semiformula L X n :=
  if semiformula_polarity phi
  then LLQuest (llfo_girard phi)
  else llfo_girard phi.

Theorem llfo_Girard_rewrite : forall L X n Y m (w : rew L X n Y m)
    (phi : semiformula L X n),
  llfo_Girard (semiformula_rewrite w phi) =
  llfo_rewrite w (llfo_Girard phi).
Proof.
  intros. unfold llfo_Girard.
  rewrite semiformula_polarity_rewrite, llfo_girard_rewrite.
  destruct (semiformula_polarity phi); reflexivity.
Qed.

Theorem llfo_girard_negative : forall L X n (phi : semiformula L X n),
  semiformula_negative phi -> llfo_negative n (llfo_girard phi).
Proof.
  intros L X n phi. induction phi; intro Hneg; simpl.
  - now apply semiformula_verum_not_negative in Hneg.
  - constructor.
  - now apply semiformula_rel_not_negative in Hneg.
  - constructor.
  - apply semiformula_and_negative_iff in Hneg as [Hp Hq].
    unfold semiformula_negative in Hp, Hq.
    rewrite Hp, Hq. constructor; [now apply IHphi1 | now apply IHphi2].
  - destruct (semiformula_polarity phi1) eqn:Hp,
      (semiformula_polarity phi2) eqn:Hq; simpl.
    + unfold semiformula_negative in Hneg. simpl in Hneg.
      rewrite Hp, Hq in Hneg. discriminate.
    + constructor; [constructor | now apply IHphi2].
    + constructor; [now apply IHphi1 | constructor].
    + constructor; [now apply IHphi1 | now apply IHphi2].
  - destruct (semiformula_polarity phi) eqn:Hp.
    + constructor. constructor.
    + constructor. now apply IHphi.
  - discriminate.
Qed.

Theorem llfo_girard_positive : forall L X n (phi : semiformula L X n),
  semiformula_positive phi -> llfo_positive n (llfo_girard phi).
Proof.
  intros L X n phi Hpos.
  apply (proj1 (llfo_neg_negative_iff_positive (llfo_girard phi))).
  rewrite <- llfo_girard_neg.
  apply llfo_girard_negative.
  now apply (proj2 (semiformula_neg_negative_iff phi)).
Qed.

Theorem llfo_girard_negative_iff : forall L X n
    (phi : semiformula L X n),
  llfo_negative n (llfo_girard phi) <-> semiformula_negative phi.
Proof.
  intros L X n phi. split; [|apply llfo_girard_negative].
  intro Hlinear. unfold semiformula_negative.
  destruct (semiformula_polarity phi) eqn:Hpol; [|reflexivity].
  exfalso.
  apply (@llfo_positive_negative_disjoint L X n (llfo_girard phi)).
  split; [now apply llfo_girard_positive | exact Hlinear].
Qed.

Theorem llfo_girard_positive_iff : forall L X n
    (phi : semiformula L X n),
  llfo_positive n (llfo_girard phi) <-> semiformula_positive phi.
Proof.
  intros L X n phi. split; [|apply llfo_girard_positive].
  intro Hlinear. unfold semiformula_positive.
  destruct (semiformula_polarity phi) eqn:Hpol; [reflexivity |].
  exfalso.
  apply (@llfo_positive_negative_disjoint L X n (llfo_girard phi)).
  split; [exact Hlinear |].
  apply llfo_girard_negative. exact Hpol.
Qed.

Theorem llfo_Girard_negative : forall L X n (phi : semiformula L X n),
  llfo_negative n (llfo_Girard phi).
Proof.
  intros L X n phi. unfold llfo_Girard.
  destruct (semiformula_polarity phi) eqn:Hpol.
  - constructor.
  - now apply llfo_girard_negative.
Qed.

Definition llfo_girard_sequent {L} (Gamma : first_order_sequent L) :
    llfo_sequent L := map llfo_Girard Gamma.

Lemma llfo_girard_sequent_negative : forall L (Gamma : first_order_sequent L),
  llfo_sequent_negative (llfo_girard_sequent Gamma).
Proof.
  intros L Gamma phi Hphi. apply in_map_iff in Hphi.
  destruct Hphi as [psi [<- _]]. apply llfo_Girard_negative.
Qed.

Lemma llfo_girard_sequent_shift : forall L (Gamma : first_order_sequent L),
  llfo_shift_sequent (llfo_girard_sequent Gamma) =
  llfo_girard_sequent (first_order_sequent_shift Gamma).
Proof.
  intros L Gamma.
  unfold llfo_shift_sequent, llfo_girard_sequent,
    first_order_sequent_shift.
  rewrite !map_map. apply map_ext. intro phi.
  apply eq_sym. apply llfo_Girard_rewrite.
Qed.

Theorem llfo_forget_girard : forall L X n (phi : semiformula L X n),
  llfo_forget (llfo_girard phi) = phi.
Proof.
  intros L X n phi. induction phi; simpl; try reflexivity.
  - destruct (semiformula_polarity phi1), (semiformula_polarity phi2);
      simpl; now rewrite IHphi1, IHphi2.
  - destruct (semiformula_polarity phi1), (semiformula_polarity phi2);
      simpl; now rewrite IHphi1, IHphi2.
  - destruct (semiformula_polarity phi); simpl; now rewrite IHphi.
  - destruct (semiformula_polarity phi); simpl; now rewrite IHphi.
Qed.

Theorem llfo_forget_Girard : forall L X n (phi : semiformula L X n),
  llfo_forget (llfo_Girard phi) = phi.
Proof.
  intros. unfold llfo_Girard.
  destruct (semiformula_polarity phi); apply llfo_forget_girard.
Qed.

Definition llfo_forget_sequent {L} (Gamma : llfo_sequent L) :
    first_order_sequent L := map llfo_forget Gamma.

Lemma llfo_forget_sequent_shift : forall L (Gamma : llfo_sequent L),
  llfo_forget_sequent (llfo_shift_sequent Gamma) =
  first_order_sequent_shift (llfo_forget_sequent Gamma).
Proof.
  intros L Gamma. induction Gamma as [|phi Gamma IH]; simpl; [reflexivity |].
  unfold llfo_shift. rewrite llfo_forget_rewrite. now rewrite IH.
Qed.

Lemma llfo_forget_permutation_subset : forall L
    (Gamma Delta : llfo_sequent L),
  Permutation Gamma Delta ->
  generic_list_subset (llfo_forget_sequent Gamma)
    (llfo_forget_sequent Delta).
Proof.
  intros L Gamma Delta Hperm. induction Hperm; simpl.
  - intros q Hq. exact Hq.
  - intros q [Hq | Hq]; [now left | right; now apply IHHperm].
  - intros q [Hq | [Hq | Hq]].
    + right. now left.
    + now left.
    + right. now right.
  - intros q Hq. apply IHHperm2, IHHperm1, Hq.
Qed.

Fixpoint llfo_derivation_forget {L Gamma}
    (d : llfo_derivation L Gamma) :
    first_order_derivation L (llfo_forget_sequent Gamma).
Proof.
  destruct d as
    [phi
    | phi Gamma Delta d1 d2
    | Gamma Delta d p
    |
    | Gamma d
    | phi psi Gamma Delta d1 d2
    | phi psi Gamma d
    | Gamma
    | phi psi Gamma d1 d2
    | phi psi Gamma d
    | phi psi Gamma d
    | phi Gamma d hquest
    | phi Gamma d
    | phi Gamma d
    | phi Gamma d
    | phi Gamma d
    | phi Gamma t d].
  - refine (first_order_derivation_cast
      (first_order_derivation_eta (llfo_forget phi)) _).
    simpl. now rewrite llfo_forget_neg.
  - refine (first_order_derivation_cast
      (FODCut (@llfo_derivation_forget L _ d1)
        (first_order_derivation_cast (@llfo_derivation_forget L _ d2) _)) _).
    + simpl. now rewrite llfo_forget_neg.
    + unfold llfo_forget_sequent. now rewrite map_app.
  - apply (FODContraction (@llfo_derivation_forget L _ d)).
    now apply llfo_forget_permutation_subset.
  - exact FODVerum.
  - apply (FODContraction (@llfo_derivation_forget L _ d)).
    intros q Hq. now right.
  - refine (first_order_derivation_cast
      (first_order_derivation_tensor
        (@llfo_derivation_forget L _ d1)
        (@llfo_derivation_forget L _ d2)) _).
    change (Semiformula_and (llfo_forget phi) (llfo_forget psi) ::
      map llfo_forget Gamma ++ map llfo_forget Delta =
      Semiformula_and (llfo_forget phi) (llfo_forget psi) ::
      map llfo_forget (Gamma ++ Delta)).
    now rewrite map_app.
  - exact (FODOr (@llfo_derivation_forget L _ d)).
  - apply first_order_derivation_top. now left.
  - exact (FODAnd (@llfo_derivation_forget L _ d1)
      (@llfo_derivation_forget L _ d2)).
  - apply FODOr.
    apply (FODContraction (@llfo_derivation_forget L _ d)).
    intros q [Hq | Hq].
    + subst q. right. now left.
    + right. now right.
  - apply FODOr.
    apply (FODContraction (@llfo_derivation_forget L _ d)).
    intros q [Hq | Hq].
    + subst q. now left.
    + right. now right.
  - exact (@llfo_derivation_forget L _ d).
  - apply (FODContraction (@llfo_derivation_forget L _ d)).
    intros q Hq. now right.
  - exact (@llfo_derivation_forget L _ d).
  - apply (FODContraction (@llfo_derivation_forget L _ d)).
    intros q [Hq | [Hq | Hq]].
    + subst q. now left.
    + subst q. now left.
    + now right.
  - apply FODAll.
    refine (first_order_derivation_cast (@llfo_derivation_forget L _ d) _).
    simpl. unfold llfo_free, semiformula_free.
    rewrite llfo_forget_rewrite, llfo_forget_sequent_shift. reflexivity.
  - refine (@FODExists L (llfo_forget phi) t
      (llfo_forget_sequent Gamma) _).
    refine (first_order_derivation_cast (@llfo_derivation_forget L _ d) _).
    simpl. unfold llfo_substitute, semiformula_substitute.
    now rewrite llfo_forget_rewrite.
Defined.

Theorem llfo_proof_forget : forall L (phi : llfo_proposition L),
  llfo_proof phi ->
  first_order_derivation L [llfo_forget phi].
Proof. intros L phi d. exact (@llfo_derivation_forget L _ d). Qed.
