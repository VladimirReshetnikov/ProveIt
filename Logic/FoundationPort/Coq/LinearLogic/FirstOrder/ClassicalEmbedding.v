(** Forgetful embedding of first-order linear logic into classical LK. *)

From Stdlib Require Import Lists.List Sorting.Permutation Vectors.Fin.
From FoundationModal Require Import GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.
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
