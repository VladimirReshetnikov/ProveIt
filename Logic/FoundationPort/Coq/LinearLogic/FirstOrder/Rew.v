(** Rewriting for first-order linear formulas.

    A rewrite acts only on the semiterms at relation atoms.  Beneath a
    quantifier it is lifted with [rew_q], so the newly bound variable is fixed
    and every pre-existing term variable is shifted.  This makes all of the
    structural laws consequences of the corresponding semiterm laws. *)

From Stdlib Require Import Logic.FunctionalExtensionality Program.Equality Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.LinearLogic.FirstOrder Require Import Formula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint llfo_rewrite_aux {L X n} (phi : llfo_semiformula L X n) :
    forall Y m, rew L X n Y m -> llfo_semiformula L Y m :=
  match phi in llfo_semiformula _ _ n0 return
      forall Y m, rew L X n0 Y m -> llfo_semiformula L Y m with
  | LLRel R v => fun Y m w => LLRel R (fun i => rew_apply w (v i))
  | LLNRel R v => fun Y m w => LLNRel R (fun i => rew_apply w (v i))
  | LLOne => fun Y m _ => @LLOne L Y m
  | LLFalsum => fun Y m _ => @LLFalsum L Y m
  | LLTensor psi chi => fun Y m w =>
      LLTensor (@llfo_rewrite_aux L X _ psi Y m w)
        (@llfo_rewrite_aux L X _ chi Y m w)
  | LLPar psi chi => fun Y m w =>
      LLPar (@llfo_rewrite_aux L X _ psi Y m w)
        (@llfo_rewrite_aux L X _ chi Y m w)
  | LLVerum => fun Y m _ => @LLVerum L Y m
  | LLZero => fun Y m _ => @LLZero L Y m
  | LLWith psi chi => fun Y m w =>
      LLWith (@llfo_rewrite_aux L X _ psi Y m w)
        (@llfo_rewrite_aux L X _ chi Y m w)
  | LLPlus psi chi => fun Y m w =>
      LLPlus (@llfo_rewrite_aux L X _ psi Y m w)
        (@llfo_rewrite_aux L X _ chi Y m w)
  | LLBang psi => fun Y m w => LLBang (@llfo_rewrite_aux L X _ psi Y m w)
  | LLQuest psi => fun Y m w => LLQuest (@llfo_rewrite_aux L X _ psi Y m w)
  | LLAll psi => fun Y m w =>
      LLAll (@llfo_rewrite_aux L X _ psi Y (S m) (rew_q w))
  | LLExs psi => fun Y m w =>
      LLExs (@llfo_rewrite_aux L X _ psi Y (S m) (rew_q w))
  end.

Definition llfo_rewrite {L X n Y m} (w : rew L X n Y m)
    (phi : llfo_semiformula L X n) : llfo_semiformula L Y m :=
  @llfo_rewrite_aux L X n phi Y m w.

Lemma llfo_rewrite_rel : forall L X n Y m (w : rew L X n Y m)
    k (R : language_rel L k) v,
  llfo_rewrite w (@LLRel L X n k R v) =
  LLRel R (fun i => rew_apply w (v i)).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_nrel : forall L X n Y m (w : rew L X n Y m)
    k (R : language_rel L k) v,
  llfo_rewrite w (@LLNRel L X n k R v) =
  LLNRel R (fun i => rew_apply w (v i)).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_one : forall L X n Y m (w : rew L X n Y m),
  llfo_rewrite w (@LLOne L X n) = @LLOne L Y m.
Proof. reflexivity. Qed.

Lemma llfo_rewrite_falsum : forall L X n Y m (w : rew L X n Y m),
  llfo_rewrite w (@LLFalsum L X n) = @LLFalsum L Y m.
Proof. reflexivity. Qed.

Lemma llfo_rewrite_tensor : forall L X n Y m (w : rew L X n Y m)
    (phi psi : llfo_semiformula L X n),
  llfo_rewrite w (LLTensor phi psi) =
  LLTensor (llfo_rewrite w phi) (llfo_rewrite w psi).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_par : forall L X n Y m (w : rew L X n Y m)
    (phi psi : llfo_semiformula L X n),
  llfo_rewrite w (LLPar phi psi) =
  LLPar (llfo_rewrite w phi) (llfo_rewrite w psi).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_verum : forall L X n Y m (w : rew L X n Y m),
  llfo_rewrite w (@LLVerum L X n) = @LLVerum L Y m.
Proof. reflexivity. Qed.

Lemma llfo_rewrite_zero : forall L X n Y m (w : rew L X n Y m),
  llfo_rewrite w (@LLZero L X n) = @LLZero L Y m.
Proof. reflexivity. Qed.

Lemma llfo_rewrite_with : forall L X n Y m (w : rew L X n Y m)
    (phi psi : llfo_semiformula L X n),
  llfo_rewrite w (LLWith phi psi) =
  LLWith (llfo_rewrite w phi) (llfo_rewrite w psi).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_plus : forall L X n Y m (w : rew L X n Y m)
    (phi psi : llfo_semiformula L X n),
  llfo_rewrite w (LLPlus phi psi) =
  LLPlus (llfo_rewrite w phi) (llfo_rewrite w psi).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_bang : forall L X n Y m (w : rew L X n Y m)
    (phi : llfo_semiformula L X n),
  llfo_rewrite w (LLBang phi) = LLBang (llfo_rewrite w phi).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_quest : forall L X n Y m (w : rew L X n Y m)
    (phi : llfo_semiformula L X n),
  llfo_rewrite w (LLQuest phi) = LLQuest (llfo_rewrite w phi).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_all : forall L X n Y m (w : rew L X n Y m)
    (phi : llfo_semiformula L X (S n)),
  llfo_rewrite w (LLAll phi) = LLAll (llfo_rewrite (rew_q w) phi).
Proof. reflexivity. Qed.

Lemma llfo_rewrite_exs : forall L X n Y m (w : rew L X n Y m)
    (phi : llfo_semiformula L X (S n)),
  llfo_rewrite w (LLExs phi) = LLExs (llfo_rewrite (rew_q w) phi).
Proof. reflexivity. Qed.

Theorem llfo_rewrite_neg : forall L X n Y m (w : rew L X n Y m)
    (phi : llfo_semiformula L X n),
  llfo_rewrite w (llfo_neg phi) = llfo_neg (llfo_rewrite w phi).
Proof.
  intros L X n Y m w phi.
  revert m w. induction phi; intros m w; simpl; try reflexivity.
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi m w).
  - now rewrite (IHphi m w).
  - now rewrite (IHphi (S m) (rew_q w)).
  - now rewrite (IHphi (S m) (rew_q w)).
Qed.

Lemma llfo_rewrite_ext : forall L X n Y m (w v : rew L X n Y m)
    (phi : llfo_semiformula L X n),
  rew_equiv w v -> llfo_rewrite w phi = llfo_rewrite v phi.
Proof.
  intros L X n Y m w v phi Hwv.
  revert m w v Hwv. induction phi; intros m w v Hwv; simpl.
  - f_equal. apply functional_extensionality. intro i. apply Hwv.
  - f_equal. apply functional_extensionality. intro i. apply Hwv.
  - reflexivity.
  - reflexivity.
  - now rewrite (IHphi1 m w v Hwv), (IHphi2 m w v Hwv).
  - now rewrite (IHphi1 m w v Hwv), (IHphi2 m w v Hwv).
  - reflexivity.
  - reflexivity.
  - now rewrite (IHphi1 m w v Hwv), (IHphi2 m w v Hwv).
  - now rewrite (IHphi1 m w v Hwv), (IHphi2 m w v Hwv).
  - now rewrite (IHphi m w v Hwv).
  - now rewrite (IHphi m w v Hwv).
  - f_equal. apply IHphi. now apply rew_q_respects_equiv.
  - f_equal. apply IHphi. now apply rew_q_respects_equiv.
Qed.

Theorem llfo_rewrite_id : forall L X n (phi : llfo_semiformula L X n),
  llfo_rewrite rew_id phi = phi.
Proof.
  intros L X n phi. induction phi; simpl; try congruence.
  - f_equal.
  - f_equal.
  - f_equal.
    transitivity (llfo_rewrite (@rew_id L X (S n)) phi).
    + apply llfo_rewrite_ext. intro t. apply rew_q_id_apply.
    + exact IHphi.
  - f_equal.
    transitivity (llfo_rewrite (@rew_id L X (S n)) phi).
    + apply llfo_rewrite_ext. intro t. apply rew_q_id_apply.
    + exact IHphi.
Qed.

Theorem llfo_rewrite_comp : forall L X n Y m Z o
    (v : rew L Y m Z o) (w : rew L X n Y m)
    (phi : llfo_semiformula L X n),
  llfo_rewrite (rew_comp v w) phi =
  llfo_rewrite v (llfo_rewrite w phi).
Proof.
  intros L X n Y m Z o v w phi.
  revert Y m Z o v w.
  induction phi; intros Y m Z o v w; simpl; try congruence.
  - f_equal.
    transitivity (llfo_rewrite (rew_comp (rew_q v) (rew_q w)) phi).
    + apply llfo_rewrite_ext. intro t. apply rew_q_comp_apply.
    + apply IHphi.
  - f_equal.
    transitivity (llfo_rewrite (rew_comp (rew_q v) (rew_q w)) phi).
    + apply llfo_rewrite_ext. intro t. apply rew_q_comp_apply.
    + apply IHphi.
Qed.

Theorem llfo_complexity_rewrite : forall L X n Y m
    (w : rew L X n Y m) (phi : llfo_semiformula L X n),
  llfo_complexity (llfo_rewrite w phi) = llfo_complexity phi.
Proof.
  intros L X n Y m w phi. revert m w.
  induction phi; intros m w; simpl; try reflexivity.
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi m w).
  - now rewrite (IHphi m w).
  - now rewrite (IHphi (S m) (rew_q w)).
  - now rewrite (IHphi (S m) (rew_q w)).
Qed.

Theorem llfo_negative_rewrite_iff : forall L X n Y m
    (w : rew L X n Y m) (phi : llfo_semiformula L X n),
  llfo_negative m (llfo_rewrite w phi) <-> llfo_negative n phi.
Proof.
  intros L X n Y m w phi. revert m w.
  induction phi; intros m w; simpl.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; constructor.
  - split; intro H; inversion H.
  - rewrite !llfo_negative_par_iff.
    now rewrite (IHphi1 m w), (IHphi2 m w).
  - split; intro H; constructor.
  - split; intro H; inversion H.
  - rewrite !llfo_negative_with_iff.
    now rewrite (IHphi1 m w), (IHphi2 m w).
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; constructor.
  - rewrite !llfo_negative_all_iff.
    apply IHphi.
  - split; intro H; inversion H.
Qed.

Theorem llfo_positive_rewrite_iff : forall L X n Y m
    (w : rew L X n Y m) (phi : llfo_semiformula L X n),
  llfo_positive m (llfo_rewrite w phi) <-> llfo_positive n phi.
Proof.
  intros L X n Y m w phi. revert m w.
  induction phi; intros m w; simpl.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; constructor.
  - split; intro H; inversion H.
  - rewrite !llfo_positive_tensor_iff.
    now rewrite (IHphi1 m w), (IHphi2 m w).
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H; constructor.
  - split; intro H; inversion H.
  - rewrite !llfo_positive_plus_iff.
    now rewrite (IHphi1 m w), (IHphi2 m w).
  - split; intro H; constructor.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - rewrite !llfo_positive_exs_iff.
    apply IHphi.
Qed.

Theorem llfo_is_quest_rewrite_iff : forall L X n Y m
    (w : rew L X n Y m) (phi : llfo_semiformula L X n),
  llfo_is_quest (llfo_rewrite w phi) <-> llfo_is_quest phi.
Proof.
  intros L X n Y m w phi. destruct phi; simpl;
    split; intro H; inversion H; constructor.
Qed.

Lemma llfo_rewrite_lolli : forall L X n Y m (w : rew L X n Y m)
    (phi psi : llfo_semiformula L X n),
  llfo_rewrite w (llfo_lolli phi psi) =
  llfo_lolli (llfo_rewrite w phi) (llfo_rewrite w psi).
Proof. intros. unfold llfo_lolli. simpl. now rewrite llfo_rewrite_neg. Qed.

Definition llfo_map {L X n Y m} (b : Fin.t n -> Fin.t m) (e : X -> Y)
    (phi : llfo_semiformula L X n) : llfo_semiformula L Y m :=
  llfo_rewrite (rew_map b e) phi.

Definition llfo_emb {L O X n} (empty : O -> False)
    (phi : llfo_semiformula L O n) : llfo_semiformula L X n :=
  llfo_rewrite (rew_emb empty) phi.

Definition llfo_shift {L n} (phi : llfo_semiproposition L n) :
    llfo_semiproposition L n := llfo_rewrite rew_shift phi.

Definition llfo_free {L n} (phi : llfo_semiproposition L (n + 1)) :
    llfo_semiproposition L n := llfo_rewrite rew_free phi.

Definition llfo_substitute {L X n m}
    (b : Fin.t n -> semiterm L X m) (phi : llfo_semiformula L X n) :
    llfo_semiformula L X m := llfo_rewrite (rew_subst b) phi.

Lemma llfo_substitute_shift_one_eq_free : forall L
    (phi : llfo_semiproposition L 1),
  llfo_substitute
      (fun _ : Fin.t 1 => Semiterm_fvar 0)
      (llfo_shift phi) =
  @llfo_free L 0 phi.
Proof.
  intros. unfold llfo_substitute, llfo_shift, llfo_free.
  rewrite <- llfo_rewrite_comp.
  apply llfo_rewrite_ext, rew_equiv_of_variables.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    now subst i.
  - intro x. reflexivity.
Qed.

Lemma llfo_substitute_neg_shift_one_eq_neg_free : forall L
    (phi : llfo_semiproposition L 1),
  llfo_substitute
      (fun _ : Fin.t 1 => Semiterm_fvar 0)
      (llfo_neg (llfo_shift phi)) =
  llfo_neg (@llfo_free L 0 phi).
Proof.
  intros. unfold llfo_substitute.
  rewrite llfo_rewrite_neg.
  f_equal. apply llfo_substitute_shift_one_eq_free.
Qed.

Lemma llfo_free_neg : forall L n
    (phi : llfo_semiproposition L (n + 1)),
  llfo_free (llfo_neg phi) = llfo_neg (llfo_free phi).
Proof. intros. unfold llfo_free. apply llfo_rewrite_neg. Qed.

Lemma llfo_shift_neg : forall L n (phi : llfo_semiproposition L n),
  llfo_shift (llfo_neg phi) = llfo_neg (llfo_shift phi).
Proof. intros. unfold llfo_shift. apply llfo_rewrite_neg. Qed.

Lemma llfo_shift_exs : forall L (phi : llfo_semiproposition L 1),
  llfo_shift (LLExs phi) = LLExs (llfo_shift phi).
Proof.
  intros. unfold llfo_shift. simpl. f_equal.
  apply llfo_rewrite_ext, rew_q_shift.
Qed.
