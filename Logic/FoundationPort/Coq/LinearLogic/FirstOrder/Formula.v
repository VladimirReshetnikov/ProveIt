(** Core first-order linear-logic syntax and negation. *)

From Stdlib Require Import Arith.PeanoNat Lia Program.Equality Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.LinearLogic Require Import LogicSymbol.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive llfo_semiformula (L : language) (X : Type) : nat -> Type :=
| LLRel : forall n k, language_rel L k ->
    (Fin.t k -> semiterm L X n) -> llfo_semiformula L X n
| LLNRel : forall n k, language_rel L k ->
    (Fin.t k -> semiterm L X n) -> llfo_semiformula L X n
| LLOne : forall n, llfo_semiformula L X n
| LLFalsum : forall n, llfo_semiformula L X n
| LLTensor : forall n, llfo_semiformula L X n -> llfo_semiformula L X n ->
    llfo_semiformula L X n
| LLPar : forall n, llfo_semiformula L X n -> llfo_semiformula L X n ->
    llfo_semiformula L X n
| LLVerum : forall n, llfo_semiformula L X n
| LLZero : forall n, llfo_semiformula L X n
| LLWith : forall n, llfo_semiformula L X n -> llfo_semiformula L X n ->
    llfo_semiformula L X n
| LLPlus : forall n, llfo_semiformula L X n -> llfo_semiformula L X n ->
    llfo_semiformula L X n
| LLBang : forall n, llfo_semiformula L X n -> llfo_semiformula L X n
| LLQuest : forall n, llfo_semiformula L X n -> llfo_semiformula L X n
| LLAll : forall n, llfo_semiformula L X (S n) -> llfo_semiformula L X n
| LLExs : forall n, llfo_semiformula L X (S n) -> llfo_semiformula L X n.

Arguments LLRel {L X n k} _ _.
Arguments LLNRel {L X n k} _ _.
Arguments LLOne {L X n}.
Arguments LLFalsum {L X n}.
Arguments LLTensor {L X n} _ _.
Arguments LLPar {L X n} _ _.
Arguments LLVerum {L X n}.
Arguments LLZero {L X n}.
Arguments LLWith {L X n} _ _.
Arguments LLPlus {L X n} _ _.
Arguments LLBang {L X n} _.
Arguments LLQuest {L X n} _.
Arguments LLAll {L X n} _.
Arguments LLExs {L X n} _.

Definition llfo_formula L X := llfo_semiformula L X 0.
Definition llfo_semisentence L n := llfo_semiformula L Empty_set n.
Definition llfo_sentence L := llfo_semiformula L Empty_set 0.
Definition llfo_semiproposition L n := llfo_semiformula L nat n.
Definition llfo_proposition L := llfo_formula L nat.

Definition llfo_multiplicative_connective L X n :
    multiplicative_connective (llfo_semiformula L X n).
Proof.
  refine {| linear_tensor := LLTensor;
            linear_par := LLPar |}.
  - intros a b c d H. dependent destruction H. now split.
  - intros a b c d H. dependent destruction H. now split.
Defined.

Definition llfo_multiplicative_neutral L X n :
    multiplicative_neutral (llfo_semiformula L X n) :=
  {| linear_one := LLOne; linear_bottom := LLFalsum |}.

Definition llfo_additive_connective L X n :
    additive_connective (llfo_semiformula L X n).
Proof.
  refine {| linear_with := LLWith;
            linear_plus := LLPlus |}.
  - intros a b c d H. dependent destruction H. now split.
  - intros a b c d H. dependent destruction H. now split.
Defined.

Definition llfo_additive_neutral L X n :
    additive_neutral (llfo_semiformula L X n) :=
  {| linear_top := LLVerum; linear_zero := LLZero |}.

Definition llfo_exponential_connective L X n :
    exponential_connective (llfo_semiformula L X n).
Proof.
  refine {| linear_bang := LLBang;
            linear_quest := LLQuest |}.
  - intros a b H. now dependent destruction H.
  - intros a b H. now dependent destruction H.
Defined.

Lemma llfo_all_injective : forall L X n
    (phi psi : llfo_semiformula L X (S n)),
  LLAll phi = LLAll psi <-> phi = psi.
Proof.
  intros L X n phi psi. split.
  - intro H. now dependent destruction H.
  - now intros ->.
Qed.

Lemma llfo_exs_injective : forall L X n
    (phi psi : llfo_semiformula L X (S n)),
  LLExs phi = LLExs psi <-> phi = psi.
Proof.
  intros L X n phi psi. split.
  - intro H. now dependent destruction H.
  - now intros ->.
Qed.

Fixpoint llfo_neg {L X n} (phi : llfo_semiformula L X n) :
    llfo_semiformula L X n :=
  match phi with
  | LLRel R v => LLNRel R v
  | LLNRel R v => LLRel R v
  | LLOne => LLFalsum
  | LLFalsum => LLOne
  | LLTensor psi chi => LLPar (llfo_neg psi) (llfo_neg chi)
  | LLPar psi chi => LLTensor (llfo_neg psi) (llfo_neg chi)
  | LLVerum => LLZero
  | LLZero => LLVerum
  | LLWith psi chi => LLPlus (llfo_neg psi) (llfo_neg chi)
  | LLPlus psi chi => LLWith (llfo_neg psi) (llfo_neg chi)
  | LLBang psi => LLQuest (llfo_neg psi)
  | LLQuest psi => LLBang (llfo_neg psi)
  | LLAll psi => LLExs (llfo_neg psi)
  | LLExs psi => LLAll (llfo_neg psi)
  end.

Lemma llfo_neg_rel : forall L X n k (R : language_rel L k) v,
  llfo_neg (@LLRel L X n k R v) = LLNRel R v.
Proof. reflexivity. Qed.

Lemma llfo_neg_nrel : forall L X n k (R : language_rel L k) v,
  llfo_neg (@LLNRel L X n k R v) = LLRel R v.
Proof. reflexivity. Qed.

Lemma llfo_neg_all : forall L X n (phi : llfo_semiformula L X (S n)),
  llfo_neg (LLAll phi) = LLExs (llfo_neg phi).
Proof. reflexivity. Qed.

Lemma llfo_neg_exs : forall L X n (phi : llfo_semiformula L X (S n)),
  llfo_neg (LLExs phi) = LLAll (llfo_neg phi).
Proof. reflexivity. Qed.

Theorem llfo_neg_involutive : forall L X n
    (phi : llfo_semiformula L X n),
  llfo_neg (llfo_neg phi) = phi.
Proof.
  intros L X n phi. induction phi; simpl; congruence.
Qed.

Lemma llfo_neg_eq_iff : forall L X n
    (phi psi : llfo_semiformula L X n),
  llfo_neg phi = llfo_neg psi <-> phi = psi.
Proof.
  intros L X n phi psi. split.
  - intro H. apply (f_equal llfo_neg) in H.
    now rewrite !llfo_neg_involutive in H.
  - now intros ->.
Qed.

Definition llfo_lolli {L X n}
    (phi psi : llfo_semiformula L X n) : llfo_semiformula L X n :=
  LLPar (llfo_neg phi) psi.

Definition llfo_wedge {L X n}
    (phi psi : llfo_semiformula L X n) : llfo_semiformula L X n :=
  LLWith phi psi.

Definition llfo_vee {L X n}
    (phi psi : llfo_semiformula L X n) : llfo_semiformula L X n :=
  LLPar phi psi.

Definition llfo_imply {L X n}
    (phi psi : llfo_semiformula L X n) : llfo_semiformula L X n :=
  llfo_lolli phi psi.

Fixpoint llfo_complexity {L X n} (phi : llfo_semiformula L X n) : nat :=
  match phi with
  | LLRel _ _ | LLNRel _ _ | LLOne | LLFalsum | LLVerum | LLZero => 0
  | LLTensor psi chi | LLPar psi chi | LLWith psi chi | LLPlus psi chi =>
      Nat.max (llfo_complexity psi) (llfo_complexity chi) + 1
  | LLBang psi | LLQuest psi | LLAll psi | LLExs psi =>
      llfo_complexity psi + 1
  end.

Theorem llfo_complexity_neg : forall L X n
    (phi : llfo_semiformula L X n),
  llfo_complexity (llfo_neg phi) = llfo_complexity phi.
Proof.
  intros L X n phi. induction phi; simpl; now rewrite ?IHphi1, ?IHphi2, ?IHphi.
Qed.

Inductive llfo_is_quest {L X n} : llfo_semiformula L X n -> Prop :=
| llfo_is_quest_intro : forall phi, llfo_is_quest (LLQuest phi).

Lemma llfo_is_quest_quest : forall L X n
    (phi : llfo_semiformula L X n),
  llfo_is_quest (LLQuest phi).
Proof. constructor. Qed.

Lemma llfo_is_quest_not_bang : forall L X n
    (phi : llfo_semiformula L X n),
  ~ llfo_is_quest (LLBang phi).
Proof. intros L X n phi H. inversion H. Qed.

Lemma llfo_is_quest_not_tensor : forall L X n
    (phi psi : llfo_semiformula L X n),
  ~ llfo_is_quest (LLTensor phi psi).
Proof. intros L X n phi psi H. inversion H. Qed.

Lemma llfo_is_quest_not_par : forall L X n
    (phi psi : llfo_semiformula L X n),
  ~ llfo_is_quest (LLPar phi psi).
Proof. intros L X n phi psi H. inversion H. Qed.

Lemma llfo_is_quest_not_all : forall L X n
    (phi : llfo_semiformula L X (S n)),
  ~ llfo_is_quest (LLAll phi).
Proof. intros L X n phi H. inversion H. Qed.

Lemma llfo_is_quest_not_exs : forall L X n
    (phi : llfo_semiformula L X (S n)),
  ~ llfo_is_quest (LLExs phi).
Proof. intros L X n phi H. inversion H. Qed.

Lemma llfo_is_quest_not_rel : forall L X n k
    (R : language_rel L k) v,
  ~ llfo_is_quest (@LLRel L X n k R v).
Proof. intros L X n k R v H. inversion H. Qed.

Lemma llfo_is_quest_not_nrel : forall L X n k
    (R : language_rel L k) v,
  ~ llfo_is_quest (@LLNRel L X n k R v).
Proof. intros L X n k R v H. inversion H. Qed.

Lemma llfo_is_quest_not_one : forall L X n,
  ~ llfo_is_quest (@LLOne L X n).
Proof. intros L X n H. inversion H. Qed.

Lemma llfo_is_quest_not_falsum : forall L X n,
  ~ llfo_is_quest (@LLFalsum L X n).
Proof. intros L X n H. inversion H. Qed.

Lemma llfo_is_quest_not_verum : forall L X n,
  ~ llfo_is_quest (@LLVerum L X n).
Proof. intros L X n H. inversion H. Qed.

Lemma llfo_is_quest_not_zero : forall L X n,
  ~ llfo_is_quest (@LLZero L X n).
Proof. intros L X n H. inversion H. Qed.

Lemma llfo_is_quest_not_with : forall L X n
    (phi psi : llfo_semiformula L X n),
  ~ llfo_is_quest (LLWith phi psi).
Proof. intros L X n phi psi H. inversion H. Qed.

Lemma llfo_is_quest_not_plus : forall L X n
    (phi psi : llfo_semiformula L X n),
  ~ llfo_is_quest (LLPlus phi psi).
Proof. intros L X n phi psi H. inversion H. Qed.

Inductive llfo_negative {L X} :
    forall n, llfo_semiformula L X n -> Prop :=
| LLNegativeQuest : forall n (phi : llfo_semiformula L X n),
    @llfo_negative L X n (LLQuest phi)
| LLNegativeVerum : forall n,
    @llfo_negative L X n LLVerum
| LLNegativeFalsum : forall n,
    @llfo_negative L X n LLFalsum
| LLNegativePar : forall n (phi psi : llfo_semiformula L X n),
    @llfo_negative L X n phi -> @llfo_negative L X n psi ->
    @llfo_negative L X n (LLPar phi psi)
| LLNegativeWith : forall n (phi psi : llfo_semiformula L X n),
    @llfo_negative L X n phi -> @llfo_negative L X n psi ->
    @llfo_negative L X n (LLWith phi psi)
| LLNegativeAll : forall n (phi : llfo_semiformula L X (S n)),
    @llfo_negative L X (S n) phi -> @llfo_negative L X n (LLAll phi).

Inductive llfo_positive {L X} :
    forall n, llfo_semiformula L X n -> Prop :=
| LLPositiveBang : forall n (phi : llfo_semiformula L X n),
    @llfo_positive L X n (LLBang phi)
| LLPositiveZero : forall n,
    @llfo_positive L X n LLZero
| LLPositiveOne : forall n,
    @llfo_positive L X n LLOne
| LLPositiveTensor : forall n (phi psi : llfo_semiformula L X n),
    @llfo_positive L X n phi -> @llfo_positive L X n psi ->
    @llfo_positive L X n (LLTensor phi psi)
| LLPositivePlus : forall n (phi psi : llfo_semiformula L X n),
    @llfo_positive L X n phi -> @llfo_positive L X n psi ->
    @llfo_positive L X n (LLPlus phi psi)
| LLPositiveExs : forall n (phi : llfo_semiformula L X (S n)),
    @llfo_positive L X (S n) phi -> @llfo_positive L X n (LLExs phi).

Arguments llfo_negative {L X} n _.
Arguments llfo_positive {L X} n _.

Lemma llfo_negative_par_iff : forall L X n
    (phi psi : llfo_semiformula L X n),
  llfo_negative n (LLPar phi psi) <->
  llfo_negative n phi /\ llfo_negative n psi.
Proof.
  intros L X n phi psi. split.
  - intro H. dependent destruction H. now split.
  - intros [Hphi Hpsi]. now constructor.
Qed.

Lemma llfo_negative_with_iff : forall L X n
    (phi psi : llfo_semiformula L X n),
  llfo_negative n (LLWith phi psi) <->
  llfo_negative n phi /\ llfo_negative n psi.
Proof.
  intros L X n phi psi. split.
  - intro H. dependent destruction H. now split.
  - intros [Hphi Hpsi]. now constructor.
Qed.

Lemma llfo_negative_all_iff : forall L X n
    (phi : llfo_semiformula L X (S n)),
  llfo_negative n (LLAll phi) <-> llfo_negative (S n) phi.
Proof.
  intros L X n phi. split.
  - intro H. dependent destruction H. assumption.
  - now constructor.
Qed.

Lemma llfo_positive_tensor_iff : forall L X n
    (phi psi : llfo_semiformula L X n),
  llfo_positive n (LLTensor phi psi) <->
  llfo_positive n phi /\ llfo_positive n psi.
Proof.
  intros L X n phi psi. split.
  - intro H. dependent destruction H. now split.
  - intros [Hphi Hpsi]. now constructor.
Qed.

Lemma llfo_positive_plus_iff : forall L X n
    (phi psi : llfo_semiformula L X n),
  llfo_positive n (LLPlus phi psi) <->
  llfo_positive n phi /\ llfo_positive n psi.
Proof.
  intros L X n phi psi. split.
  - intro H. dependent destruction H. now split.
  - intros [Hphi Hpsi]. now constructor.
Qed.

Lemma llfo_positive_exs_iff : forall L X n
    (phi : llfo_semiformula L X (S n)),
  llfo_positive n (LLExs phi) <-> llfo_positive (S n) phi.
Proof.
  intros L X n phi. split.
  - intro H. dependent destruction H. assumption.
  - now constructor.
Qed.

Theorem llfo_neg_positive_iff_negative : forall L X n
    (phi : llfo_semiformula L X n),
  llfo_positive n (llfo_neg phi) <-> llfo_negative n phi.
Proof.
  intros L X n phi. induction phi; simpl.
  - split; intro H; dependent destruction H.
  - split; intro H; dependent destruction H.
  - split; intro H; dependent destruction H.
  - split; intro H; constructor.
  - split; intro H; dependent destruction H.
  - rewrite llfo_positive_tensor_iff, llfo_negative_par_iff,
      IHphi1, IHphi2. tauto.
  - split; intro H; constructor.
  - split; intro H; dependent destruction H.
  - rewrite llfo_positive_plus_iff, llfo_negative_with_iff,
      IHphi1, IHphi2. tauto.
  - split; intro H; dependent destruction H.
  - split; intro H; dependent destruction H.
  - split; intro H; constructor.
  - rewrite llfo_positive_exs_iff, llfo_negative_all_iff, IHphi.
    tauto.
  - split; intro H; dependent destruction H.
Qed.

Theorem llfo_neg_negative_iff_positive : forall L X n
    (phi : llfo_semiformula L X n),
  llfo_negative n (llfo_neg phi) <-> llfo_positive n phi.
Proof.
  intros L X n phi.
  rewrite <- (llfo_neg_positive_iff_negative (llfo_neg phi)).
  now rewrite llfo_neg_involutive.
Qed.

Theorem llfo_positive_negative_disjoint : forall L X n
    (phi : llfo_semiformula L X n),
  ~ (llfo_positive n phi /\ llfo_negative n phi).
Proof.
  intros L X n phi. induction phi; intros [Hpos Hneg];
    inversion Hpos; inversion Hneg; subst; eauto.
Qed.
