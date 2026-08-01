(** Indexed syntax for intuitionistic first-order logic. *)

From Stdlib Require Import Arith.PeanoNat Logic.Eqdep_dec
  Logic.FunctionalExtensionality Program.Equality Vectors.Fin.
From FoundationModal Require Import GenericSemantics.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive ifo_semiformula (L : language) (X : Type) : nat -> Type :=
| IFOFalsum : forall n, ifo_semiformula L X n
| IFORel : forall n k, language_rel L k ->
    (Fin.t k -> semiterm L X n) -> ifo_semiformula L X n
| IFOAnd : forall n, ifo_semiformula L X n -> ifo_semiformula L X n ->
    ifo_semiformula L X n
| IFOOr : forall n, ifo_semiformula L X n -> ifo_semiformula L X n ->
    ifo_semiformula L X n
| IFOImp : forall n, ifo_semiformula L X n -> ifo_semiformula L X n ->
    ifo_semiformula L X n
| IFOAll : forall n, ifo_semiformula L X (S n) -> ifo_semiformula L X n
| IFOExs : forall n, ifo_semiformula L X (S n) -> ifo_semiformula L X n.

Arguments IFOFalsum {L X n}.
Arguments IFORel {L X n k} _ _.
Arguments IFOAnd {L X n} _ _.
Arguments IFOOr {L X n} _ _.
Arguments IFOImp {L X n} _ _.
Arguments IFOAll {L X n} _.
Arguments IFOExs {L X n} _.

Definition ifo_formula L X := ifo_semiformula L X 0.
Definition ifo_sentence L := ifo_formula L Empty_set.
Definition ifo_semisentence L n := ifo_semiformula L Empty_set n.
Definition ifo_semiproposition L n := ifo_semiformula L nat n.
Definition ifo_proposition L := ifo_semiproposition L 0.

Definition ifo_neg {L X n} (phi : ifo_semiformula L X n) :
    ifo_semiformula L X n := IFOImp phi IFOFalsum.

Definition ifo_verum {L X n} : ifo_semiformula L X n :=
  IFOImp IFOFalsum IFOFalsum.

Definition ifo_connectives L X n :
    generic_connectives (ifo_semiformula L X n) :=
  {| generic_top := ifo_verum;
     generic_bottom := IFOFalsum;
     generic_and := IFOAnd;
     generic_or := IFOOr;
     generic_imp := IFOImp;
     generic_neg := ifo_neg |}.

Lemma ifo_and_injective : forall L X n
    (phi1 phi2 psi1 psi2 : ifo_semiformula L X n),
  IFOAnd phi1 phi2 = IFOAnd psi1 psi2 <->
  phi1 = psi1 /\ phi2 = psi2.
Proof.
  intros. split; [intro H | intros [-> ->]].
  - dependent destruction H. now split.
  - reflexivity.
Qed.

Lemma ifo_or_injective : forall L X n
    (phi1 phi2 psi1 psi2 : ifo_semiformula L X n),
  IFOOr phi1 phi2 = IFOOr psi1 psi2 <->
  phi1 = psi1 /\ phi2 = psi2.
Proof.
  intros. split; [intro H | intros [-> ->]].
  - dependent destruction H. now split.
  - reflexivity.
Qed.

Lemma ifo_imp_injective : forall L X n
    (phi1 phi2 psi1 psi2 : ifo_semiformula L X n),
  IFOImp phi1 phi2 = IFOImp psi1 psi2 <->
  phi1 = psi1 /\ phi2 = psi2.
Proof.
  intros. split; [intro H | intros [-> ->]].
  - dependent destruction H. now split.
  - reflexivity.
Qed.

Lemma ifo_all_injective : forall L X n
    (phi psi : ifo_semiformula L X (S n)),
  IFOAll phi = IFOAll psi <-> phi = psi.
Proof.
  intros. split; [intro H | now intros ->].
  now dependent destruction H.
Qed.

Lemma ifo_exs_injective : forall L X n
    (phi psi : ifo_semiformula L X (S n)),
  IFOExs phi = IFOExs psi <-> phi = psi.
Proof.
  intros. split; [intro H | now intros ->].
  now dependent destruction H.
Qed.

Definition ifo_universal_quantifier L X :
    first_universal_quantifier (ifo_semiformula L X) :=
  {| first_all := fun n phi => @IFOAll L X n phi |}.

Definition ifo_existential_quantifier L X :
    first_existential_quantifier (ifo_semiformula L X) :=
  {| first_exists := fun n phi => @IFOExs L X n phi |}.

Definition ifo_quantifiers L X :
    first_quantifiers (ifo_semiformula L X) :=
  {| first_quantifier_all := ifo_universal_quantifier L X;
     first_quantifier_exists := ifo_existential_quantifier L X |}.

Definition ifo_lcwq L X :
    first_connectives_with_quantifiers (ifo_semiformula L X) :=
  {| first_lcwq_quantifiers := ifo_quantifiers L X;
     first_lcwq_connectives := ifo_connectives L X |}.

Lemma ifo_all_closure_injective : forall L X n
    (phi psi : ifo_semiformula L X n),
  first_all_closure (ifo_universal_quantifier L X) n phi =
  first_all_closure (ifo_universal_quantifier L X) n psi <-> phi = psi.
Proof.
  intros L X n; induction n as [|n IH]; intros phi psi; simpl.
  - reflexivity.
  - rewrite IH. apply ifo_all_injective.
Qed.

Lemma ifo_exs_closure_injective : forall L X n
    (phi psi : ifo_semiformula L X n),
  first_exists_closure (ifo_existential_quantifier L X) n phi =
  first_exists_closure (ifo_existential_quantifier L X) n psi <-> phi = psi.
Proof.
  intros L X n; induction n as [|n IH]; intros phi psi; simpl.
  - reflexivity.
  - rewrite IH. apply ifo_exs_injective.
Qed.

Lemma ifo_all_iter_injective : forall L X k n
    (phi psi : ifo_semiformula L X (k + n)),
  first_all_iter (ifo_universal_quantifier L X) k n phi =
  first_all_iter (ifo_universal_quantifier L X) k n psi <-> phi = psi.
Proof.
  intros L X k; induction k as [|k IH]; intros n phi psi; simpl.
  - reflexivity.
  - rewrite IH. apply ifo_all_injective.
Qed.

Lemma ifo_exs_iter_injective : forall L X k n
    (phi psi : ifo_semiformula L X (k + n)),
  first_exists_iter (ifo_existential_quantifier L X) k n phi =
  first_exists_iter (ifo_existential_quantifier L X) k n psi <-> phi = psi.
Proof.
  intros L X k; induction k as [|k IH]; intros n phi psi; simpl.
  - reflexivity.
  - rewrite IH. apply ifo_exs_injective.
Qed.

Fixpoint ifo_complexity {L X n} (phi : ifo_semiformula L X n) : nat :=
  match phi with
  | IFOFalsum | IFORel _ _ => 0
  | IFOAnd psi chi | IFOOr psi chi | IFOImp psi chi =>
      Nat.max (ifo_complexity psi) (ifo_complexity chi) + 1
  | IFOAll psi | IFOExs psi => ifo_complexity psi + 1
  end.

Lemma ifo_complexity_verum : forall L X n,
  ifo_complexity (@ifo_verum L X n) = 1.
Proof. reflexivity. Qed.

Lemma ifo_complexity_neg : forall L X n (phi : ifo_semiformula L X n),
  ifo_complexity (ifo_neg phi) = ifo_complexity phi + 1.
Proof. intros. unfold ifo_neg. simpl. now rewrite Nat.max_0_r. Qed.

Definition ifo_rel_payload (L : language) (X : Type) (n : nat) :=
  {k : nat & (language_rel L k * (Fin.t k -> semiterm L X n))%type}.

Definition ifo_outer_rel_payload {L X n} (phi : ifo_semiformula L X n) :
    option (ifo_rel_payload L X n) :=
  match phi with
  | @IFORel _ _ _ k R v => Some (existT _ k (R, v))
  | _ => None
  end.

Lemma ifo_rel_injective_same_arity : forall L X n k
    (R S : language_rel L k) (v w : Fin.t k -> semiterm L X n),
  IFORel R v = IFORel S w -> R = S /\ v = w.
Proof.
  intros L X n k R S v w H.
  pose proof (f_equal ifo_outer_rel_payload H) as Hp; simpl in Hp.
  apply option_some_injective in Hp.
  apply (@inj_pair2_eq_dec nat Nat.eq_dec
    (fun j => (language_rel L j *
      (Fin.t j -> semiterm L X n))%type)
    k (R, v) (S, w)) in Hp.
  now injection Hp.
Qed.

Definition ifo_semiformula_eq_dec {L X n}
    (D : language_decidable_eq L)
    (free_eq_dec : forall x y : X, {x = y} + {x <> y})
    (phi psi : ifo_semiformula L X n) : {phi = psi} + {phi <> psi}.
Proof.
  revert psi.
  refine (@ifo_semiformula_rect L X
    (fun n phi => forall psi : ifo_semiformula L X n,
      {phi = psi} + {phi <> psi})
    _ _ _ _ _ _ _ n phi); clear phi n.
  - intros n psi. destruct psi; try (right; discriminate); left; reflexivity.
  - intros n k R v psi. destruct psi as [| n l S w | | | | | ];
      try (right; discriminate).
    destruct (Nat.eq_dec k l) as [Hkl | Hkl].
    + subst l. destruct (@language_rel_eq_dec L D k R S) as [-> | HRS].
      * destruct (@fin_function_pointwise_eq_dec k (semiterm L X n) v w
          (fun i => semiterm_eq_dec (language_func_eq_dec D) free_eq_dec
            (v i) (w i))) as [-> | Hvw].
        { left; reflexivity. }
        { right; intro H. apply Hvw.
          exact (proj2 (ifo_rel_injective_same_arity H)). }
      * right; intro H. apply HRS.
        exact (proj1 (ifo_rel_injective_same_arity H)).
    + right; intro H. apply Hkl.
      pose proof (f_equal ifo_outer_rel_payload H) as Hp; simpl in Hp.
      apply option_some_injective in Hp. now injection Hp.
  - intros n a IHa b IHb psi. destruct psi; try (right; discriminate).
    destruct (IHa psi1) as [-> | Ha].
    2: { right; intro H. apply Ha. now dependent destruction H. }
    destruct (IHb psi2) as [-> | Hb]; [left; reflexivity |].
    right; intro H. apply Hb. now dependent destruction H.
  - intros n a IHa b IHb psi. destruct psi; try (right; discriminate).
    destruct (IHa psi1) as [-> | Ha].
    2: { right; intro H. apply Ha. now dependent destruction H. }
    destruct (IHb psi2) as [-> | Hb]; [left; reflexivity |].
    right; intro H. apply Hb. now dependent destruction H.
  - intros n a IHa b IHb psi. destruct psi; try (right; discriminate).
    destruct (IHa psi1) as [-> | Ha].
    2: { right; intro H. apply Ha. now dependent destruction H. }
    destruct (IHb psi2) as [-> | Hb]; [left; reflexivity |].
    right; intro H. apply Hb. now dependent destruction H.
  - intros n a IHa psi. destruct psi; try (right; discriminate).
    destruct (IHa psi) as [-> | Ha]; [left; reflexivity |].
    right; intro H. apply Ha. now dependent destruction H.
  - intros n a IHa psi. destruct psi; try (right; discriminate).
    destruct (IHa psi) as [-> | Ha]; [left; reflexivity |].
    right; intro H. apply Ha. now dependent destruction H.
Defined.

Inductive ifo_negative {L X} : forall n, ifo_semiformula L X n -> Prop :=
| IFONegativeFalsum : forall n, @ifo_negative L X n IFOFalsum
| IFONegativeAnd : forall n (phi psi : ifo_semiformula L X n),
    @ifo_negative L X n phi -> @ifo_negative L X n psi ->
    @ifo_negative L X n (IFOAnd phi psi)
| IFONegativeImp : forall n (phi psi : ifo_semiformula L X n),
    @ifo_negative L X n psi -> @ifo_negative L X n (IFOImp phi psi)
| IFONegativeAll : forall n (phi : ifo_semiformula L X (S n)),
    @ifo_negative L X (S n) phi -> @ifo_negative L X n (IFOAll phi).

Arguments ifo_negative {L X} n _.

Lemma ifo_negative_and_iff : forall L X n
    (phi psi : ifo_semiformula L X n),
  ifo_negative n (IFOAnd phi psi) <->
  ifo_negative n phi /\ ifo_negative n psi.
Proof.
  intros. split; [intro H | intros [Hphi Hpsi]].
  - dependent destruction H. now split.
  - now constructor.
Qed.

Lemma ifo_negative_imp_iff : forall L X n
    (phi psi : ifo_semiformula L X n),
  ifo_negative n (IFOImp phi psi) <-> ifo_negative n psi.
Proof.
  intros. split; [intro H | intro H].
  - now dependent destruction H.
  - now constructor.
Qed.

Lemma ifo_negative_all_iff : forall L X n
    (phi : ifo_semiformula L X (S n)),
  ifo_negative n (IFOAll phi) <-> ifo_negative (S n) phi.
Proof.
  intros. split; [intro H | intro H].
  - now dependent destruction H.
  - now constructor.
Qed.

Lemma ifo_negative_verum : forall L X n,
  ifo_negative n (@ifo_verum L X n).
Proof. intros. constructor. constructor. Qed.

Lemma ifo_negative_neg : forall L X n (phi : ifo_semiformula L X n),
  ifo_negative n (ifo_neg phi).
Proof. intros. constructor. constructor. Qed.

Lemma ifo_negative_not_or : forall L X n
    (phi psi : ifo_semiformula L X n),
  ~ ifo_negative n (IFOOr phi psi).
Proof. intros L X n phi psi H. inversion H. Qed.

Lemma ifo_negative_not_exs : forall L X n
    (phi : ifo_semiformula L X (S n)),
  ~ ifo_negative n (IFOExs phi).
Proof. intros L X n phi H. inversion H. Qed.

Lemma ifo_negative_not_rel : forall L X n k
    (R : language_rel L k) v,
  ~ ifo_negative n (@IFORel L X n k R v).
Proof. intros L X n k R v H. inversion H. Qed.

Definition ifo_negative_dec {L X n} (phi : ifo_semiformula L X n) :
    {ifo_negative n phi} + {~ ifo_negative n phi}.
Proof.
  refine (@ifo_semiformula_rect L X
    (fun n phi => {ifo_negative n phi} + {~ ifo_negative n phi})
    _ _ _ _ _ _ _ n phi).
  - intros. left. constructor.
  - intros. right. intro Hneg. inversion Hneg.
  - intros m a Ha b Hb. destruct Ha as [Ha | Ha], Hb as [Hb | Hb].
    + left. now constructor.
    + right. intro H. apply Hb. dependent destruction H. assumption.
    + right. intro H. apply Ha. dependent destruction H. assumption.
    + right. intro H. apply Ha. dependent destruction H. assumption.
  - intros. right. intro Hneg. inversion Hneg.
  - intros m a Ha b Hb. destruct Hb as [Hb | Hb].
    + left. now constructor.
    + right. intro H. apply Hb. dependent destruction H. assumption.
  - intros m a Ha. destruct Ha as [Ha | Ha].
    + left. now constructor.
    + right. intro H. apply Ha. dependent destruction H. assumption.
  - intros. right. intro Hneg. inversion Hneg.
Defined.
