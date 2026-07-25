(**
  Finite words of modal operators and their reduction in S5.

  This file ports the mathematical content of Foundation's
  [Modal/Modality/Basic.lean] and [Modal/Modality/S5.lean].  A modality is a
  word over box, diamond, and negation; composition is concatenation of
  words, and applying a word wraps a formula from left to right.

  Foundation represents finite collections of modalities by Lean
  [Finset]s.  The Coq presentation uses duplicate-insensitive list
  membership.  This removes representation-only coercions while retaining
  the enumeration, maximum-size, splitting, and reduction theorems.

  The final section proves canonical completeness for the already existing
  presentation of S5 (T + Five).  Consequently the six-normal-form theorem
  is genuinely syntactic: every returned arrow is an [S5_proves]
  derivation, not a semantic-validity surrogate.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke HilbertKSoundness Correspondence
  NormalHilbert CanonicalK CanonicalExtensions.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Syntax and elementary algebra *)

Inductive modality : Type :=
| MEmpty : modality
| MBox : modality -> modality
| MDia : modality -> modality
| MNeg : modality -> modality.

Definition modality_eq_dec : forall m n : modality, {m = n} + {m <> n}.
Proof. decide equality. Defined.

Definition pure_box : modality := MBox MEmpty.
Definition pure_dia : modality := MDia MEmpty.
Definition pure_neg : modality := MNeg MEmpty.

(** Smart negation cancels one leading syntactic negation. *)
Definition modality_sneg (m : modality) : modality :=
  match m with
  | MNeg n => n
  | _ => MNeg m
  end.

Definition pure_sneg : modality := modality_sneg MEmpty.

Fixpoint modality_add (m n : modality) : modality :=
  match m with
  | MEmpty => n
  | MBox k => MBox (modality_add k n)
  | MDia k => MDia (modality_add k n)
  | MNeg k => MNeg (modality_add k n)
  end.

Lemma modality_add_empty_left :
  forall m, modality_add MEmpty m = m.
Proof. reflexivity. Qed.

Lemma modality_add_box_left :
  forall m n, modality_add (MBox m) n = MBox (modality_add m n).
Proof. reflexivity. Qed.

Lemma modality_add_dia_left :
  forall m n, modality_add (MDia m) n = MDia (modality_add m n).
Proof. reflexivity. Qed.

Lemma modality_add_neg_left :
  forall m n, modality_add (MNeg m) n = MNeg (modality_add m n).
Proof. reflexivity. Qed.

Lemma modality_add_empty_right :
  forall m, modality_add m MEmpty = m.
Proof.
  induction m; simpl; now f_equal.
Qed.

Lemma modality_add_assoc :
  forall m1 m2 m3,
    modality_add (modality_add m1 m2) m3 =
    modality_add m1 (modality_add m2 m3).
Proof.
  induction m1; intros m2 m3; simpl; now f_equal.
Qed.

Inductive polarity : Type := Positive | Negative.

Definition polarity_inv (P : polarity) : polarity :=
  match P with Positive => Negative | Negative => Positive end.

Lemma polarity_inv_involutive :
  forall P, polarity_inv (polarity_inv P) = P.
Proof. now destruct P. Qed.

Fixpoint modality_polarity (m : modality) : polarity :=
  match m with
  | MEmpty => Positive
  | MBox k | MDia k => modality_polarity k
  | MNeg k => polarity_inv (modality_polarity k)
  end.

Lemma modality_empty_positive :
  modality_polarity MEmpty = Positive.
Proof. reflexivity. Qed.

Lemma modality_pure_box_positive :
  modality_polarity (MBox MEmpty) = Positive.
Proof. reflexivity. Qed.

Lemma modality_pure_dia_positive :
  modality_polarity (MDia MEmpty) = Positive.
Proof. reflexivity. Qed.

Lemma modality_pure_neg_negative :
  modality_polarity (MNeg MEmpty) = Negative.
Proof. reflexivity. Qed.

Lemma modality_box_polarity :
  forall m, modality_polarity (MBox m) = modality_polarity m.
Proof. reflexivity. Qed.

Lemma modality_dia_polarity :
  forall m, modality_polarity (MDia m) = modality_polarity m.
Proof. reflexivity. Qed.

Lemma modality_neg_polarity :
  forall m,
    modality_polarity (MNeg m) = polarity_inv (modality_polarity m).
Proof. reflexivity. Qed.

Fixpoint modality_size (m : modality) : nat :=
  match m with
  | MEmpty => 0
  | MBox k | MDia k | MNeg k => S (modality_size k)
  end.

Lemma modality_empty_size_zero : modality_size MEmpty = 0.
Proof. reflexivity. Qed.

Lemma modality_pure_box_size_one : modality_size (MBox MEmpty) = 1.
Proof. reflexivity. Qed.

Lemma modality_pure_dia_size_one : modality_size (MDia MEmpty) = 1.
Proof. reflexivity. Qed.

Lemma modality_pure_neg_size_one : modality_size (MNeg MEmpty) = 1.
Proof. reflexivity. Qed.

Lemma modality_box_size_succ :
  forall m, modality_size (MBox m) = S (modality_size m).
Proof. reflexivity. Qed.

Lemma modality_dia_size_succ :
  forall m, modality_size (MDia m) = S (modality_size m).
Proof. reflexivity. Qed.

Lemma modality_neg_size_succ :
  forall m, modality_size (MNeg m) = S (modality_size m).
Proof. reflexivity. Qed.

Lemma modality_sneg_size_le_succ :
  forall m, modality_size (modality_sneg m) <= S (modality_size m).
Proof. destruct m; simpl; lia. Qed.

Lemma modality_sneg_size_le_neg_size :
  forall m, modality_size (modality_sneg m) <= modality_size (MNeg m).
Proof. intro m; apply modality_sneg_size_le_succ. Qed.

Lemma modality_sneg_twice_size_le_succ :
  forall m,
    modality_size (modality_sneg (modality_sneg m)) <=
    S (modality_size m).
Proof. destruct m; simpl; try lia; destruct m; simpl; lia. Qed.

Lemma modality_size_zero_iff :
  forall m, modality_size m = 0 <-> m = MEmpty.
Proof.
  destruct m; simpl; split; intro H; try reflexivity; try discriminate.
Qed.

Lemma modality_size_one_iff :
  forall m,
    modality_size m = 1 <->
    m = MBox MEmpty \/ m = MDia MEmpty \/ m = MNeg MEmpty.
Proof.
  destruct m as [|m|m|m]; simpl.
  - intuition congruence.
  - rewrite Nat.succ_inj_wd, modality_size_zero_iff. intuition congruence.
  - rewrite Nat.succ_inj_wd, modality_size_zero_iff. intuition congruence.
  - rewrite Nat.succ_inj_wd, modality_size_zero_iff. intuition congruence.
Qed.

Lemma modality_size_two_iff :
  forall m,
    modality_size m = 2 <->
    m = MBox (MBox MEmpty) \/
    m = MBox (MDia MEmpty) \/
    m = MBox (MNeg MEmpty) \/
    m = MDia (MBox MEmpty) \/
    m = MDia (MDia MEmpty) \/
    m = MDia (MNeg MEmpty) \/
    m = MNeg (MBox MEmpty) \/
    m = MNeg (MDia MEmpty) \/
    m = MNeg (MNeg MEmpty).
Proof.
  destruct m as [|m|m|m]; simpl.
  - intuition congruence.
  - rewrite Nat.succ_inj_wd, modality_size_one_iff. intuition congruence.
  - rewrite Nat.succ_inj_wd, modality_size_one_iff. intuition congruence.
  - rewrite Nat.succ_inj_wd, modality_size_one_iff. intuition congruence.
Qed.

Lemma modality_add_size :
  forall m1 m2,
    modality_size (modality_add m1 m2) =
    modality_size m1 + modality_size m2.
Proof.
  induction m1; intro m2; simpl; rewrite ?IHm1; lia.
Qed.

(** Splitting is most naturally proved by consuming the requested prefix. *)
Lemma modality_split :
  forall n1 m n2,
    modality_size m = n1 + n2 ->
    exists m1 m2,
      modality_size m1 = n1 /\
      modality_size m2 = n2 /\
      m = modality_add m1 m2.
Proof.
  induction n1 as [|n1 IH]; intros m n2 Hsize.
  - exists MEmpty, m. simpl in *. now repeat split.
  - destruct m as [|m|m|m]; simpl in Hsize; try lia;
      apply Nat.succ_inj in Hsize;
      destruct (IH m n2 Hsize) as [m1 [m2 [H1 [H2 ->]]]];
      [exists (MBox m1), m2 | exists (MDia m1), m2 |
       exists (MNeg m1), m2]; simpl; repeat split; try assumption; try reflexivity; lia.
Qed.

Lemma modality_split_left_one :
  forall m n,
    modality_size m = S n ->
    exists m1 m2,
      modality_size m1 = 1 /\
      modality_size m2 = n /\
      m = modality_add m1 m2.
Proof.
  intros m n H. apply (@modality_split 1 m n). simpl. exact H.
Qed.

Lemma modality_split_left_one_shape :
  forall m n,
    modality_size m = S n ->
    exists k,
      modality_size k = n /\
      (m = MBox k \/ m = MDia k \/ m = MNeg k).
Proof.
  intros m n H.
  destruct (modality_split_left_one H)
    as [m1 [k [Hone [Hk ->]]]].
  exists k; split; [exact Hk |].
  apply modality_size_one_iff in Hone.
  destruct Hone as [-> | [-> | ->]]; simpl; tauto.
Qed.

Lemma modality_split_right_one :
  forall m n,
    modality_size m = S n ->
    exists m1 m2,
      modality_size m1 = n /\
      modality_size m2 = 1 /\
      m = modality_add m1 m2.
Proof.
  intros m n H. apply (@modality_split n m 1). lia.
Qed.

Lemma modality_split_left_two_shape :
  forall m n,
    modality_size m = n + 2 ->
    exists k,
      modality_size k = n /\
      (m = MBox (MBox k) \/
       m = MBox (MDia k) \/
       m = MBox (MNeg k) \/
       m = MDia (MBox k) \/
       m = MDia (MDia k) \/
       m = MDia (MNeg k) \/
       m = MNeg (MBox k) \/
       m = MNeg (MDia k) \/
       m = MNeg (MNeg k)).
Proof.
  intros m n H.
  destruct (@modality_split 2 m n) as [m1 [k [Htwo [Hk ->]]]]; [lia |].
  exists k; split; [exact Hk |].
  apply modality_size_two_iff in Htwo.
  destruct Htwo as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    simpl; tauto.
Qed.

Lemma modality_split_le :
  forall n1 m n2,
    modality_size m <= n1 + n2 ->
    exists m1 m2,
      modality_size m1 <= n1 /\
      modality_size m2 <= n2 /\
      m = modality_add m1 m2.
Proof.
  induction n1 as [|n1 IH]; intros m n2 Hsize.
  - exists MEmpty, m. simpl in *. now repeat split.
  - destruct m as [|m|m|m].
    + exists MEmpty, MEmpty. simpl. repeat split; try lia; reflexivity.
    + simpl in Hsize.
      assert (Htail : modality_size m <= n1 + n2) by lia.
      destruct (IH m n2 Htail) as [m1 [m2 [H1 [H2 ->]]]].
      exists (MBox m1), m2. simpl. repeat split; try lia; reflexivity.
    + simpl in Hsize.
      assert (Htail : modality_size m <= n1 + n2) by lia.
      destruct (IH m n2 Htail) as [m1 [m2 [H1 [H2 ->]]]].
      exists (MDia m1), m2. simpl. repeat split; try lia; reflexivity.
    + simpl in Hsize.
      assert (Htail : modality_size m <= n1 + n2) by lia.
      destruct (IH m n2 Htail) as [m1 [m2 [H1 [H2 ->]]]].
      exists (MNeg m1), m2. simpl. repeat split; try lia; reflexivity.
Qed.

Lemma modality_split_left_le_one :
  forall m n,
    modality_size m <= S n ->
    exists m1 m2,
      modality_size m1 <= 1 /\
      modality_size m2 <= n /\
      m = modality_add m1 m2.
Proof.
  intros m n H. apply (@modality_split_le 1 m n). simpl. exact H.
Qed.

Lemma modality_split_right_le_one :
  forall m n,
    modality_size m <= S n ->
    exists m1 m2,
      modality_size m1 <= n /\
      modality_size m2 <= 1 /\
      m = modality_add m1 m2.
Proof.
  intros m n H. apply (@modality_split_le n m 1). lia.
Qed.

(** * Acting on formulas *)

Fixpoint apply_modality {AtomType}
    (m : modality) (p : formula AtomType) : formula AtomType :=
  match m with
  | MEmpty => p
  | MBox k => Box (apply_modality k p)
  | MDia k => Dia (apply_modality k p)
  | MNeg k => Neg (apply_modality k p)
  end.

Lemma apply_modality_add :
  forall AtomType (m1 m2 : modality) (p : formula AtomType),
    apply_modality m1 (apply_modality m2 p) =
    apply_modality (modality_add m1 m2) p.
Proof.
  intros AtomType m1; induction m1; intros m2 p; simpl; now rewrite ?IHm1.
Qed.

Lemma substitute_apply_modality :
  forall (A B : Type) (sigma : A -> formula B) m (p : formula A),
    substitute sigma (apply_modality m p) =
    apply_modality m (substitute sigma p).
Proof.
  intros A B sigma m; induction m; intro p; simpl; now rewrite ?IHm.
Qed.

(** * Syntactic translations and equivalences *)

Definition modality_translation
    (Ax : modal_axiom_schema) (m1 m2 : modality) : Prop :=
  forall p : formula nat,
    normal_proves Ax
      (Imp (apply_modality m1 p) (apply_modality m2 p)).

Definition modality_equivalence
    (Ax : modal_axiom_schema) (m1 m2 : modality) : Prop :=
  forall p : formula nat,
    normal_proves Ax
      (Iff (apply_modality m1 p) (apply_modality m2 p)).

Lemma normal_proves_imp_trans_modality :
  forall Ax (p q r : formula nat),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp q r) ->
    normal_proves Ax (Imp p r).
Proof.
  intros Ax p q r Hpq Hqr.
  eapply Np_mp.
  - eapply Np_mp.
    + exact (Np_imply_S p q r).
    + apply (Np_mp (Np_imply_K (Imp q r) p)). exact Hqr.
  - exact Hpq.
Qed.

Lemma K_proves_iff_left_modality :
  forall p q : formula nat, K_proves (Imp (Iff p q) (Imp p q)).
Proof.
  intros p q. apply K_complete. intros F V w.
  rewrite satisfies_imp, satisfies_iff. tauto.
Qed.

Lemma K_proves_iff_right_modality :
  forall p q : formula nat, K_proves (Imp (Iff p q) (Imp q p)).
Proof.
  intros p q. apply K_complete. intros F V w.
  rewrite satisfies_imp, satisfies_iff. tauto.
Qed.

Lemma K_proves_iff_intro_modality :
  forall p q : formula nat,
    K_proves (Imp (Imp p q) (Imp (Imp q p) (Iff p q))).
Proof.
  intros p q. apply K_complete. intros F V w.
  repeat rewrite satisfies_imp. rewrite satisfies_iff. tauto.
Qed.

Lemma K_proves_contraposition_modality :
  forall p q : formula nat,
    K_proves (Imp (Imp p q) (Imp (Neg q) (Neg p))).
Proof.
  intros p q. apply K_complete. intros F V w.
  repeat rewrite satisfies_imp. repeat rewrite satisfies_neg. tauto.
Qed.

Lemma normal_proves_iff_left_modality :
  forall Ax (p q : formula nat),
    normal_proves Ax (Iff p q) -> normal_proves Ax (Imp p q).
Proof.
  intros Ax p q H. eapply Np_mp; [|exact H].
  apply K_proves_normal. apply K_proves_iff_left_modality.
Qed.

Lemma normal_proves_iff_right_modality :
  forall Ax (p q : formula nat),
    normal_proves Ax (Iff p q) -> normal_proves Ax (Imp q p).
Proof.
  intros Ax p q H. eapply Np_mp; [|exact H].
  apply K_proves_normal. apply K_proves_iff_right_modality.
Qed.

Lemma normal_proves_iff_intro_modality :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp q p) ->
    normal_proves Ax (Iff p q).
Proof.
  intros Ax p q Hpq Hqp.
  eapply Np_mp; [|exact Hqp].
  eapply Np_mp; [|exact Hpq].
  apply K_proves_normal. apply K_proves_iff_intro_modality.
Qed.

Lemma normal_proves_contraposition_modality :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp (Neg q) (Neg p)).
Proof.
  intros Ax p q H. eapply Np_mp; [|exact H].
  apply K_proves_normal. apply K_proves_contraposition_modality.
Qed.

Lemma normal_proves_box_regularity_modality :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp (Box p) (Box q)).
Proof.
  intros Ax p q H.
  eapply Np_mp; [exact (Np_modal_K p q) | now apply Np_nec].
Qed.

Lemma normal_proves_dia_regularity_modality :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p q) ->
    normal_proves Ax (Imp (Dia p) (Dia q)).
Proof.
  intros Ax p q H.
  unfold Dia.
  apply normal_proves_contraposition_modality.
  apply normal_proves_box_regularity_modality.
  now apply normal_proves_contraposition_modality.
Qed.

Lemma modality_translation_refl :
  forall Ax m, modality_translation Ax m m.
Proof.
  intros Ax m p. apply K_proves_normal. apply K_proves_identity.
Qed.

Lemma modality_translation_trans :
  forall Ax m1 m2 m3,
    modality_translation Ax m1 m2 ->
    modality_translation Ax m2 m3 ->
    modality_translation Ax m1 m3.
Proof.
  intros Ax m1 m2 m3 H12 H23 p.
  eapply normal_proves_imp_trans_modality; [apply H12 | apply H23].
Qed.

Lemma modality_equivalence_iff_bitranslation :
  forall Ax m1 m2,
    modality_equivalence Ax m1 m2 <->
    modality_translation Ax m1 m2 /\ modality_translation Ax m2 m1.
Proof.
  intros Ax m1 m2; split.
  - intro H; split; intro p.
    + apply normal_proves_iff_left_modality. apply H.
    + apply normal_proves_iff_right_modality. apply H.
  - intros [H12 H21] p.
    apply normal_proves_iff_intro_modality; [apply H12 | apply H21].
Qed.

Lemma modality_equivalence_refl :
  forall Ax m, modality_equivalence Ax m m.
Proof.
  intros Ax m. apply modality_equivalence_iff_bitranslation.
  split; apply modality_translation_refl.
Qed.

Lemma modality_equivalence_sym :
  forall Ax m1 m2,
    modality_equivalence Ax m1 m2 -> modality_equivalence Ax m2 m1.
Proof.
  intros Ax m1 m2 H.
  apply modality_equivalence_iff_bitranslation in H.
  apply modality_equivalence_iff_bitranslation. tauto.
Qed.

Lemma modality_equivalence_trans :
  forall Ax m1 m2 m3,
    modality_equivalence Ax m1 m2 ->
    modality_equivalence Ax m2 m3 ->
    modality_equivalence Ax m1 m3.
Proof.
  intros Ax m1 m2 m3 H12 H23.
  apply modality_equivalence_iff_bitranslation in H12.
  apply modality_equivalence_iff_bitranslation in H23.
  apply modality_equivalence_iff_bitranslation.
  destruct H12 as [H12 H21]. destruct H23 as [H23 H32]. split.
  - eapply modality_translation_trans; eauto.
  - eapply modality_translation_trans; eauto.
Qed.

Lemma normal_proves_modality_congruence :
  forall Ax m (p q : formula nat),
    normal_proves Ax (Iff p q) ->
    normal_proves Ax
      (Iff (apply_modality m p) (apply_modality m q)).
Proof.
  intros Ax m; induction m; intros p q H; simpl.
  - exact H.
  - apply normal_proves_iff_intro_modality;
      apply normal_proves_box_regularity_modality;
      [apply normal_proves_iff_left_modality |
       apply normal_proves_iff_right_modality]; now apply IHm.
  - apply normal_proves_iff_intro_modality;
      apply normal_proves_dia_regularity_modality;
      [apply normal_proves_iff_left_modality |
       apply normal_proves_iff_right_modality]; now apply IHm.
  - apply normal_proves_iff_intro_modality;
      apply normal_proves_contraposition_modality;
      [apply normal_proves_iff_right_modality |
       apply normal_proves_iff_left_modality]; now apply IHm.
Qed.

(** Foundation defines translations from an atomic instance and then uses
    substitution.  Because [modality_translation] is formula-polymorphic,
    its application lemma is definitionally available; the following
    theorem recovers the atomic constructor when that presentation is more
    convenient. *)
Lemma modality_translation_of_atom :
  forall Ax,
    schema_substitution_closed Ax ->
    forall m1 m2 (a : nat),
      normal_proves Ax
        (Imp (apply_modality m1 (Atom a))
             (apply_modality m2 (Atom a))) ->
      modality_translation Ax m1 m2.
Proof.
  intros Ax Hclosed m1 m2 a Hatom p.
  pose (sigma := fun b : nat =>
    if Nat.eq_dec b a then p else Atom b).
  pose proof (@normal_proves_substitute Ax Hclosed nat nat sigma
    (Imp (apply_modality m1 (Atom a))
         (apply_modality m2 (Atom a))) Hatom) as Hsub.
  change
    (normal_proves Ax
      (Imp (substitute sigma (apply_modality m1 (Atom a)))
           (substitute sigma (apply_modality m2 (Atom a))))) in Hsub.
  rewrite !substitute_apply_modality in Hsub.
  assert (Hs : sigma a = p).
  { unfold sigma. destruct (Nat.eq_dec a a); congruence. }
  simpl in Hsub. now rewrite Hs in Hsub.
Qed.

Lemma modality_equivalence_of_atom :
  forall Ax,
    schema_substitution_closed Ax ->
    forall m1 m2 (a : nat),
      normal_proves Ax
        (Iff (apply_modality m1 (Atom a))
             (apply_modality m2 (Atom a))) ->
      modality_equivalence Ax m1 m2.
Proof.
  intros Ax Hclosed m1 m2 a Hiff.
  apply modality_equivalence_iff_bitranslation. split.
  - eapply (@modality_translation_of_atom Ax Hclosed m1 m2 a).
    now apply normal_proves_iff_left_modality.
  - eapply (@modality_translation_of_atom Ax Hclosed m2 m1 a).
    now apply normal_proves_iff_right_modality.
Qed.

Lemma normal_proves_substitute_apply_modality_iff :
  forall Ax (sigma : nat -> formula nat) m p,
    normal_proves Ax
      (Iff (substitute sigma (apply_modality m p))
           (apply_modality m (substitute sigma p))).
Proof.
  intros Ax sigma m p. rewrite substitute_apply_modality.
  apply normal_proves_iff_intro_modality;
    apply K_proves_normal; apply K_proves_identity.
Qed.

Lemma normal_proves_substitute_apply_modality_forward :
  forall Ax (sigma : nat -> formula nat) m p,
    normal_proves Ax
      (Imp (substitute sigma (apply_modality m p))
           (apply_modality m (substitute sigma p))).
Proof.
  intros. apply normal_proves_iff_left_modality.
  apply normal_proves_substitute_apply_modality_iff.
Qed.

Lemma normal_proves_substitute_apply_modality_backward :
  forall Ax (sigma : nat -> formula nat) m p,
    normal_proves Ax
      (Imp (apply_modality m (substitute sigma p))
           (substitute sigma (apply_modality m p))).
Proof.
  intros. apply normal_proves_iff_right_modality.
  apply normal_proves_substitute_apply_modality_iff.
Qed.

Lemma apply_modality_substitute_of_substitute_apply_modality :
  forall Ax (sigma : nat -> formula nat) m p,
    normal_proves Ax (substitute sigma (apply_modality m p)) ->
    normal_proves Ax (apply_modality m (substitute sigma p)).
Proof.
  intros Ax sigma m p H.
  rewrite <- substitute_apply_modality. exact H.
Qed.

Lemma substitute_apply_modality_of_apply_modality_substitute :
  forall Ax (sigma : nat -> formula nat) m p,
    normal_proves Ax (apply_modality m (substitute sigma p)) ->
    normal_proves Ax (substitute sigma (apply_modality m p)).
Proof.
  intros Ax sigma m p H.
  rewrite substitute_apply_modality. exact H.
Qed.

Lemma modality_translation_expand_right :
  forall Ax m1 m2 suffix,
    modality_translation Ax m1 m2 ->
    modality_translation Ax (modality_add m1 suffix)
      (modality_add m2 suffix).
Proof.
  intros Ax m1 m2 suffix H p.
  repeat rewrite <- apply_modality_add. apply H.
Qed.

Lemma modality_translation_expand_left :
  forall Ax prefix m1 m2,
    modality_translation Ax prefix MEmpty ->
    modality_translation Ax m1 m2 ->
    modality_translation Ax (modality_add prefix m1) m2.
Proof.
  intros Ax prefix m1 m2 Hstrip H12 p.
  rewrite <- apply_modality_add.
  eapply normal_proves_imp_trans_modality; [apply Hstrip | apply H12].
Qed.

Lemma modality_equivalence_expand_right :
  forall Ax m1 m2 suffix,
    modality_equivalence Ax m1 m2 ->
    modality_equivalence Ax (modality_add m1 suffix)
      (modality_add m2 suffix).
Proof.
  intros Ax m1 m2 suffix H.
  apply modality_equivalence_iff_bitranslation in H.
  apply modality_equivalence_iff_bitranslation.
  destruct H as [H12 H21]; split; now apply modality_translation_expand_right.
Qed.

Lemma modality_equivalence_expand_left :
  forall Ax prefix m1 m2,
    modality_equivalence Ax m1 m2 ->
    modality_equivalence Ax (modality_add prefix m1)
      (modality_add prefix m2).
Proof.
  intros Ax prefix m1 m2 H p.
  repeat rewrite <- apply_modality_add.
  apply normal_proves_modality_congruence. apply H.
Qed.

(** The five basic normal-modal equivalences, including the duality whose
    Lean proof contains an admitted subgoal at the pinned revision. *)
Lemma modality_equiv_dia_neg_box_neg :
  forall Ax,
    modality_equivalence Ax (MDia MEmpty)
      (MNeg (MBox (MNeg MEmpty))).
Proof.
  intros Ax p. simpl. apply normal_proves_iff_intro_modality;
    apply K_proves_normal; apply K_proves_identity.
Qed.

Lemma modality_equiv_double_neg :
  forall Ax,
    modality_equivalence Ax (MNeg (MNeg MEmpty)) MEmpty.
Proof.
  intros Ax p. simpl. apply normal_proves_iff_intro_modality;
    apply K_proves_normal; [apply K_proves_dne | apply K_proves_dni].
Qed.

Lemma modality_equiv_box_neg_neg_dia :
  forall Ax,
    modality_equivalence Ax (MBox (MNeg MEmpty))
      (MNeg (MDia MEmpty)).
Proof.
  intros Ax p. simpl. apply normal_proves_iff_intro_modality;
    apply K_proves_normal; [apply K_proves_dni | apply K_proves_dne].
Qed.

Lemma modality_equiv_dia_neg_neg_box :
  forall Ax,
    modality_equivalence Ax (MDia (MNeg MEmpty))
      (MNeg (MBox MEmpty)).
Proof.
  intros Ax p. simpl.
  apply normal_proves_iff_intro_modality.
  - unfold Dia. apply normal_proves_contraposition_modality.
    apply normal_proves_box_regularity_modality.
    apply K_proves_normal. apply K_proves_dni.
  - unfold Dia. apply normal_proves_contraposition_modality.
    apply normal_proves_box_regularity_modality.
    apply K_proves_normal. apply K_proves_dne.
Qed.

Lemma modality_equiv_box_neg_dia_neg :
  forall Ax,
    modality_equivalence Ax (MBox MEmpty)
      (MNeg (MDia (MNeg MEmpty))).
Proof.
  intros Ax p. simpl.
  pose proof (modality_equiv_dia_neg_neg_box Ax p) as H.
  apply normal_proves_modality_congruence with (m := MNeg MEmpty) in H.
  simpl in H.
  eapply normal_proves_iff_intro_modality.
  - eapply normal_proves_imp_trans_modality.
    + apply K_proves_normal. apply K_proves_dni.
    + apply normal_proves_iff_right_modality. exact H.
  - eapply normal_proves_imp_trans_modality.
    + apply normal_proves_iff_left_modality. exact H.
    + apply K_proves_normal. apply K_proves_dne.
Qed.

(** * Finite enumerations by size *)

Definition modalities := list modality.

Fixpoint modalities_max_size (M : modalities) : nat :=
  match M with
  | [] => 0
  | m :: rest => Nat.max (modality_size m) (modalities_max_size rest)
  end.

Lemma modality_size_le_max_of_mem :
  forall M m, In m M -> modality_size m <= modalities_max_size M.
Proof.
  induction M as [|x M IH]; intros m Hmem; simpl in *.
  - contradiction.
  - destruct Hmem as [-> | Hmem].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hmem | apply Nat.le_max_r].
Qed.

Fixpoint modalities_all_of_size (n : nat) : modalities :=
  match n with
  | 0 => [MEmpty]
  | S k =>
      map MNeg (modalities_all_of_size k) ++
      map MBox (modalities_all_of_size k) ++
      map MDia (modalities_all_of_size k)
  end.

Lemma modalities_all_of_size_zero :
  modalities_all_of_size 0 = [MEmpty].
Proof. reflexivity. Qed.

Lemma modalities_all_of_size_iff :
  forall n m,
    In m (modalities_all_of_size n) <-> modality_size m = n.
Proof.
  induction n as [|n IH]; intro m; simpl.
  - split.
    + intros [H | H]; [subst m; reflexivity | contradiction].
    + intro H. apply modality_size_zero_iff in H. now subst m; left.
  - repeat rewrite in_app_iff. repeat rewrite in_map_iff.
    split.
    + intros [[x [Heq Hx]] | [[x [Heq Hx]] | [x [Heq Hx]]]];
        subst m; simpl; apply IH in Hx; lia.
    + intro Hsize. destruct m as [|m|m|m]; simpl in Hsize; try lia.
      * right; left. exists m. split; [reflexivity | apply IH; lia].
      * right; right. exists m. split; [reflexivity | apply IH; lia].
      * left. exists m. split; [reflexivity | apply IH; lia].
Qed.

Corollary modality_in_all_of_its_size :
  forall m, In m (modalities_all_of_size (modality_size m)).
Proof. intro m; apply modalities_all_of_size_iff; reflexivity. Qed.

Corollary modalities_all_of_size_zero_iff :
  forall m, In m (modalities_all_of_size 0) <-> m = MEmpty.
Proof. intro m; rewrite modalities_all_of_size_iff, modality_size_zero_iff; tauto. Qed.

Lemma modalities_all_of_size_split_left_one :
  forall n m,
    In m (modalities_all_of_size (S n)) ->
    exists m1 m2,
      In m1 (modalities_all_of_size 1) /\
      In m2 (modalities_all_of_size n) /\
      m = modality_add m1 m2.
Proof.
  intros n m H. apply modalities_all_of_size_iff in H.
  destruct (modality_split_left_one H) as [m1 [m2 [H1 [H2 Hadd]]]].
  exists m1, m2. repeat split; try apply modalities_all_of_size_iff; assumption.
Qed.

Lemma modalities_all_of_size_split_right_one :
  forall n m,
    In m (modalities_all_of_size (S n)) ->
    exists m1 m2,
      In m1 (modalities_all_of_size n) /\
      In m2 (modalities_all_of_size 1) /\
      m = modality_add m1 m2.
Proof.
  intros n m H. apply modalities_all_of_size_iff in H.
  destruct (modality_split_right_one H) as [m1 [m2 [H1 [H2 Hadd]]]].
  exists m1, m2. repeat split; try apply modalities_all_of_size_iff; assumption.
Qed.

Fixpoint modalities_all_of_size_le (n : nat) : modalities :=
  match n with
  | 0 => modalities_all_of_size 0
  | S k => modalities_all_of_size_le k ++ modalities_all_of_size (S k)
  end.

Lemma modalities_all_of_size_le_iff :
  forall n m,
    In m (modalities_all_of_size_le n) <-> modality_size m <= n.
Proof.
  induction n as [|n IH]; intro m.
  - change (In m (modalities_all_of_size 0) <-> modality_size m <= 0).
    rewrite modalities_all_of_size_iff. lia.
  - change
      (In m (modalities_all_of_size_le n ++ modalities_all_of_size (S n))
       <-> modality_size m <= S n).
    rewrite in_app_iff, IH, modalities_all_of_size_iff. lia.
Qed.

Corollary modalities_all_of_size_le_zero_iff :
  forall m, In m (modalities_all_of_size_le 0) <-> m = MEmpty.
Proof.
  intro m; rewrite modalities_all_of_size_le_iff; split.
  - intro H. apply modality_size_zero_iff. lia.
  - intro H. apply modality_size_zero_iff in H. lia.
Qed.

Lemma modalities_all_of_size_le_empty :
  forall n, In MEmpty (modalities_all_of_size_le n).
Proof. intro n; apply modalities_all_of_size_le_iff; simpl; lia. Qed.

Lemma modalities_all_of_size_le_monotone :
  forall n1 n2,
    n1 <= n2 ->
    incl (modalities_all_of_size_le n1) (modalities_all_of_size_le n2).
Proof.
  intros n1 n2 Hle m Hm.
  apply modalities_all_of_size_le_iff.
  apply modalities_all_of_size_le_iff in Hm. lia.
Qed.

Lemma modalities_all_of_size_le_split_left_one :
  forall n m,
    In m (modalities_all_of_size_le (S n)) ->
    exists m1 m2,
      In m1 (modalities_all_of_size_le 1) /\
      In m2 (modalities_all_of_size_le n) /\
      m = modality_add m1 m2.
Proof.
  intros n m H. apply modalities_all_of_size_le_iff in H.
  destruct (modality_split_left_le_one H)
    as [m1 [m2 [H1 [H2 Hadd]]]].
  exists m1, m2. repeat split; try apply modalities_all_of_size_le_iff; assumption.
Qed.

Lemma modalities_all_of_size_le_split_right_one :
  forall n m,
    In m (modalities_all_of_size_le (S n)) ->
    exists m1 m2,
      In m1 (modalities_all_of_size_le n) /\
      In m2 (modalities_all_of_size_le 1) /\
      m = modality_add m1 m2.
Proof.
  intros n m H. apply modalities_all_of_size_le_iff in H.
  destruct (modality_split_right_le_one H)
    as [m1 [m2 [H1 [H2 Hadd]]]].
  exists m1, m2. repeat split; try apply modalities_all_of_size_le_iff; assumption.
Qed.

Fixpoint positive_modalities_of_size (n : nat) : modalities :=
  match n with
  | 0 => [MEmpty]
  | S k =>
      map MBox (positive_modalities_of_size k) ++
      map MDia (positive_modalities_of_size k)
  end.

(** * Generic finite modal reduction *)

Definition modal_reduction
    (Ax : modal_axiom_schema) (n : nat) (M : modalities) : Prop :=
  forall m, modality_size m = n ->
    exists m', In m' M /\ modality_translation Ax m m'.

Definition modal_reduction_le
    (Ax : modal_axiom_schema) (n : nat) (M : modalities) : Prop :=
  forall m, modality_size m <= n ->
    exists m', In m' M /\ modality_translation Ax m m'.

Lemma modal_reduction_of_all_of_size :
  forall Ax n M,
    (forall m, In m (modalities_all_of_size n) ->
      exists m', In m' M /\ modality_translation Ax m m') ->
    modal_reduction Ax n M.
Proof.
  intros Ax n M H m Hsize. apply H.
  now apply modalities_all_of_size_iff.
Qed.

Lemma modal_reduction_le_of_all_of_size_le :
  forall Ax n M,
    (forall m, In m (modalities_all_of_size_le n) ->
      exists m', In m' M /\ modality_translation Ax m m') ->
    modal_reduction_le Ax n M.
Proof.
  intros Ax n M H m Hsize. apply H.
  now apply modalities_all_of_size_le_iff.
Qed.

Lemma modal_reduction_le_of_cumulative :
  forall Ax n M,
    (forall k, k <= n -> modal_reduction Ax k M) ->
    modal_reduction_le Ax n M.
Proof.
  intros Ax n M H m Hsize. apply (H (modality_size m) Hsize m). reflexivity.
Qed.

Lemma modal_reduction_le_weaken :
  forall Ax n n' M,
    n' <= n -> modal_reduction_le Ax n M -> modal_reduction_le Ax n' M.
Proof. intros Ax n n' M Hle H m Hm; apply H; lia. Qed.

Lemma modal_reduction_of_le :
  forall Ax n M,
    modal_reduction_le Ax n M -> modal_reduction Ax n M.
Proof. intros Ax n M H m Hm; apply H; lia. Qed.

Lemma modal_reduction_zero_of_mem :
  forall Ax M,
    In MEmpty M -> modal_reduction Ax 0 M.
Proof.
  intros Ax M Hmem m Hsize. apply modality_size_zero_iff in Hsize.
  subst m. exists MEmpty. split; [exact Hmem | apply modality_translation_refl].
Qed.

Lemma modal_reduction_one_of_mem :
  forall Ax M,
    In (MNeg MEmpty) M ->
    In (MBox MEmpty) M ->
    In (MDia MEmpty) M ->
    modal_reduction Ax 1 M.
Proof.
  intros Ax M Hneg Hbox Hdia m Hsize.
  apply modality_size_one_iff in Hsize.
  destruct Hsize as [-> | [-> | ->]].
  - exists (MBox MEmpty). split; [exact Hbox | apply modality_translation_refl].
  - exists (MDia MEmpty). split; [exact Hdia | apply modality_translation_refl].
  - exists (MNeg MEmpty). split; [exact Hneg | apply modality_translation_refl].
Qed.

Lemma modal_reduction_succ_max_of :
  forall Ax M,
    (exists x, In x M) ->
    modal_reduction_le Ax (S (modalities_max_size M)) M ->
    forall n,
      modal_reduction_le Ax (n + modalities_max_size M + 2) M.
Proof.
  intros Ax M Hnonempty Hbase n.
  induction n as [|n IH]; intros m Hm.
  - destruct (@modality_split_le (S (modalities_max_size M)) m 1)
      as [m1 [m2 [H1 [H2 ->]]]]; [lia |].
    destruct (Hbase m1 H1) as [m3 [Hm3 H13]].
    assert (H3 : modality_size m3 <= modalities_max_size M).
    { now apply modality_size_le_max_of_mem. }
    destruct (Hbase (modality_add m3 m2)) as [m4 [Hm4 H34]].
    { rewrite modality_add_size. lia. }
    exists m4. split; [exact Hm4 |].
    eapply modality_translation_trans.
    + apply modality_translation_expand_right. exact H13.
    + exact H34.
  - destruct (@modality_split_le (n + modalities_max_size M + 2) m 1)
      as [m1 [m2 [H1 [H2 ->]]]]; [lia |].
    destruct (IH m1) as [m3 [Hm3 H13]]; [lia |].
    assert (H3 : modality_size m3 <= modalities_max_size M).
    { now apply modality_size_le_max_of_mem. }
    destruct (Hbase (modality_add m3 m2)) as [m4 [Hm4 H34]].
    { rewrite modality_add_size. lia. }
    exists m4. split; [exact Hm4 |].
    eapply modality_translation_trans.
    + apply modality_translation_expand_right. exact H13.
    + exact H34.
Qed.

Lemma modal_reduction_le_all_of_base :
  forall Ax M,
    (exists x, In x M) ->
    modal_reduction_le Ax (S (modalities_max_size M)) M ->
    forall n, modal_reduction_le Ax n M.
Proof.
  intros Ax M Hnonempty Hbase n.
  destruct (le_dec n (S (modalities_max_size M))) as [Hsmall | Hlarge].
  - eapply modal_reduction_le_weaken; eauto.
  - eapply modal_reduction_le_weaken.
    + instantiate (1 := n + modalities_max_size M + 2). lia.
    + now apply modal_reduction_succ_max_of.
Qed.

Corollary modal_reduction_all_of_base :
  forall Ax M,
    (exists x, In x M) ->
    modal_reduction_le Ax (S (modalities_max_size M)) M ->
    forall n, modal_reduction Ax n M.
Proof.
  intros Ax M Hnonempty Hbase n.
  apply modal_reduction_of_le.
  now apply modal_reduction_le_all_of_base.
Qed.

Theorem modal_reduction_all_of_reducible_to_max :
  forall Ax M,
    (exists x, In x M) ->
    (forall n, n <= S (modalities_max_size M) ->
      modal_reduction Ax n M) ->
    forall n, modal_reduction Ax n M.
Proof.
  intros Ax M Hnonempty Hsmall.
  apply modal_reduction_all_of_base; [exact Hnonempty |].
  apply modal_reduction_le_of_cumulative. exact Hsmall.
Qed.

(** * Translations supplied by the standard modal axioms *)

Lemma modality_translation_T :
  forall Ax,
    (forall p : formula nat, normal_proves Ax (T p)) ->
    forall m, modality_translation Ax (MBox m) m.
Proof. intros Ax HT m p; apply HT. Qed.

Lemma modality_translation_Four :
  forall Ax,
    (forall p : formula nat, normal_proves Ax (Four p)) ->
    forall m, modality_translation Ax (MBox m) (MBox (MBox m)).
Proof. intros Ax HFour m p; apply HFour. Qed.

Lemma modality_translation_Tc :
  forall Ax,
    (forall p : formula nat, normal_proves Ax (Tc p)) ->
    forall m, modality_translation Ax m (MBox m).
Proof. intros Ax HTc m p; apply HTc. Qed.

Lemma modality_translation_B :
  forall Ax,
    (forall p : formula nat, normal_proves Ax (B p)) ->
    forall m, modality_translation Ax m (MBox (MDia m)).
Proof. intros Ax HB m p; apply HB. Qed.

Lemma modality_translation_D :
  forall Ax,
    (forall p : formula nat, normal_proves Ax (D p)) ->
    forall m, modality_translation Ax (MBox m) (MDia m).
Proof. intros Ax HD m p; apply HD. Qed.

Lemma modality_translation_Five :
  forall Ax,
    (forall p : formula nat, normal_proves Ax (Five p)) ->
    forall m, modality_translation Ax (MDia m) (MBox (MDia m)).
Proof. intros Ax HFive m p; apply HFive. Qed.

Corollary schema_T_modality_translation :
  forall m, modality_translation schema_T (MBox m) m.
Proof.
  apply modality_translation_T. intro p. apply Np_extra.
  exists p. reflexivity.
Qed.

Corollary schema_Four_modality_translation :
  forall m,
    modality_translation schema_Four (MBox m) (MBox (MBox m)).
Proof.
  apply modality_translation_Four. intro p. apply Np_extra.
  exists p. reflexivity.
Qed.

Corollary schema_B_modality_translation :
  forall m, modality_translation schema_B m (MBox (MDia m)).
Proof.
  apply modality_translation_B. intro p. apply Np_extra.
  exists p. reflexivity.
Qed.

Corollary schema_D_modality_translation :
  forall m, modality_translation schema_D (MBox m) (MDia m).
Proof.
  apply modality_translation_D. intro p. apply Np_extra.
  exists p. reflexivity.
Qed.

Corollary schema_Five_modality_translation :
  forall m,
    modality_translation schema_Five (MDia m) (MBox (MDia m)).
Proof.
  apply modality_translation_Five. intro p. apply Np_extra.
  exists p. reflexivity.
Qed.

Corollary S4_box_modality_translation :
  forall m, modality_translation S4_schema (MBox m) m.
Proof.
  apply modality_translation_T. intro p. apply Np_extra.
  left. exists p. reflexivity.
Qed.

Corollary S5_box_modality_translation :
  forall m, modality_translation S5_schema (MBox m) m.
Proof.
  apply modality_translation_T. intro p. apply Np_extra.
  left. exists p. reflexivity.
Qed.

(** The tiny T + Tc presentation used by Foundation's [Modal.Triv].  Names
    are file-prefixed because the broader port may also expose a global
    [schema_Tc] alongside the other named systems. *)
Definition modality_schema_Tc : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Tc q.

Definition modality_Triv_schema : modal_axiom_schema :=
  schema_union schema_T modality_schema_Tc.

Lemma modality_schema_Tc_substitution_closed :
  schema_substitution_closed modality_schema_Tc.
Proof.
  intros A B sigma p [q ->]. exists (substitute sigma q). reflexivity.
Qed.

Corollary Triv_box_modality_equivalence :
  forall m,
    modality_equivalence modality_Triv_schema (MBox m) m.
Proof.
  intro m. apply modality_equivalence_iff_bitranslation. split.
  - apply modality_translation_T. intro p. apply Np_extra.
    left. exists p. reflexivity.
  - apply modality_translation_Tc. intro p. apply Np_extra.
    right. exists p. reflexivity.
Qed.

(** * Canonical completeness for S5 = K + T + Five *)

(** Five at [~p] entails the form [~box p -> box ~box p] used by
    the Euclidean canonical-frame argument. *)
Lemma K_proves_Five_neg_box_bridge :
  forall p : formula nat,
    K_proves
      (Imp (Five (Neg p))
        (Imp (Neg (Box p)) (Box (Neg (Box p))))).
Proof.
  intro p. apply K_complete. intros F V w Hfive Hnotbox y Rwy Hboxp.
  assert (Hdia : satisfies F V w (Dia (Neg p))).
  {
    apply satisfies_dia_intro.
    apply NNPP. intro Hnone. apply Hnotbox.
    intros z Rwz. apply NNPP. intro Hnotp.
    apply Hnone. exists z; split; [exact Rwz |].
    apply (proj2 (@satisfies_neg nat F V z p)). exact Hnotp.
  }
  assert (Hboxdia : satisfies F V w (Box (Dia (Neg p)))).
  { exact (Hfive Hdia). }
  pose proof (Hboxdia y Rwy) as Hdiay.
  destruct (@satisfies_dia_elim nat F V y (Neg p) Hdiay)
    as [z [Ryz Hnegp]].
  apply (proj1 (@satisfies_neg nat F V z p) Hnegp).
  exact (Hboxp z Ryz).
Qed.

Lemma S5_proves_neg_box_five :
  forall p : formula nat,
    S5_proves (Imp (Neg (Box p)) (Box (Neg (Box p)))).
Proof.
  intro p. eapply Np_mp.
  - apply K_proves_normal. apply K_proves_Five_neg_box_bridge.
  - apply Np_extra. right. exists (Neg p). reflexivity.
Qed.

Definition frame_s5 (F : frame) : Prop :=
  frame_reflexive F /\ frame_right_euclidean F.

Lemma S5_canonical_frame_reflexive :
  frame_reflexive (normal_canonical_frame S5_schema).
Proof.
  intros M p Hbox. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. left. exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma S5_canonical_frame_right_euclidean :
  frame_right_euclidean (normal_canonical_frame S5_schema).
Proof.
  intros M N O HMN HMO p HboxN.
  destruct (classic (normal_mct_mem M (Box p))) as [HboxM | HnotboxM].
  - exact (HMO p HboxM).
  - assert (HnegboxM : normal_mct_mem M (Neg (Box p))).
    { apply (proj2 (@normal_mct_neg_iff S5_schema M (Box p))). exact HnotboxM. }
    assert (HboxnegboxM : normal_mct_mem M (Box (Neg (Box p)))).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem. apply S5_proves_neg_box_five.
      - apply ND_assumption. exact HnegboxM.
    }
    pose proof (HMN (Neg (Box p)) HboxnegboxM) as HnegboxN.
    exfalso. exact (@normal_mct_not_both S5_schema N (Box p)
      HboxN HnegboxN).
Qed.

Theorem S5_complete :
  forall p : formula nat,
    normal_valid_on_class frame_s5 p -> S5_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := S5_schema) (C := frame_s5)).
  - exact (@S5_is_consistent nat).
  - split.
    + exact S5_canonical_frame_reflexive.
    + exact S5_canonical_frame_right_euclidean.
Qed.

Theorem S5_sound_complete :
  forall p : formula nat,
    S5_proves p <-> normal_valid_on_class frame_s5 p.
Proof.
  intro p; split.
  - intros Hp F [HR HE].
    now apply S5_proves_sound_on_reflexive_euclidean_frame.
  - apply S5_complete.
Qed.

(** * Six S5 normal forms *)

Definition s5_modalities : modalities :=
  [ MEmpty;
    MNeg MEmpty;
    MBox MEmpty;
    MDia MEmpty;
    MNeg (MBox MEmpty);
    MNeg (MDia MEmpty) ].

Definition s5_neg_normal_form (m : modality) : modality :=
  match m with
  | MEmpty => MNeg MEmpty
  | MNeg MEmpty => MEmpty
  | MBox MEmpty => MNeg (MBox MEmpty)
  | MDia MEmpty => MNeg (MDia MEmpty)
  | MNeg (MBox MEmpty) => MBox MEmpty
  | MNeg (MDia MEmpty) => MDia MEmpty
  | _ => MNeg m
  end.

Definition s5_box_normal_form (m : modality) : modality :=
  match m with
  | MEmpty => MBox MEmpty
  | MNeg MEmpty => MNeg (MDia MEmpty)
  | MBox MEmpty => MBox MEmpty
  | MDia MEmpty => MDia MEmpty
  | MNeg (MBox MEmpty) => MNeg (MBox MEmpty)
  | MNeg (MDia MEmpty) => MNeg (MDia MEmpty)
  | _ => MBox m
  end.

Definition s5_dia_normal_form (m : modality) : modality :=
  match m with
  | MEmpty => MDia MEmpty
  | MNeg MEmpty => MNeg (MBox MEmpty)
  | MBox MEmpty => MBox MEmpty
  | MDia MEmpty => MDia MEmpty
  | MNeg (MBox MEmpty) => MNeg (MBox MEmpty)
  | MNeg (MDia MEmpty) => MNeg (MDia MEmpty)
  | _ => MDia m
  end.

Fixpoint s5_normalize (m : modality) : modality :=
  match m with
  | MEmpty => MEmpty
  | MBox k => s5_box_normal_form (s5_normalize k)
  | MDia k => s5_dia_normal_form (s5_normalize k)
  | MNeg k => s5_neg_normal_form (s5_normalize k)
  end.

Lemma s5_neg_normal_form_mem :
  forall m,
    In m s5_modalities -> In (s5_neg_normal_form m) s5_modalities.
Proof.
  intros m H. simpl in H |- *.
  repeat (destruct H as [H | H]; [subst m; simpl; tauto |]).
  contradiction.
Qed.

Lemma s5_box_normal_form_mem :
  forall m,
    In m s5_modalities -> In (s5_box_normal_form m) s5_modalities.
Proof.
  intros m H. simpl in H |- *.
  repeat (destruct H as [H | H]; [subst m; simpl; tauto |]).
  contradiction.
Qed.

Lemma s5_dia_normal_form_mem :
  forall m,
    In m s5_modalities -> In (s5_dia_normal_form m) s5_modalities.
Proof.
  intros m H. simpl in H |- *.
  repeat (destruct H as [H | H]; [subst m; simpl; tauto |]).
  contradiction.
Qed.

Lemma s5_normalize_mem :
  forall m, In (s5_normalize m) s5_modalities.
Proof.
  induction m; simpl.
  - now left.
  - now apply s5_box_normal_form_mem.
  - now apply s5_dia_normal_form_mem.
  - now apply s5_neg_normal_form_mem.
Qed.

Lemma frame_s5_symmetric :
  forall F, frame_s5 F -> frame_symmetric F.
Proof.
  intros F [HR HE] x y Rxy.
  exact (HE x y x Rxy (HR x)).
Qed.

Lemma frame_s5_transitive :
  forall F, frame_s5 F -> frame_transitive F.
Proof.
  intros F HF x y z Rxy Ryz.
  pose proof (@frame_s5_symmetric F HF x y Rxy) as Ryx.
  exact ((proj2 HF) y x z Ryx Ryz).
Qed.

Lemma s5_box_truth_invariant :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (p : formula AtomType) x y,
    frame_s5 F -> Rel F x y ->
    (satisfies F V x (Box p) <-> satisfies F V y (Box p)).
Proof.
  intros AtomType F V p x y HF Rxy; split; intros Hbox z R.
  - apply Hbox. exact (@frame_s5_transitive F HF x y z Rxy R).
  - apply Hbox. exact ((proj2 HF) x y z Rxy R).
Qed.

Lemma s5_dia_truth_invariant :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (p : formula AtomType) x y,
    frame_s5 F -> Rel F x y ->
    (satisfies F V x (Dia p) <-> satisfies F V y (Dia p)).
Proof.
  intros AtomType F V p x y HF Rxy; split; intro Hdia.
  - destruct (@satisfies_dia_elim AtomType F V x p Hdia)
      as [z [Rxz Hp]].
    apply satisfies_dia_intro. exists z; split; [|exact Hp].
    exact ((proj2 HF) x y z Rxy Rxz).
  - destruct (@satisfies_dia_elim AtomType F V y p Hdia)
      as [z [Ryz Hp]].
    apply satisfies_dia_intro. exists z; split; [|exact Hp].
    exact (@frame_s5_transitive F HF x y z Rxy Ryz).
Qed.

Definition s5_stable_modality (m : modality) : Prop :=
  m = MBox MEmpty \/
  m = MDia MEmpty \/
  m = MNeg (MBox MEmpty) \/
  m = MNeg (MDia MEmpty).

Lemma s5_stable_truth_invariant :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p : formula AtomType) x y,
    frame_s5 F -> Rel F x y -> s5_stable_modality m ->
    (satisfies F V x (apply_modality m p) <->
     satisfies F V y (apply_modality m p)).
Proof.
  intros AtomType F V m p x y HF Rxy
    [-> | [-> | [-> | ->]]]; simpl.
  - now apply s5_box_truth_invariant.
  - now apply s5_dia_truth_invariant.
  - pose proof
      (@s5_box_truth_invariant AtomType F V p x y HF Rxy). tauto.
  - pose proof
      (@s5_dia_truth_invariant AtomType F V p x y HF Rxy). tauto.
Qed.

Lemma s5_box_stable_iff :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p : formula AtomType) w,
    frame_s5 F -> s5_stable_modality m ->
    (satisfies F V w (Box (apply_modality m p)) <->
     satisfies F V w (apply_modality m p)).
Proof.
  intros AtomType F V m p w HF Hstable; split.
  - intro Hbox. exact (Hbox w ((proj1 HF) w)).
  - intros Hp y Rwy.
    apply (proj1 (@s5_stable_truth_invariant AtomType F V m p w y
      HF Rwy Hstable)). exact Hp.
Qed.

Lemma s5_dia_stable_iff :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p : formula AtomType) w,
    frame_s5 F -> s5_stable_modality m ->
    (satisfies F V w (Dia (apply_modality m p)) <->
     satisfies F V w (apply_modality m p)).
Proof.
  intros AtomType F V m p w HF Hstable; split.
  - intro Hdia. destruct (satisfies_dia_elim Hdia) as [y [Rwy Hy]].
    apply (proj2 (@s5_stable_truth_invariant AtomType F V m p w y
      HF Rwy Hstable)). exact Hy.
  - intro Hp. apply satisfies_dia_intro. exists w; split.
    + exact ((proj1 HF) w).
    + exact Hp.
Qed.

Lemma s5_neg_normal_form_truth :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p : formula AtomType) w,
    In m s5_modalities ->
    (satisfies F V w (Neg (apply_modality m p)) <->
     satisfies F V w (apply_modality (s5_neg_normal_form m) p)).
Proof.
  intros AtomType F V m p w H. simpl in H.
  repeat (destruct H as [H | H]; [subst m; simpl; tauto |]).
  contradiction.
Qed.

Lemma s5_box_normal_form_truth :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p : formula AtomType) w,
    frame_s5 F -> In m s5_modalities ->
    (satisfies F V w (Box (apply_modality m p)) <->
     satisfies F V w (apply_modality (s5_box_normal_form m) p)).
Proof.
  intros AtomType F V m p w HF H. simpl in H.
  destruct H as [H | H]; [subst m; reflexivity |].
  destruct H as [H | H].
  - subst m. simpl. tauto.
  - destruct H as [H | H]; [subst m |].
    + simpl. apply (@s5_box_stable_iff AtomType F V
        (MBox MEmpty) p w); [exact HF | now left].
    + destruct H as [H | H]; [subst m |].
      * simpl. apply (@s5_box_stable_iff AtomType F V
          (MDia MEmpty) p w); [exact HF | now right; left].
      * destruct H as [H | H]; [subst m |].
        (** Negated box is constant on an S5 cluster, just as box is. *)
        ** simpl. apply (@s5_box_stable_iff AtomType F V
            (MNeg (MBox MEmpty)) p w);
            [exact HF | now right; right; left].
        ** destruct H as [H | H]; [subst m | contradiction].
           simpl. apply (@s5_box_stable_iff AtomType F V
             (MNeg (MDia MEmpty)) p w);
             [exact HF | now right; right; right].
Qed.

Lemma s5_dia_neg_iff_neg_box :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (p : formula AtomType) w,
    (satisfies F V w (Dia (Neg p)) <->
     satisfies F V w (Neg (Box p))).
Proof.
  intros AtomType F V p w.
  rewrite (@satisfies_dia AtomType F V w (Neg p)).
  split.
  - intros [y [Rwy Hnp]].
    apply (proj2 (@satisfies_neg AtomType F V w (Box p))).
    intro Hbox. apply (proj1 (@satisfies_neg AtomType F V y p) Hnp).
    exact (Hbox y Rwy).
  - intro Hnegbox.
    pose proof (proj1 (@satisfies_neg AtomType F V w (Box p)) Hnegbox)
      as Hnotbox.
    apply NNPP. intro Hnone. apply Hnotbox. intros y Rwy.
    apply NNPP. intro Hnotp. apply Hnone. exists y; split; [exact Rwy |].
    apply (proj2 (@satisfies_neg AtomType F V y p)). exact Hnotp.
Qed.

Lemma s5_dia_normal_form_truth :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p : formula AtomType) w,
    frame_s5 F -> In m s5_modalities ->
    (satisfies F V w (Dia (apply_modality m p)) <->
     satisfies F V w (apply_modality (s5_dia_normal_form m) p)).
Proof.
  intros AtomType F V m p w HF H. simpl in H.
  destruct H as [H | H]; [subst m; reflexivity |].
  destruct H as [H | H].
  - subst m. simpl. apply s5_dia_neg_iff_neg_box.
  - destruct H as [H | H]; [subst m |].
    + simpl. apply (@s5_dia_stable_iff AtomType F V
        (MBox MEmpty) p w); [exact HF | now left].
    + destruct H as [H | H]; [subst m |].
      * simpl. apply (@s5_dia_stable_iff AtomType F V
          (MDia MEmpty) p w); [exact HF | now right; left].
      * destruct H as [H | H]; [subst m |].
        ** simpl. apply (@s5_dia_stable_iff AtomType F V
            (MNeg (MBox MEmpty)) p w);
            [exact HF | now right; right; left].
        ** destruct H as [H | H]; [subst m | contradiction].
           simpl. apply (@s5_dia_stable_iff AtomType F V
             (MNeg (MDia MEmpty)) p w);
             [exact HF | now right; right; right].
Qed.

Lemma apply_modality_truth_congruence :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p q : formula AtomType),
    (forall w, satisfies F V w p <-> satisfies F V w q) ->
    forall w,
      satisfies F V w (apply_modality m p) <->
      satisfies F V w (apply_modality m q).
Proof.
  intros AtomType F V m; induction m; intros p q Heq w; simpl.
  - apply Heq.
  - split; intros H y Rwy.
    + apply (proj1 (IHm p q Heq y)). exact (H y Rwy).
    + apply (proj2 (IHm p q Heq y)). exact (H y Rwy).
  - unfold Dia, Neg; simpl. split; intros Hnot Hbox; apply Hnot;
      intros y Rwy Hp.
    + apply (Hbox y Rwy). apply (proj1 (IHm p q Heq y)). exact Hp.
    + apply (Hbox y Rwy). apply (proj2 (IHm p q Heq y)). exact Hp.
  - pose proof (IHm p q Heq w). tauto.
Qed.

Theorem s5_normalize_truth :
  forall AtomType (F : frame) (V : valuation AtomType F)
         m (p : formula AtomType) w,
    frame_s5 F ->
    (satisfies F V w (apply_modality m p) <->
     satisfies F V w (apply_modality (s5_normalize m) p)).
Proof.
  intros AtomType F V m; induction m; intros p w HF; simpl.
  - reflexivity.
  - eapply iff_trans.
    + apply (@apply_modality_truth_congruence AtomType F V
        (MBox MEmpty) (apply_modality m p)
        (apply_modality (s5_normalize m) p)).
      intro y. apply IHm. exact HF.
    + apply (@s5_box_normal_form_truth AtomType F V
        (s5_normalize m) p w HF). apply s5_normalize_mem.
  - eapply iff_trans.
    + apply (@apply_modality_truth_congruence AtomType F V
        (MDia MEmpty) (apply_modality m p)
        (apply_modality (s5_normalize m) p)).
      intro y. apply IHm. exact HF.
    + apply (@s5_dia_normal_form_truth AtomType F V
        (s5_normalize m) p w HF). apply s5_normalize_mem.
  - eapply iff_trans.
    + apply (@apply_modality_truth_congruence AtomType F V
        (MNeg MEmpty) (apply_modality m p)
        (apply_modality (s5_normalize m) p)).
      intro y. apply IHm. exact HF.
    + apply (@s5_neg_normal_form_truth AtomType F V
        (s5_normalize m) p w). apply s5_normalize_mem.
Qed.

Theorem s5_normalize_equivalence :
  forall m, modality_equivalence S5_schema m (s5_normalize m).
Proof.
  intros m p. apply S5_complete. intros F HF V w.
  rewrite satisfies_iff. apply s5_normalize_truth. exact HF.
Qed.

Corollary s5_box_box_equivalence :
  modality_equivalence S5_schema
    (MBox (MBox MEmpty)) (MBox MEmpty).
Proof.
  change (modality_equivalence S5_schema (MBox (MBox MEmpty))
    (s5_normalize (MBox (MBox MEmpty)))).
  apply s5_normalize_equivalence.
Qed.

Corollary s5_box_dia_equivalence :
  modality_equivalence S5_schema
    (MBox (MDia MEmpty)) (MDia MEmpty).
Proof.
  change (modality_equivalence S5_schema (MBox (MDia MEmpty))
    (s5_normalize (MBox (MDia MEmpty)))).
  apply s5_normalize_equivalence.
Qed.

Corollary s5_dia_dia_equivalence :
  modality_equivalence S5_schema
    (MDia (MDia MEmpty)) (MDia MEmpty).
Proof.
  change (modality_equivalence S5_schema (MDia (MDia MEmpty))
    (s5_normalize (MDia (MDia MEmpty)))).
  apply s5_normalize_equivalence.
Qed.

Corollary s5_dia_box_equivalence :
  modality_equivalence S5_schema
    (MDia (MBox MEmpty)) (MBox MEmpty).
Proof.
  change (modality_equivalence S5_schema (MDia (MBox MEmpty))
    (s5_normalize (MDia (MBox MEmpty)))).
  apply s5_normalize_equivalence.
Qed.

Corollary s5_normalize_translation :
  forall m, modality_translation S5_schema m (s5_normalize m).
Proof.
  intro m.
  apply (proj1 (modality_equivalence_iff_bitranslation
    S5_schema m (s5_normalize m))).
  apply s5_normalize_equivalence.
Qed.

Theorem s5_modal_reduction :
  forall n, modal_reduction S5_schema n s5_modalities.
Proof.
  intros n m Hsize. exists (s5_normalize m). split.
  - apply s5_normalize_mem.
  - apply s5_normalize_translation.
Qed.

Corollary s5_modal_reduction_zero :
  modal_reduction S5_schema 0 s5_modalities.
Proof. apply s5_modal_reduction. Qed.

Corollary s5_modal_reduction_one :
  modal_reduction S5_schema 1 s5_modalities.
Proof. apply s5_modal_reduction. Qed.

Corollary s5_modal_reduction_two :
  modal_reduction S5_schema 2 s5_modalities.
Proof. apply s5_modal_reduction. Qed.

Corollary s5_modal_reduction_three :
  modal_reduction S5_schema 3 s5_modalities.
Proof. apply s5_modal_reduction. Qed.
