(**
  Formula padding by a recognizable conjunction of truths.

  This ports [Foundation/FirstOrder/Basic/Padding.lean].  The syntactic
  decoder, injectivity, rewrite compatibility, and minimal-entailment
  equivalence are constructive and need no decidable formula equality.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericSemantics GenericEntailment PropositionalEntailmentMinimal.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.Syntax.Predicate Require Import Language Rew.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The conjunction of [k] copies of truth, with truth as the empty
    conjunction. *)
Fixpoint semiformula_repeated_verum {L X n} (k : nat) :
    semiformula L X n :=
  match k with
  | 0 => Semiformula_verum n
  | S k' => Semiformula_and (Semiformula_verum n)
      (semiformula_repeated_verum k')
  end.

Definition semiformula_padding {L X n}
    (p : semiformula L X n) (k : nat) : semiformula L X n :=
  Semiformula_and p (semiformula_repeated_verum k).

Fixpoint semiformula_get_padding_aux {L X n}
    (p : semiformula L X n) : option nat :=
  match p with
  | Semiformula_verum _ => Some 0
  | Semiformula_and p q =>
      match p with
      | Semiformula_verum _ =>
          option_map S (semiformula_get_padding_aux q)
      | _ => None
      end
  | _ => None
  end.

Definition semiformula_get_padding {L X n}
    (p : semiformula L X n) : option nat :=
  match p with
  | Semiformula_and _ q => semiformula_get_padding_aux q
  | _ => None
  end.

Definition semiformula_get_padding_formula {L X n}
    (p : semiformula L X n) : option (semiformula L X n) :=
  match p with
  | Semiformula_and q _ => Some q
  | _ => None
  end.

Lemma semiformula_get_padding_aux_repeated_verum : forall L X n k,
  @semiformula_get_padding_aux L X n
    (semiformula_repeated_verum k) = Some k.
Proof.
  intros L X n k. induction k as [|k IH]; simpl; [reflexivity |].
  now rewrite IH.
Qed.

Lemma semiformula_get_padding_padding : forall L X n
    (p : semiformula L X n) k,
  semiformula_get_padding (semiformula_padding p k) = Some k.
Proof.
  intros. unfold semiformula_get_padding, semiformula_padding.
  apply semiformula_get_padding_aux_repeated_verum.
Qed.

Lemma semiformula_get_padding_formula_padding : forall L X n
    (p : semiformula L X n) k,
  semiformula_get_padding_formula (semiformula_padding p k) = Some p.
Proof. reflexivity. Qed.

Lemma semiformula_padding_injective_iff : forall L X n
    (p q : semiformula L X n) k m,
  semiformula_padding p k = semiformula_padding q m <->
  p = q /\ k = m.
Proof.
  intros L X n p q k m. split.
  - intro H. split.
    + pose proof (f_equal semiformula_get_padding_formula H) as Hp.
      now rewrite semiformula_get_padding_formula_padding,
        semiformula_get_padding_formula_padding in Hp; inversion Hp.
    + pose proof (f_equal semiformula_get_padding H) as Hk.
      now rewrite semiformula_get_padding_padding,
        semiformula_get_padding_padding in Hk; inversion Hk.
  - intros [-> ->]. reflexivity.
Qed.

Lemma semiformula_rewrite_repeated_verum : forall L X n Y m
    (w : rew L X n Y m) k,
  semiformula_rewrite w (semiformula_repeated_verum k) =
  semiformula_repeated_verum k.
Proof.
  intros L X n Y m w k. induction k as [|k IH]; simpl;
    [reflexivity | now rewrite IH].
Qed.

Lemma semiformula_rewrite_padding : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X n) k,
  semiformula_rewrite w (semiformula_padding p k) =
  semiformula_padding (semiformula_rewrite w p) k.
Proof.
  intros. unfold semiformula_padding. simpl.
  now rewrite semiformula_rewrite_repeated_verum.
Qed.

(** A finite conjunction of truths is derivable in every minimal system. *)
Fixpoint semiformula_repeated_verum_raw
    {S : Type} {L : language} {X : Type} {n : nat}
    {E : generic_entailment S (semiformula L X n)} {s : S}
    (H : generic_minimal_entailment E
      (semiformula_connectives L X n) s) (k : nat) :
    generic_proof E s (semiformula_repeated_verum k).
Proof.
  destruct k as [|k].
  - exact (generic_minimal_verum H).
  - exact (generic_minimal_and_intro_raw H _ _
      (generic_minimal_verum H)
      (@semiformula_repeated_verum_raw S L X n E s H k)).
Defined.

Definition semiformula_padding_iff_raw
    {S : Type} {L : language} {X : Type} {n : nat}
    {E : generic_entailment S (semiformula L X n)} {s : S}
    (H : generic_minimal_entailment E
      (semiformula_connectives L X n) s)
    (p : semiformula L X n) (k : nat) :
    generic_proof E s
      (semiformula_iff (semiformula_padding p k) p).
Proof.
  apply (generic_minimal_iff_intro_raw H).
  - exact (generic_minimal_and1 H p (semiformula_repeated_verum k)).
  - apply (generic_minimal_right_and_intro_raw H).
    + exact (generic_minimal_identity_raw H p).
    + exact (generic_minimal_dhyp_raw H _ p
        (semiformula_repeated_verum_raw H k)).
Defined.

Lemma semiformula_padding_iff_provable : forall
    (S : Type) (L : language) (X : Type) (n : nat)
    (E : generic_entailment S (semiformula L X n)) (s : S),
  generic_minimal_entailment E (semiformula_connectives L X n) s ->
  forall (p : semiformula L X n) k,
    generic_provable E s
      (semiformula_iff (semiformula_padding p k) p).
Proof.
  intros S L X n E s H p k. constructor.
  exact (semiformula_padding_iff_raw H p k).
Qed.
