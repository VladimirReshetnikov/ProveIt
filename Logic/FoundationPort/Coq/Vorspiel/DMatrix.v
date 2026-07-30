(** Dependent finite vectors. *)

From Stdlib Require Import Logic.FunctionalExtensionality Vectors.Fin.
From Foundation.Vorspiel Require Import Fintype.
From Foundation.Vorspiel.Fin Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition dvec_empty {A : Fin.t 0 -> Type} : forall i, A i :=
  fun i => match i with end.

Definition dvec_cons {n} {A : Fin.t (S n) -> Type}
    (head : A Fin.F1) (tail : forall i : Fin.t n, A (Fin.FS i)) :
    forall i, A i :=
  fun i => @Fin.caseS' n i A head tail.

Lemma dvec_cons_zero : forall n (A : Fin.t (S n) -> Type)
    (head : A Fin.F1) tail,
  dvec_cons head tail Fin.F1 = head.
Proof. reflexivity. Qed.

Lemma dvec_cons_succ : forall n (A : Fin.t (S n) -> Type)
    (head : A Fin.F1) tail (i : Fin.t n),
  dvec_cons head tail (Fin.FS i) = tail i.
Proof. reflexivity. Qed.

Theorem dvec_eta : forall n (A : Fin.t (S n) -> Type)
    (v : forall i, A i),
  v = dvec_cons (v Fin.F1) (fun i => v (Fin.FS i)).
Proof.
  intros n A v. apply functional_extensionality_dep. intro i.
  refine (@Fin.caseS' n i
    (fun j => v j = dvec_cons (v Fin.F1) (fun k => v (Fin.FS k)) j)
    eq_refl _).
  intro j. reflexivity.
Qed.

Theorem dvec_cons_ext_iff : forall n (A : Fin.t (S n) -> Type)
    (a1 a2 : A Fin.F1)
    (s1 s2 : forall i : Fin.t n, A (Fin.FS i)),
  dvec_cons a1 s1 = dvec_cons a2 s2 <-> a1 = a2 /\ s1 = s2.
Proof.
  intros n A a1 a2 s1 s2. split.
  - intro H. split.
    + exact (f_equal (fun v => v Fin.F1) H).
    + apply functional_extensionality_dep. intro i.
      exact (f_equal (fun v => v (Fin.FS i)) H).
  - intros [-> ->]. reflexivity.
Qed.

Definition fin_cover_data (n : nat) : finite_cover_data (Fin.t n) :=
  {| finite_cover_list := vorspiel_fin_enum n;
     finite_cover_complete := @vorspiel_fin_enum_complete n |}.

Definition dvec_eq_dec {n} {A : Fin.t n -> Type}
    (v w : forall i, A i)
    (dec : forall i, {v i = w i} + {v i <> w i}) :
    {v = w} + {v <> w} :=
  @finite_cover_dependent_eq_dec (Fin.t n) (fin_cover_data n) A v w dec.
