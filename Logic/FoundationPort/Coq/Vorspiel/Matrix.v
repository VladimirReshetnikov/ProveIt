(** Homogeneous finite-vector algebra over [Fin.t]. *)

From Stdlib Require Import Arith.Cantor Lists.List
  Logic.FunctionalExtensionality Vectors.Fin.
From Foundation.Vorspiel Require Import DMatrix.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition matrix_vec_empty {A} : Fin.t 0 -> A :=
  fun i => match i with end.

Definition matrix_vec_cons {A n} (head : A) (tail : Fin.t n -> A) :
    Fin.t (S n) -> A :=
  dvec_cons head tail.

Definition matrix_vec_head {A n} (v : Fin.t (S n) -> A) : A := v Fin.F1.
Definition matrix_vec_tail {A n} (v : Fin.t (S n) -> A) : Fin.t n -> A :=
  fun i => v (Fin.FS i).

Lemma matrix_vec_cons_zero : forall A n (a : A) (v : Fin.t n -> A),
  matrix_vec_cons a v Fin.F1 = a.
Proof. reflexivity. Qed.

Lemma matrix_vec_cons_succ : forall A n (a : A) (v : Fin.t n -> A) i,
  matrix_vec_cons a v (Fin.FS i) = v i.
Proof. reflexivity. Qed.

Theorem matrix_vec_eta : forall A n (v : Fin.t (S n) -> A),
  matrix_vec_cons (matrix_vec_head v) (matrix_vec_tail v) = v.
Proof.
  intros A n v. symmetry. apply dvec_eta.
Qed.

Theorem matrix_vec_cons_ext_iff : forall A n (a b : A)
    (v w : Fin.t n -> A),
  matrix_vec_cons a v = matrix_vec_cons b w <-> a = b /\ v = w.
Proof. intros. apply dvec_cons_ext_iff. Qed.

Definition matrix_vec_eq_dec {A n} (v w : Fin.t n -> A)
    (dec : forall i, {v i = w i} + {v i <> w i}) :
    {v = w} + {v <> w} :=
  @dvec_eq_dec n (fun _ => A) v w dec.

Definition matrix_vec_map {A B n} (f : A -> B) (v : Fin.t n -> A) :
    Fin.t n -> B :=
  fun i => f (v i).

Lemma matrix_vec_map_cons : forall A B n (f : A -> B) a
    (v : Fin.t n -> A),
  matrix_vec_map f (matrix_vec_cons a v) =
  matrix_vec_cons (f a) (matrix_vec_map f v).
Proof.
  intros A B n f a v. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    matrix_vec_map f (matrix_vec_cons a v) j =
    matrix_vec_cons (f a) (matrix_vec_map f v) j) eq_refl _).
  intro j. reflexivity.
Qed.

Lemma matrix_vec_map_comp : forall A B C n (g : B -> C) (f : A -> B)
    (v : Fin.t n -> A),
  matrix_vec_map g (matrix_vec_map f v) =
  matrix_vec_map (fun x => g (f x)) v.
Proof. reflexivity. Qed.

Fixpoint matrix_vec_to_list {A} (n : nat) :
    (Fin.t n -> A) -> list A :=
  match n as k return (Fin.t k -> A) -> list A with
  | 0 => fun _ => nil
  | S k => fun v => matrix_vec_head v ::
      @matrix_vec_to_list A k (matrix_vec_tail v)
  end.

Lemma matrix_vec_to_list_zero : forall A (v : Fin.t 0 -> A),
  @matrix_vec_to_list A 0 v = nil.
Proof. reflexivity. Qed.

Lemma matrix_vec_to_list_succ : forall A n (v : Fin.t (S n) -> A),
  @matrix_vec_to_list A (S n) v =
  matrix_vec_head v :: @matrix_vec_to_list A n (matrix_vec_tail v).
Proof. reflexivity. Qed.

Lemma matrix_vec_to_list_length : forall A n (v : Fin.t n -> A),
  length (@matrix_vec_to_list A n v) = n.
Proof.
  intros A n. induction n as [|n IH]; intro v; simpl; [reflexivity |].
  now rewrite IH.
Qed.

Theorem matrix_vec_to_list_member_iff : forall A n
    (v : Fin.t n -> A) a,
  In a (@matrix_vec_to_list A n v) <-> exists i, v i = a.
Proof.
  intros A n. induction n as [|n IH]; intros v a; simpl.
  - split; [intro H; inversion H | intros [i _]; inversion i].
  - rewrite IH. split.
    + intros [Ha | [i Hi]].
      * exists Fin.F1. exact Ha.
      * exists (Fin.FS i). exact Hi.
    + intros [i Hi].
      refine (@Fin.caseS' n i
        (fun j => v j = a ->
          v Fin.F1 = a \/ exists k, v (Fin.FS k) = a) _ _ Hi).
      * now left.
      * intros j Hj. right. now exists j.
Qed.

Fixpoint matrix_vec_foldr {A B} (f : A -> B -> B) (init : B)
    (n : nat) : (Fin.t n -> A) -> B :=
  match n as k return (Fin.t k -> A) -> B with
  | 0 => fun _ => init
  | S k => fun v => f (matrix_vec_head v)
      (@matrix_vec_foldr A B f init k (matrix_vec_tail v))
  end.

Fixpoint matrix_vec_foldl {A B} (f : A -> B -> A) (init : A)
    (n : nat) : (Fin.t n -> B) -> A :=
  match n as k return (Fin.t k -> B) -> A with
  | 0 => fun _ => init
  | S k => fun v => @matrix_vec_foldl A B f
      (f init (matrix_vec_head v)) k (matrix_vec_tail v)
  end.

Lemma matrix_vec_foldr_zero : forall A B (f : A -> B -> B) init
    (v : Fin.t 0 -> A),
  @matrix_vec_foldr A B f init 0 v = init.
Proof. reflexivity. Qed.

Lemma matrix_vec_foldr_succ : forall A B (f : A -> B -> B) init n
    (v : Fin.t (S n) -> A),
  @matrix_vec_foldr A B f init (S n) v =
  f (matrix_vec_head v)
    (@matrix_vec_foldr A B f init n (matrix_vec_tail v)).
Proof. reflexivity. Qed.

Lemma matrix_vec_foldl_zero : forall A B (f : A -> B -> A) init
    (v : Fin.t 0 -> B),
  @matrix_vec_foldl A B f init 0 v = init.
Proof. reflexivity. Qed.

Lemma matrix_vec_foldl_succ : forall A B (f : A -> B -> A) init n
    (v : Fin.t (S n) -> B),
  @matrix_vec_foldl A B f init (S n) v =
  @matrix_vec_foldl A B f (f init (matrix_vec_head v)) n
    (matrix_vec_tail v).
Proof. reflexivity. Qed.

Theorem matrix_vec_forall_iff : forall A n
    (P : (Fin.t (S n) -> A) -> Prop),
  (forall v, P v) <->
  forall a (tail : Fin.t n -> A), P (matrix_vec_cons a tail).
Proof.
  intros A n P. split.
  - intros H a tail. apply H.
  - intros H v. rewrite <- (matrix_vec_eta v). apply H.
Qed.

Theorem matrix_vec_exists_iff : forall A n
    (P : (Fin.t (S n) -> A) -> Prop),
  (exists v, P v) <->
  exists a, exists tail : Fin.t n -> A, P (matrix_vec_cons a tail).
Proof.
  intros A n P. split.
  - intros [v Hv]. exists (matrix_vec_head v), (matrix_vec_tail v).
    now rewrite matrix_vec_eta.
  - intros [a [tail H]]. now exists (matrix_vec_cons a tail).
Qed.

Fixpoint matrix_vec_option_sequence {n} {A : Fin.t n -> Type} :
    (forall i, option (A i)) -> option (forall i, A i) :=
  match n as k return
    forall A : Fin.t k -> Type,
      (forall i, option (A i)) -> option (forall i, A i) with
  | 0 => fun A _ => Some (@dvec_empty A)
  | S k => fun A v =>
      match v Fin.F1,
        @matrix_vec_option_sequence k (fun i => A (Fin.FS i))
          (fun i => v (Fin.FS i)) with
      | Some head, Some tail => Some (dvec_cons head tail)
      | _, _ => None
      end
  end A.

Theorem matrix_vec_option_sequence_some : forall n
    (A : Fin.t n -> Type) (v : forall i, option (A i))
    (w : forall i, A i),
  (forall i, v i = Some (w i)) ->
  matrix_vec_option_sequence v = Some w.
Proof.
  induction n as [|n IH]; intros A v w H.
  - cbn [matrix_vec_option_sequence]. f_equal.
    apply functional_extensionality_dep. intro i. inversion i.
  - cbn [matrix_vec_option_sequence]. rewrite H.
    rewrite (IH (fun i => A (Fin.FS i)) (fun i => v (Fin.FS i))
      (fun i => w (Fin.FS i)) (fun i => H (Fin.FS i))).
    f_equal. symmetry. apply dvec_eta.
Qed.

Theorem matrix_vec_cons_injective : forall A n (f : Fin.t n -> A) a,
  (forall i j, f i = f j -> i = j) ->
  (forall i, a <> f i) ->
  forall i j,
    matrix_vec_cons a f i = matrix_vec_cons a f j -> i = j.
Proof.
  intros A n f a Hf Ha i.
  refine (@Fin.caseS' n i (fun i => forall j,
    matrix_vec_cons a f i = matrix_vec_cons a f j -> i = j) _ _).
  - intro j. refine (@Fin.caseS' n j (fun j =>
      matrix_vec_cons a f Fin.F1 = matrix_vec_cons a f j -> Fin.F1 = j)
      (fun _ => eq_refl) _).
    intros k H. exfalso. now apply (Ha k).
  - intros k j. refine (@Fin.caseS' n j (fun j =>
      matrix_vec_cons a f (Fin.FS k) = matrix_vec_cons a f j ->
      Fin.FS k = j) _ _).
    + intro H. exfalso. apply (Ha k). now symmetry.
    + intros l H. f_equal. now apply Hf.
Qed.

(** Concatenation is recursive in its left argument.  This orientation makes
    cons distribution definitional and gives the canonical [Fin.L]/[Fin.R]
    index laws without casts. *)
Fixpoint matrix_vec_append {A} (n : nat) :
    (Fin.t n -> A) -> forall m, (Fin.t m -> A) -> Fin.t (n + m) -> A :=
  match n as k return
    (Fin.t k -> A) -> forall m, (Fin.t m -> A) -> Fin.t (k + m) -> A with
  | 0 => fun _ _ w => w
  | S k => fun v m w => matrix_vec_cons (matrix_vec_head v)
      (@matrix_vec_append A k (matrix_vec_tail v) m w)
  end.

Lemma matrix_vec_append_zero : forall A m (v : Fin.t 0 -> A)
    (w : Fin.t m -> A),
  @matrix_vec_append A 0 v m w = w.
Proof. reflexivity. Qed.

Lemma matrix_vec_append_cons : forall A n m a (v : Fin.t n -> A)
    (w : Fin.t m -> A),
  @matrix_vec_append A (S n) (matrix_vec_cons a v) m w =
  matrix_vec_cons a (@matrix_vec_append A n v m w).
Proof. reflexivity. Qed.

Theorem matrix_vec_append_left : forall A n m (v : Fin.t n -> A)
    (w : Fin.t m -> A) (i : Fin.t n),
  @matrix_vec_append A n v m w (Fin.L m i) = v i.
Proof.
  intros A n. induction n as [|n IH]; intros m v w i; [inversion i |].
  refine (@Fin.caseS' n i (fun j =>
    @matrix_vec_append A (S n) v m w (Fin.L m j) = v j) _ _).
  - reflexivity.
  - intro j. apply IH.
Qed.

Theorem matrix_vec_append_right : forall A n m (v : Fin.t n -> A)
    (w : Fin.t m -> A) (i : Fin.t m),
  @matrix_vec_append A n v m w (Fin.R n i) = w i.
Proof.
  intros A n. induction n as [|n IH]; intros m v w i; simpl.
  - reflexivity.
  - apply IH.
Qed.

Definition matrix_vec_singleton {A} (a : A) : Fin.t 1 -> A :=
  matrix_vec_cons a matrix_vec_empty.

Definition matrix_vec_snoc {A n} (v : Fin.t n -> A) (a : A) :
    Fin.t (n + 1) -> A :=
  @matrix_vec_append A n v 1 (matrix_vec_singleton a).

Lemma matrix_vec_snoc_left : forall A n (v : Fin.t n -> A) a
    (i : Fin.t n),
  matrix_vec_snoc v a (Fin.L 1 i) = v i.
Proof. intros. apply matrix_vec_append_left. Qed.

Lemma matrix_vec_snoc_last : forall A n (v : Fin.t n -> A) a,
  matrix_vec_snoc v a (Fin.R n Fin.F1) = a.
Proof. intros. apply matrix_vec_append_right. Qed.

Lemma matrix_vec_snoc_cons : forall A n a b (v : Fin.t n -> A),
  matrix_vec_snoc (matrix_vec_cons a v) b =
  matrix_vec_cons a (matrix_vec_snoc v b).
Proof. reflexivity. Qed.

Theorem matrix_vec_map_append : forall A B n m (f : A -> B)
    (v : Fin.t n -> A) (w : Fin.t m -> A),
  matrix_vec_map f (@matrix_vec_append A n v m w) =
  @matrix_vec_append B n (matrix_vec_map f v) m (matrix_vec_map f w).
Proof.
  intros A B n. induction n as [|n IH]; intros m f v w; simpl.
  - reflexivity.
  - rewrite matrix_vec_map_cons. f_equal. apply IH.
Qed.

Definition matrix_vec_to_nat {n} (v : Fin.t n -> nat) : nat :=
  @matrix_vec_foldr nat nat
    (fun head tail => S (Cantor.to_nat (head, tail))) 0 n v.

Lemma matrix_vec_to_nat_empty : forall (v : Fin.t 0 -> nat),
  matrix_vec_to_nat v = 0.
Proof. reflexivity. Qed.

Lemma matrix_vec_to_nat_cons : forall n x (v : Fin.t n -> nat),
  matrix_vec_to_nat (matrix_vec_cons x v) =
  S (Cantor.to_nat (x, matrix_vec_to_nat v)).
Proof. reflexivity. Qed.
