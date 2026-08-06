(** The concrete first-order language of set theory.

    The signature has no function symbols and exactly two binary relation
    symbols, equality and membership.  Besides the source-facing symbol
    encodings, this module gives an exact bridge between abstract membership
    structures and the generic first-order semantics already used throughout
    the port.

    An arbitrary set-language structure canonically determines a membership
    relation.  Rebuilding its standard structure preserves membership
    definitionally and preserves equality under only the explicit condition
    that the original equality symbol denotes Coq equality.  The exact laws
    on canonical two-element vectors are constructive; extension to every
    finite-vector presentation uses only function extensionality for vector
    eta, avoiding the source's additional propositional extensionality. *)

From Stdlib Require Import Lists.List Program.Equality Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.SetTheory.Basic Require Import Model.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition set_func (_ : nat) : Type := Empty_set.

Definition set_func_elim {k A} (F : set_func k) : A :=
  match F with end.

Inductive set_rel : nat -> Type :=
| SetEq : set_rel 2
| SetMem : set_rel 2.

Definition set_language : language :=
  {| language_func := set_func;
     language_rel := set_rel |}.

Definition set_language_eq : language_has_eq set_language :=
  @Build_language_has_eq set_language SetEq.

Definition set_language_mem : language_has_mem set_language :=
  @Build_language_has_mem set_language SetMem.

Lemma set_language_relational : language_relational set_language.
Proof. intros k f. destruct f. Qed.

Lemma set_rel_arity_two : forall k (R : set_rel k), k = 2.
Proof. intros k R. destruct R; reflexivity. Qed.

(** A dependent eliminator is the cast-free form of the source theorem that
    every relation symbol is either equality or membership. *)
Lemma set_rel_elim : forall
    (P : forall k, set_rel k -> Prop),
  P 2 SetEq -> P 2 SetMem -> forall k (R : set_rel k), P k R.
Proof. intros P Heq Hmem k R. destruct R; assumption. Qed.

Definition set_language_decidable_eq : language_decidable_eq set_language.
Proof.
  constructor; intros k x y.
  - destruct x.
  - change (set_rel k) in x, y.
    dependent destruction x; dependent destruction y;
      try (left; reflexivity); right; discriminate.
Defined.

Definition set_rel_encode {k} (R : set_rel k) : nat :=
  match R with SetEq => 0 | SetMem => 1 end.

Definition set_rel_decode (k code : nat) : option (set_rel k).
Proof.
  destruct k as [|[|[|k]]].
  - exact None.
  - exact None.
  - destruct code as [|[|code]];
      [exact (Some SetEq) | exact (Some SetMem) | exact None].
  - exact None.
Defined.

Lemma set_rel_decode_encode : forall k (R : set_rel k),
  set_rel_decode k (set_rel_encode R) = Some R.
Proof. intros k R. destruct R; reflexivity. Qed.

Definition set_language_func_encoding k :
    encoding (language_func set_language k) := empty_encoding.

Definition set_language_rel_encoding k :
    encoding (language_rel set_language k) :=
  {| encode := set_rel_encode;
     decode := set_rel_decode k;
     decode_encode := fun R => set_rel_decode_encode (k := k) R |}.

Definition set_language_encodable : language_encodable set_language :=
  {| language_func_encoding := set_language_func_encoding;
     language_rel_encoding := set_language_rel_encoding |}.

Definition set_function_symbols :
    list {k : nat & language_func set_language k} := [].

Definition set_relation_symbols :
    list {k : nat & language_rel set_language k} :=
  [existT _ 2 SetEq; existT _ 2 SetMem].

Lemma set_function_symbols_complete : forall x,
  In x set_function_symbols.
Proof. intros [k f]. destruct f. Qed.

Lemma set_relation_symbols_complete : forall x,
  In x set_relation_symbols.
Proof. intros [k R]. destruct R; simpl; auto. Qed.

Definition set_language_finite : language_finite set_language :=
  {| language_finite_func :=
       {| finite_cover_list := set_function_symbols;
          finite_cover_complete := set_function_symbols_complete |};
     language_finite_rel :=
       {| finite_cover_list := set_relation_symbols;
          finite_cover_complete := set_relation_symbols_complete |} |}.

Definition set_theory_syntax : Type := theory set_language.
Definition set_semiterm (X : Type) (n : nat) : Type :=
  semiterm set_language X n.
Definition set_term (X : Type) : Type := term set_language X.
Definition set_semiformula (X : Type) (n : nat) : Type :=
  semiformula set_language X n.
Definition set_formula (X : Type) : Type := formula set_language X.
Definition set_semisentence (n : nat) : Type :=
  semiformula set_language Empty_set n.
Definition set_sentence : Type := sentence set_language.
Definition set_semiproposition (n : nat) : Type :=
  semiproposition set_language n.
Definition set_proposition : Type := proposition set_language.

(** The standard first-order interpretation of a membership structure. *)
Definition set_standard_func (m : membership_structure) {k}
    (F : language_func set_language k)
    (_ : Fin.t k -> membership_carrier m) : membership_carrier m :=
  @set_func_elim k (membership_carrier m) F.

Definition set_standard_rel (m : membership_structure) {k}
    (R : language_rel set_language k)
    (v : Fin.t k -> membership_carrier m) : Prop :=
  match R in set_rel arity
      return (Fin.t arity -> membership_carrier m) -> Prop with
  | SetEq => fun w => w Fin.F1 = w (Fin.FS Fin.F1)
  | SetMem => fun w =>
      @membership_rel m (w Fin.F1) (w (Fin.FS Fin.F1))
  end v.

Definition set_standard_structure (m : membership_structure) :
    first_order_structure set_language (membership_carrier m) :=
  {| structure_func := @set_standard_func m;
     structure_rel := @set_standard_rel m |}.

Lemma set_standard_structure_eq : forall m
    (v : Fin.t 2 -> membership_carrier m),
  structure_rel (set_standard_structure m) SetEq v <->
  v Fin.F1 = v (Fin.FS Fin.F1).
Proof. intros; split; trivial. Qed.

Lemma set_standard_structure_mem : forall m
    (v : Fin.t 2 -> membership_carrier m),
  structure_rel (set_standard_structure m) SetMem v <->
  @membership_rel m (v Fin.F1) (v (Fin.FS Fin.F1)).
Proof. intros; split; trivial. Qed.

Lemma set_standard_structure_mem_two : forall m
    (x y : membership_carrier m),
  structure_rel (set_standard_structure m) SetMem (fin_two x y) <->
  @membership_rel m x y.
Proof. intros; split; trivial. Qed.

(** Extract the membership relation from any set-language structure. *)
Definition membership_of_set_structure {M : Type}
    (S : first_order_structure set_language M) : membership_structure :=
  {| membership_carrier := M;
     membership_rel := fun x y => structure_rel S SetMem (fin_two x y) |}.

Definition set_structure_equality_correct {M : Type}
    (S : first_order_structure set_language M) : Prop :=
  forall v : Fin.t 2 -> M,
    structure_rel S SetEq v <->
    v Fin.F1 = v (Fin.FS Fin.F1).

Definition canonical_set_structure {M : Type}
    (S : first_order_structure set_language M) :
    first_order_structure set_language M :=
  set_standard_structure (membership_of_set_structure S).

Lemma canonical_set_structure_mem_two : forall M
    (S : first_order_structure set_language M) x y,
  structure_rel (canonical_set_structure S) SetMem (fin_two x y) <->
  structure_rel S SetMem (fin_two x y).
Proof. intros; split; trivial. Qed.

Lemma canonical_set_structure_func : forall M
    (S : first_order_structure set_language M) k
    (F : language_func set_language k) v,
  structure_func (canonical_set_structure S) F v =
  structure_func S F v.
Proof. intros M S k F. destruct F. Qed.

Lemma canonical_set_structure_mem : forall M
    (S : first_order_structure set_language M)
    (v : Fin.t 2 -> M),
  structure_rel (canonical_set_structure S) SetMem v <->
  structure_rel S SetMem v.
Proof.
  intros M S v. unfold canonical_set_structure,
    set_standard_structure, membership_of_set_structure. simpl.
  rewrite (fin_two_eta v). split; trivial.
Qed.

Lemma canonical_set_structure_eq : forall M
    (S : first_order_structure set_language M),
  set_structure_equality_correct S ->
  forall v : Fin.t 2 -> M,
    structure_rel (canonical_set_structure S) SetEq v <->
    structure_rel S SetEq v.
Proof.
  intros M S Heq v. unfold canonical_set_structure,
    set_standard_structure. simpl. symmetry. apply Heq.
Qed.

Lemma canonical_set_structure_rel : forall M
    (S : first_order_structure set_language M),
  set_structure_equality_correct S ->
  forall k (R : language_rel set_language k) v,
    structure_rel (canonical_set_structure S) R v <->
    structure_rel S R v.
Proof.
  intros M S Heq k R. destruct R.
  - apply canonical_set_structure_eq. exact Heq.
  - apply canonical_set_structure_mem.
Qed.

Lemma set_standard_structure_equality_correct : forall m,
  set_structure_equality_correct (set_standard_structure m).
Proof. intros m v. apply set_standard_structure_eq. Qed.

Print Assumptions set_rel_elim.
Print Assumptions canonical_set_structure_mem_two.
Print Assumptions canonical_set_structure_rel.
Print Assumptions set_standard_structure_equality_correct.
