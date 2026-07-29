(**
  Arity-indexed first-order languages.

  This is an idiomatic Coq port of the mathematical surface of
  [Foundation/Syntax/Predicate/Language.lean].  Symbols retain their arity in
  their type, so malformed applications are unrepresentable.  Equality,
  encoding, and finiteness are explicit reusable packages rather than global
  typeclass search obligations.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record language : Type := {
  language_func : nat -> Type;
  language_rel : nat -> Type
}.

Arguments language_func _ _ : clear implicits.
Arguments language_rel _ _ : clear implicits.

(** Structural language classes, expressed as propositions/data. *)
Definition language_relational (L : language) : Prop :=
  forall k, language_func L k -> False.

Definition language_is_constant (L : language) : Prop :=
  (forall k, language_func L (S k) -> False) /\
  (forall k, language_rel L k -> False).

Definition language_constant_inhabited (L : language) : Type :=
  language_func L 0.

Definition empty_language : language :=
  {| language_func := fun _ => Empty_set;
     language_rel := fun _ => Empty_set |}.

(** * Standard relational signatures *)

Inductive graph_func : nat -> Type :=
| Graph_start : graph_func 0
| Graph_terminal : graph_func 0.

Inductive graph_rel : nat -> Type :=
| Graph_equal : graph_rel 2
| Graph_le : graph_rel 2.

Definition graph_language : language :=
  {| language_func := graph_func; language_rel := graph_rel |}.

Inductive binary_rel : nat -> Type :=
| Binary_isone : binary_rel 1
| Binary_equal : binary_rel 2
| Binary_le : binary_rel 2.

Definition binary_language : language :=
  {| language_func := fun _ => Empty_set; language_rel := binary_rel |}.

Inductive equality_rel : nat -> Type :=
| Equality_equal : equality_rel 2.

Definition equality_language : language :=
  {| language_func := fun _ => Empty_set; language_rel := equality_rel |}.

Lemma equality_language_relational : language_relational equality_language.
Proof. intros k f; destruct f. Qed.

(** * The ordered-ring signature *)

Inductive oring_func : nat -> Type :=
| ORing_zero : oring_func 0
| ORing_one : oring_func 0
| ORing_add : oring_func 2
| ORing_mul : oring_func 2.

Inductive oring_rel : nat -> Type :=
| ORing_eq : oring_rel 2
| ORing_lt : oring_rel 2.

Definition oring_language : language :=
  {| language_func := oring_func; language_rel := oring_rel |}.

Lemma oring_func_one_empty : language_func oring_language 1 -> False.
Proof. intro f; inversion f. Qed.

Lemma oring_func_ge_three_empty :
  forall k, 3 <= k -> language_func oring_language k -> False.
Proof. intros k H f; inversion f; lia. Qed.

(** * Constant-only and composite signatures *)

Inductive constant_func (C : Type) : nat -> Type :=
| Constant_symbol : C -> constant_func C 0.

Definition constant_language (C : Type) : language :=
  {| language_func := constant_func C;
     language_rel := fun _ => Empty_set |}.

Definition unit_language : language := constant_language unit.

Lemma constant_language_is_constant :
  forall C, language_is_constant (constant_language C).
Proof.
  intro C; split.
  - intros k f; inversion f.
  - intros k r; destruct r.
Qed.

Definition function_only_language (F : nat -> Type) : language :=
  {| language_func := F; language_rel := fun _ => Empty_set |}.

Definition language_add (L M : language) : language :=
  {| language_func := fun k => (language_func L k + language_func M k)%type;
     language_rel := fun k => (language_rel L k + language_rel M k)%type |}.

Definition language_sigma {I : Type} (Ls : I -> language) : language :=
  {| language_func := fun k => {i : I & language_func (Ls i) k};
     language_rel := fun k => {i : I & language_rel (Ls i) k} |}.

(** * Named symbol capabilities *)

Record language_has_eq (L : language) : Type :=
  { language_eq : language_rel L 2 }.
Record language_has_lt (L : language) : Type :=
  { language_lt : language_rel L 2 }.
Record language_has_mem (L : language) : Type :=
  { language_mem : language_rel L 2 }.
Record language_has_zero (L : language) : Type :=
  { language_zero : language_func L 0 }.
Record language_has_one (L : language) : Type :=
  { language_one : language_func L 0 }.
Record language_has_add (L : language) : Type :=
  { language_add_symbol : language_func L 2 }.
Record language_has_mul (L : language) : Type :=
  { language_mul_symbol : language_func L 2 }.
Record language_has_pow (L : language) : Type :=
  { language_pow_symbol : language_func L 2 }.
Record language_has_exp (L : language) : Type :=
  { language_exp_symbol : language_func L 1 }.
Record language_has_pairing (L : language) : Type :=
  { language_pair_symbol : language_func L 2 }.
Record language_has_star (L : language) : Type :=
  { language_star : language_func L 0 }.

Record language_oring (L : language) : Type := {
  language_oring_eq : language_has_eq L;
  language_oring_lt : language_has_lt L;
  language_oring_zero : language_has_zero L;
  language_oring_one : language_has_one L;
  language_oring_add : language_has_add L;
  language_oring_mul : language_has_mul L
}.

Definition oring_language_structure : language_oring oring_language :=
  {| language_oring_eq := @Build_language_has_eq oring_language ORing_eq;
     language_oring_lt := @Build_language_has_lt oring_language ORing_lt;
     language_oring_zero := @Build_language_has_zero oring_language ORing_zero;
     language_oring_one := @Build_language_has_one oring_language ORing_one;
     language_oring_add := @Build_language_has_add oring_language ORing_add;
     language_oring_mul := @Build_language_has_mul oring_language ORing_mul |}.

Definition oring_constant_inhabited :
  language_constant_inhabited oring_language := ORing_zero.

Definition unit_language_star : language_has_star unit_language :=
  @Build_language_has_star unit_language (Constant_symbol tt).

(** Named structures lift through the left summand, while star lifts through
    the right summand.  These definitions factor the six analogous source
    instances through two generic combinators. *)
Definition language_add_left_func {L M k}
    (f : language_func L k) : language_func (language_add L M) k := inl f.

Definition language_add_left_rel {L M k}
    (r : language_rel L k) : language_rel (language_add L M) k := inl r.

Definition language_add_right_func {L M k}
    (f : language_func M k) : language_func (language_add L M) k := inr f.

Definition language_add_has_zero L M (H : language_has_zero L) :
  language_has_zero (language_add L M) :=
  {| language_zero := language_add_left_func (language_zero H) |}.

Definition language_add_has_one L M (H : language_has_one L) :
  language_has_one (language_add L M) :=
  {| language_one := language_add_left_func (language_one H) |}.

Definition language_add_has_add L M (H : language_has_add L) :
  language_has_add (language_add L M) :=
  {| language_add_symbol := language_add_left_func (language_add_symbol H) |}.

Definition language_add_has_mul L M (H : language_has_mul L) :
  language_has_mul (language_add L M) :=
  {| language_mul_symbol := language_add_left_func (language_mul_symbol H) |}.

Definition language_add_has_eq L M (H : language_has_eq L) :
  language_has_eq (language_add L M) :=
  {| language_eq := language_add_left_rel (language_eq H) |}.

Definition language_add_has_lt L M (H : language_has_lt L) :
  language_has_lt (language_add L M) :=
  {| language_lt := language_add_left_rel (language_lt H) |}.

Definition language_add_has_star L M (H : language_has_star M) :
  language_has_star (language_add L M) :=
  {| language_star := language_add_right_func (language_star H) |}.

(** * Language homomorphisms *)

Record language_hom (L M : language) : Type := {
  hom_func : forall {k}, language_func L k -> language_func M k;
  hom_rel : forall {k}, language_rel L k -> language_rel M k
}.

Arguments hom_func {L M} _ {k} _.
Arguments hom_rel {L M} _ {k} _.

Definition language_hom_id (L : language) : language_hom L L :=
  {| hom_func := fun _ f => f; hom_rel := fun _ r => r |}.

Definition language_hom_comp {L M N}
    (g : language_hom M N) (f : language_hom L M) : language_hom L N :=
  {| hom_func := fun _ x => hom_func g (hom_func f x);
     hom_rel := fun _ x => hom_rel g (hom_rel f x) |}.

Definition language_hom_add_left (L M : language) :
  language_hom L (language_add L M) :=
  @Build_language_hom L (language_add L M)
    (fun k f => @inl (language_func L k) (language_func M k) f)
    (fun k r => @inl (language_rel L k) (language_rel M k) r).

Definition language_hom_add_right (L M : language) :
  language_hom M (language_add L M) :=
  @Build_language_hom M (language_add L M)
    (fun k f => @inr (language_func L k) (language_func M k) f)
    (fun k r => @inr (language_rel L k) (language_rel M k) r).

Definition language_hom_sigma {I} (Ls : I -> language) (i : I) :
  language_hom (Ls i) (language_sigma Ls) :=
  @Build_language_hom (Ls i) (language_sigma Ls)
    (fun k f => @existT I (fun j => language_func (Ls j) k) i f)
    (fun k r => @existT I (fun j => language_rel (Ls j) k) i r).

Lemma language_hom_add_left_func :
  forall L M k (f : language_func L k),
    hom_func (language_hom_add_left L M) f = inl f.
Proof. reflexivity. Qed.

Lemma language_hom_add_left_rel :
  forall L M k (r : language_rel L k),
    hom_rel (language_hom_add_left L M) r = inl r.
Proof. reflexivity. Qed.

Lemma language_hom_add_right_func :
  forall L M k (f : language_func M k),
    hom_func (language_hom_add_right L M) f = inr f.
Proof. reflexivity. Qed.

Lemma language_hom_add_right_rel :
  forall L M k (r : language_rel M k),
    hom_rel (language_hom_add_right L M) r = inr r.
Proof. reflexivity. Qed.

Lemma language_hom_sigma_func :
  forall I (Ls : I -> language) i k (f : language_func (Ls i) k),
    hom_func (language_hom_sigma Ls i) f = existT _ i f.
Proof. reflexivity. Qed.

Lemma language_hom_sigma_rel :
  forall I (Ls : I -> language) i k (r : language_rel (Ls i) k),
    hom_rel (language_hom_sigma Ls i) r = existT _ i r.
Proof. reflexivity. Qed.

Lemma language_hom_ext :
  forall L M (f g : language_hom L M),
    (forall k (x : language_func L k), hom_func f x = hom_func g x) ->
    (forall k (x : language_rel L k), hom_rel f x = hom_rel g x) ->
    f = g.
Proof.
  intros L M [ff fr] [gf gr] Hf Hr; simpl in *.
  assert (ff = gf) as ->.
  { apply functional_extensionality_dep; intro k.
    apply functional_extensionality; apply Hf. }
  assert (fr = gr) as ->.
  { apply functional_extensionality_dep; intro k.
    apply functional_extensionality; apply Hr. }
  reflexivity.
Qed.

Lemma language_hom_comp_id_left :
  forall L M (f : language_hom L M),
    language_hom_comp (language_hom_id M) f = f.
Proof.
  intros; apply language_hom_ext; reflexivity.
Qed.

Lemma language_hom_comp_id_right :
  forall L M (f : language_hom L M),
    language_hom_comp f (language_hom_id L) = f.
Proof.
  intros; apply language_hom_ext; reflexivity.
Qed.

Lemma language_hom_comp_assoc :
  forall K L M N (h : language_hom M N)
         (g : language_hom L M) (f : language_hom K L),
    language_hom_comp h (language_hom_comp g f) =
    language_hom_comp (language_hom_comp h g) f.
Proof.
  intros; apply language_hom_ext; reflexivity.
Qed.

Definition oring_embedding (L : language) (H : language_oring L) :
  language_hom oring_language L.
Proof.
  refine {| hom_func := fun k f => _; hom_rel := fun k r => _ |}.
  - destruct f.
    + exact (language_zero (language_oring_zero H)).
    + exact (language_one (language_oring_one H)).
    + exact (language_add_symbol (language_oring_add H)).
    + exact (language_mul_symbol (language_oring_mul H)).
  - destruct r.
    + exact (language_eq (language_oring_eq H)).
    + exact (language_lt (language_oring_lt H)).
Defined.

(** * Decidable equality, encodings, and finite symbol inventories *)

Record language_decidable_eq (L : language) : Type := {
  language_func_eq_dec : forall k (x y : language_func L k),
      {x = y} + {x <> y};
  language_rel_eq_dec : forall k (x y : language_rel L k),
      {x = y} + {x <> y}
}.

Definition equality_language_decidable_eq :
  language_decidable_eq equality_language.
Proof.
  constructor; intros k x y.
  - destruct x.
  - change (equality_rel k) in x, y.
    dependent destruction x; dependent destruction y.
    left; reflexivity.
Defined.

Definition oring_language_decidable_eq :
  language_decidable_eq oring_language.
Proof.
  constructor.
  - intros k x y; change (oring_func k) in x, y.
    dependent destruction x; dependent destruction y;
      try (left; reflexivity); right; discriminate.
  - intros k x y; change (oring_rel k) in x, y.
    dependent destruction x; dependent destruction y;
      try (left; reflexivity); right; discriminate.
Defined.

Record encoding (A : Type) : Type := {
  encode : A -> nat;
  decode : nat -> option A;
  decode_encode : forall x, decode (encode x) = Some x
}.

Definition empty_encoding : encoding Empty_set.
Proof.
  refine (@Build_encoding Empty_set
    (fun x : Empty_set => match x with end)
    (fun _ => @None Empty_set) _).
  intro x; destruct x.
Defined.

Definition equality_rel_encode {k} (r : equality_rel k) : nat :=
  match r with Equality_equal => 0 end.

Definition equality_rel_decode (k n : nat) : option (equality_rel k).
Proof.
  destruct k as [|[|[|k]]].
  - exact None.
  - exact None.
  - destruct n; [exact (Some Equality_equal) | exact None].
  - exact None.
Defined.

Lemma equality_rel_decode_encode :
  forall k (r : equality_rel k),
    equality_rel_decode k (equality_rel_encode r) = Some r.
Proof. intros k r; destruct r; reflexivity. Qed.

Definition equality_language_func_encoding k :
  encoding (language_func equality_language k) := empty_encoding.

Definition equality_language_rel_encoding k :
  encoding (language_rel equality_language k) :=
  {| encode := equality_rel_encode;
     decode := equality_rel_decode k;
     decode_encode := fun r => equality_rel_decode_encode (k := k) r |}.

Definition oring_func_encode {k} (f : oring_func k) : nat :=
  match f with
  | ORing_zero => 0 | ORing_one => 1
  | ORing_add => 2 | ORing_mul => 3
  end.

Definition oring_func_decode (k n : nat) : option (oring_func k).
Proof.
  destruct k as [|[|[|k]]].
  - destruct n as [|[|n]]; [exact (Some ORing_zero) | exact (Some ORing_one) | exact None].
  - exact None.
  - destruct n as [|[|[|[|n]]]];
      [exact None | exact None | exact (Some ORing_add) |
       exact (Some ORing_mul) | exact None].
  - exact None.
Defined.

Lemma oring_func_decode_encode :
  forall k (f : oring_func k),
    oring_func_decode k (oring_func_encode f) = Some f.
Proof. intros k f; destruct f; reflexivity. Qed.

Definition oring_rel_encode {k} (r : oring_rel k) : nat :=
  match r with ORing_eq => 0 | ORing_lt => 1 end.

Definition oring_rel_decode (k n : nat) : option (oring_rel k).
Proof.
  destruct k as [|[|[|k]]].
  - exact None.
  - exact None.
  - destruct n as [|[|n]];
      [exact (Some ORing_eq) | exact (Some ORing_lt) | exact None].
  - exact None.
Defined.

Lemma oring_rel_decode_encode :
  forall k (r : oring_rel k),
    oring_rel_decode k (oring_rel_encode r) = Some r.
Proof. intros k r; destruct r; reflexivity. Qed.

Definition oring_language_func_encoding k :
  encoding (language_func oring_language k) :=
  {| encode := oring_func_encode;
     decode := oring_func_decode k;
     decode_encode := fun f => oring_func_decode_encode (k := k) f |}.

Definition oring_language_rel_encoding k :
  encoding (language_rel oring_language k) :=
  {| encode := oring_rel_encode;
     decode := oring_rel_decode k;
     decode_encode := fun r => oring_rel_decode_encode (k := k) r |}.

Record language_encodable (L : language) : Type := {
  language_func_encoding : forall k, encoding (language_func L k);
  language_rel_encoding : forall k, encoding (language_rel L k)
}.

Definition equality_language_encodable : language_encodable equality_language :=
  {| language_func_encoding := equality_language_func_encoding;
     language_rel_encoding := equality_language_rel_encoding |}.

Definition oring_language_encodable : language_encodable oring_language :=
  {| language_func_encoding := oring_language_func_encoding;
     language_rel_encoding := oring_language_rel_encoding |}.

Record finite_cover (A : Type) : Type := {
  finite_cover_list : list A;
  finite_cover_complete : forall x, In x finite_cover_list
}.

Record language_finite (L : language) : Type := {
  language_finite_func : finite_cover {k : nat & language_func L k};
  language_finite_rel : finite_cover {k : nat & language_rel L k}
}.

Definition oring_function_symbols : list {k : nat & language_func oring_language k} :=
  [existT _ 0 ORing_zero; existT _ 0 ORing_one;
   existT _ 2 ORing_add; existT _ 2 ORing_mul].

Definition oring_relation_symbols : list {k : nat & language_rel oring_language k} :=
  [existT _ 2 ORing_eq; existT _ 2 ORing_lt].

Lemma oring_function_symbols_complete :
  forall x, In x oring_function_symbols.
Proof. intros [k f]; destruct f; simpl; auto. Qed.

Lemma oring_relation_symbols_complete :
  forall x, In x oring_relation_symbols.
Proof. intros [k r]; destruct r; simpl; auto. Qed.

Definition oring_language_finite : language_finite oring_language :=
  {| language_finite_func :=
       {| finite_cover_list := oring_function_symbols;
          finite_cover_complete := oring_function_symbols_complete |};
     language_finite_rel :=
       {| finite_cover_list := oring_relation_symbols;
          finite_cover_complete := oring_relation_symbols_complete |} |}.
