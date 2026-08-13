(** Generic list-membership kernel extracted from Foundation's quotation API.

    These are the only proof-level declarations in [Foundation/Meta/Qq.lean].
    The surrounding quoted-expression and metaprogramming operations are
    Lean-specific and intentionally have no Coq counterpart. *)

From Stdlib Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source declaration [Qq.List.mem_of_eq]. *)
Lemma generic_quotation_list_mem_of_eq :
  forall (A : Type) (a b : A) (tail : list A),
    a = b -> In a (b :: tail).
Proof.
  intros A a b tail Hab. subst b. now left.
Qed.

(** Source declaration [Qq.List.mem_of_mem]. *)
Lemma generic_quotation_list_mem_of_mem :
  forall (A : Type) (a b : A) (tail : list A),
    In a tail -> In a (b :: tail).
Proof.
  intros A a b tail Ha. now right.
Qed.

(** Source declaration [Qq.List.mem_singleton_of_eq]. *)
Lemma generic_quotation_list_mem_singleton_of_eq :
  forall (A : Type) (a b : A),
    a = b -> In a [b].
Proof.
  intros A a b Hab. subst b. now left.
Qed.
