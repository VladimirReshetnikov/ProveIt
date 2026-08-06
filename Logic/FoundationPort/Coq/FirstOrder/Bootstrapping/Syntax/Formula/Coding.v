(**
  Quotation of typed formulas into bootstrapped natural codes.

  The source first quotes syntax into a proof-carrying formula wrapper and
  then projects its raw value.  In the standard model that composite is
  exactly Coq's verified structural [semiformula_code].  Defining quotation
  once through that encoder makes constructor homomorphism, decoding,
  injectivity, and executable transformation laws immediate consequences of
  the reusable coding and rewriting infrastructure.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Language.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import
  Basic Typed Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Functions Typed.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition boot_typed_formula_quote {L n} (EL : language_encodable L)
    (p : boot_typed_semiformula L n) : nat :=
  semiformula_code EL boot_nat_encoding p.

Definition boot_closed_formula_quote {L n} (EL : language_encodable L)
    (p : semisentence L n) : nat :=
  semiformula_code EL empty_encoding p.

(** * Exact constructor laws *)

Lemma boot_typed_formula_quote_verum : forall L n EL,
  boot_typed_formula_quote EL (@Semiformula_verum L nat n) =
  boot_qq_verum.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_quote_falsum : forall L n EL,
  boot_typed_formula_quote EL (@Semiformula_falsum L nat n) =
  boot_qq_falsum.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_quote_rel : forall L n EL k
    (r : language_rel L k) (v : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_quote EL (Semiformula_rel r v) =
  boot_qq_rel k (boot_rel_quote EL r)
    (fin_nat_code (fun i => boot_typed_quote EL (v i))).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_quote_nrel : forall L n EL k
    (r : language_rel L k) (v : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_quote EL (Semiformula_nrel r v) =
  boot_qq_nrel k (boot_rel_quote EL r)
    (fin_nat_code (fun i => boot_typed_quote EL (v i))).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_quote_and : forall L n EL
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_quote EL (Semiformula_and p q) =
  boot_qq_and (boot_typed_formula_quote EL p)
    (boot_typed_formula_quote EL q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_quote_or : forall L n EL
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_quote EL (Semiformula_or p q) =
  boot_qq_or (boot_typed_formula_quote EL p)
    (boot_typed_formula_quote EL q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_quote_all : forall L n EL
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_quote EL (Semiformula_all p) =
  boot_qq_all (boot_typed_formula_quote EL p).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_quote_exists : forall L n EL
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_quote EL (Semiformula_exists p) =
  boot_qq_exists (boot_typed_formula_quote EL p).
Proof. reflexivity. Qed.

(** Quotation is a homomorphism for every derived connective as well. *)
Lemma boot_typed_formula_quote_neg : forall L n EL
    (p : boot_typed_semiformula L n),
  boot_typed_formula_quote EL (boot_typed_formula_neg p) =
  boot_formula_neg_code EL n (boot_typed_formula_quote EL p).
Proof. intros. symmetry. apply boot_typed_formula_neg_code. Qed.

Lemma boot_typed_formula_quote_imp : forall L n EL
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_quote EL (boot_typed_formula_imp p q) =
  boot_qq_or
    (boot_formula_neg_code EL n (boot_typed_formula_quote EL p))
    (boot_typed_formula_quote EL q).
Proof.
  intros. unfold boot_typed_formula_quote, boot_typed_formula_imp,
    semiformula_imp. rewrite boot_qq_or_quote.
  now rewrite boot_formula_neg_code_quote.
Qed.

Lemma boot_typed_formula_quote_iff : forall L n EL
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_quote EL (boot_typed_formula_iff p q) =
  boot_qq_and
    (boot_typed_formula_quote EL (boot_typed_formula_imp p q))
    (boot_typed_formula_quote EL (boot_typed_formula_imp q p)).
Proof. reflexivity. Qed.

(** * Injectivity, decoding, and exact range *)

Theorem boot_typed_formula_quote_injective : forall L n EL
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_quote EL p = boot_typed_formula_quote EL q -> p = q.
Proof.
  intros L n EL p q H.
  exact (@semiformula_code_injective L nat n EL boot_nat_encoding p q H).
Qed.

Lemma boot_typed_formula_quote_inj_iff : forall L n EL
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_quote EL p = boot_typed_formula_quote EL q <-> p = q.
Proof.
  intros; split; [apply boot_typed_formula_quote_injective|now intros ->].
Qed.

Theorem boot_typed_formula_quote_decode : forall L n EL
    (p : boot_typed_semiformula L n),
  semiformula_decode EL boot_nat_encoding n
      (boot_typed_formula_quote EL p) = Some p.
Proof. intros. apply semiformula_decode_code. Qed.

Theorem boot_closed_formula_quote_decode : forall L n EL
    (p : semisentence L n),
  semiformula_decode EL empty_encoding n
      (boot_closed_formula_quote EL p) = Some p.
Proof. intros. apply semiformula_decode_code. Qed.

Theorem boot_typed_formula_quote_recognized : forall L n EL
    (p : boot_typed_semiformula L n),
  boot_is_semiformula EL n (boot_typed_formula_quote EL p).
Proof. intros. apply semiformula_code_is_semiformula. Qed.

Theorem boot_typed_formula_quote_sound : forall L n EL code,
  @boot_is_semiformula L EL n code <->
  exists p : boot_typed_semiformula L n,
    boot_typed_formula_quote EL p = code.
Proof.
  intros L n EL code.
  unfold boot_typed_semiformula, boot_typed_formula_quote.
  apply boot_is_semiformula_quote_iff.
Qed.

(** Closed syntax embeds without changing its code. *)
Lemma boot_closed_formula_quote_emb : forall L n EL
    (p : semisentence L n),
  boot_typed_formula_quote EL
    (semiformula_rewrite
      (@rew_emb L Empty_set nat n (fun x => match x with end)) p) =
  boot_closed_formula_quote EL p.
Proof. intros. apply semiformula_code_emb. Qed.

(** * Naturality of quotation *)

Lemma boot_typed_formula_quote_shift : forall L n EL
    (p : boot_typed_semiformula L n),
  boot_typed_formula_quote EL (boot_typed_formula_shift p) =
  boot_formula_shift_code EL n (boot_typed_formula_quote EL p).
Proof. intros. symmetry. apply boot_typed_formula_shift_code. Qed.

Lemma boot_typed_formula_quote_subst : forall L n m EL
    (v : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L n),
  boot_typed_formula_quote EL (boot_typed_formula_subst v p) =
  boot_formula_subst_code EL v (boot_typed_formula_quote EL p).
Proof. intros. symmetry. apply boot_typed_formula_subst_code. Qed.

Lemma boot_typed_formula_quote_free : forall L EL
    (p : boot_typed_semiformula L 1),
  boot_typed_formula_quote EL (boot_typed_formula_free p) =
  boot_formula_subst_code EL
    (fun _ : Fin.t 1 => @Semiterm_fvar L nat 0 0)
    (boot_formula_shift_code EL 1 (boot_typed_formula_quote EL p)).
Proof.
  intros. rewrite boot_typed_formula_free_as_shift_subst,
    boot_typed_formula_quote_subst, boot_typed_formula_quote_shift.
  reflexivity.
Qed.

(** The reusable encoding package and quotation are definitionally equal. *)
Lemma boot_typed_formula_quote_encoding : forall L n EL
    (p : boot_typed_semiformula L n),
  encode (semiformula_encoding n EL boot_nat_encoding) p =
  boot_typed_formula_quote EL p.
Proof. reflexivity. Qed.

Lemma boot_closed_formula_quote_encoding : forall L n EL
    (p : semisentence L n),
  encode (semiformula_encoding n EL empty_encoding) p =
  boot_closed_formula_quote EL p.
Proof. reflexivity. Qed.
