(**
  Quotation of typed semiterms into bootstrapped natural codes.

  This is the Coq counterpart of
  [Foundation/FirstOrder/Bootstrapping/Syntax/Term/Coding.lean].  Since Coq's
  typed semiterm is already the source object wrapped by Foundation's
  [Bootstrapping.Semiterm], quotation is exactly the verified structural
  [semiterm_code].
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Language.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import
  Basic Functions Typed.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition boot_typed_quote {L n} (EL : language_encodable L)
    (t : boot_typed_semiterm L n) : nat :=
  semiterm_code EL boot_nat_encoding t.

Definition boot_closed_quote {L n} (EL : language_encodable L)
    (t : closed_semiterm L n) : nat :=
  semiterm_code EL empty_encoding t.

(** * Exact constructor laws *)

Lemma boot_typed_quote_bvar : forall L n EL (i : Fin.t n),
  boot_typed_quote EL (@Semiterm_bvar L nat n i) =
  boot_qq_bvar (fin_value i).
Proof. reflexivity. Qed.

Lemma boot_typed_quote_fvar : forall L n EL x,
  boot_typed_quote EL (@Semiterm_fvar L nat n x) = boot_qq_fvar x.
Proof. reflexivity. Qed.

Lemma boot_typed_quote_func : forall L n EL k
    (f : language_func L k) (v : boot_typed_semiterm_vec L k n),
  boot_typed_quote EL (Semiterm_func f v) =
  boot_qq_func k (boot_func_quote EL f)
    (fin_nat_code (fun i => boot_typed_quote EL (v i))).
Proof. reflexivity. Qed.

Lemma boot_closed_quote_bvar : forall L n EL (i : Fin.t n),
  boot_closed_quote EL (@Semiterm_bvar L Empty_set n i) =
  boot_qq_bvar (fin_value i).
Proof. reflexivity. Qed.

Lemma boot_closed_quote_func : forall L n EL k
    (f : language_func L k) (v : Fin.t k -> closed_semiterm L n),
  boot_closed_quote EL (Semiterm_func f v) =
  boot_qq_func k (boot_func_quote EL f)
    (fin_nat_code (fun i => boot_closed_quote EL (v i))).
Proof. reflexivity. Qed.

(** * Injectivity and decoding *)

Theorem boot_typed_quote_injective : forall L n EL
    (t u : boot_typed_semiterm L n),
  boot_typed_quote EL t = boot_typed_quote EL u -> t = u.
Proof.
  intros L n EL t u H.
  exact (@semiterm_code_injective L nat n EL boot_nat_encoding t u H).
Qed.

Lemma boot_typed_quote_inj_iff : forall L n EL
    (t u : boot_typed_semiterm L n),
  boot_typed_quote EL t = boot_typed_quote EL u <-> t = u.
Proof.
  intros; split; [apply boot_typed_quote_injective|now intros ->].
Qed.

Theorem boot_typed_quote_decode : forall L n EL
    (t : boot_typed_semiterm L n),
  semiterm_decode EL boot_nat_encoding n (boot_typed_quote EL t) = Some t.
Proof. intros. apply semiterm_decode_code. Qed.

Theorem boot_closed_quote_decode : forall L n EL
    (t : closed_semiterm L n),
  semiterm_decode EL empty_encoding n (boot_closed_quote EL t) = Some t.
Proof. intros. apply semiterm_decode_code. Qed.

Theorem boot_typed_quote_recognized : forall L n EL
    (t : boot_typed_semiterm L n),
  boot_is_semiterm EL n (boot_typed_quote EL t).
Proof. intros. apply semiterm_code_is_semiterm. Qed.

Theorem boot_typed_quote_sound : forall L n EL code,
  @boot_is_semiterm L EL n code <->
  exists t : boot_typed_semiterm L n, boot_typed_quote EL t = code.
Proof.
  intros L n EL code. unfold boot_typed_semiterm, boot_typed_quote.
  apply boot_is_semiterm_quote_iff.
Qed.

(** Closed syntax embeds without changing its code. *)
Lemma boot_closed_quote_emb : forall L n EL
    (t : closed_semiterm L n),
  boot_typed_quote EL
    (rew_apply (@rew_emb L Empty_set nat n
      (fun x => match x with end)) t) =
  boot_closed_quote EL t.
Proof. intros. apply semiterm_code_emb. Qed.

(** * Quotation commutes with all typed operations *)

Lemma boot_typed_quote_shift : forall L n EL
    (t : boot_typed_semiterm L n),
  boot_typed_quote EL (boot_typed_shift t) =
  boot_term_shift_code EL n (boot_typed_quote EL t).
Proof. intros. symmetry. apply boot_typed_shift_code. Qed.

Lemma boot_typed_quote_bshift : forall L n EL
    (t : boot_typed_semiterm L n),
  boot_typed_quote EL (boot_typed_bshift t) =
  boot_term_bshift_code EL boot_nat_encoding n (boot_typed_quote EL t).
Proof. intros. symmetry. apply boot_typed_bshift_code. Qed.

Lemma boot_typed_quote_subst : forall L n m EL
    (v : boot_typed_semiterm_vec L n m)
    (t : boot_typed_semiterm L n),
  boot_typed_quote EL (boot_typed_subst v t) =
  boot_term_subst_code EL v (boot_typed_quote EL t).
Proof. intros. symmetry. apply boot_typed_subst_code. Qed.

Lemma boot_typed_quote_q_zero : forall L k n EL
    (v : boot_typed_semiterm_vec L k n),
  boot_typed_quote EL (boot_typed_q v Fin.F1) = boot_qq_bvar 0.
Proof. reflexivity. Qed.

Lemma boot_typed_quote_q_succ : forall L k n EL
    (v : boot_typed_semiterm_vec L k n) (i : Fin.t k),
  boot_typed_quote EL (boot_typed_q v (Fin.FS i)) =
  boot_term_bshift_code EL boot_nat_encoding n
    (boot_typed_quote EL (v i)).
Proof. intros. apply boot_typed_quote_bshift. Qed.

(** The standard encoding package is not merely extensionally equivalent to
    quotation: its encoder is definitionally the same function. *)
Lemma boot_typed_quote_encoding : forall L n EL
    (t : boot_typed_semiterm L n),
  encode (semiterm_encoding n EL boot_nat_encoding) t =
  boot_typed_quote EL t.
Proof. reflexivity. Qed.

Lemma boot_closed_quote_encoding : forall L n EL
    (t : closed_semiterm L n),
  encode (semiterm_encoding n EL empty_encoding) t = boot_closed_quote EL t.
Proof. reflexivity. Qed.
