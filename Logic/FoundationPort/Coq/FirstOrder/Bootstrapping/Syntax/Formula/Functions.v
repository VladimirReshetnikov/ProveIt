(**
  Executable transformations of bootstrapped formula codes.

  A single decode--transform--encode combinator factors negation and every
  capture-avoiding formula rewrite.  Its total form uses zero only outside
  the recognized-code domain; preservation and involution theorems show that
  this branch is unreachable in all mathematical uses.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Generic formula transformations *)

Definition boot_formula_transform_code {L X Y n m}
    (EL : language_encodable L) (EX : encoding X) (EY : encoding Y)
    (f : semiformula L X n -> semiformula L Y m)
    (code : nat) : option nat :=
  match semiformula_decode EL EX n code with
  | Some p => Some (semiformula_code EL EY (f p))
  | None => None
  end.

Definition boot_formula_transform_code_total {L X Y n m}
    (EL : language_encodable L) (EX : encoding X) (EY : encoding Y)
    (f : semiformula L X n -> semiformula L Y m)
    (code : nat) : nat :=
  match boot_formula_transform_code EL EX EY f code with
  | Some result => result
  | None => 0
  end.

Lemma boot_formula_transform_code_quote : forall L X Y n m EL EX EY
    (f : semiformula L X n -> semiformula L Y m)
    (p : semiformula L X n),
  boot_formula_transform_code EL EX EY f (semiformula_code EL EX p) =
  Some (semiformula_code EL EY (f p)).
Proof.
  intros. unfold boot_formula_transform_code.
  now rewrite semiformula_decode_code.
Qed.

Lemma boot_formula_transform_code_total_quote : forall L X Y n m EL EX EY
    (f : semiformula L X n -> semiformula L Y m)
    (p : semiformula L X n),
  boot_formula_transform_code_total EL EX EY f
      (semiformula_code EL EX p) =
  semiformula_code EL EY (f p).
Proof.
  intros. unfold boot_formula_transform_code_total.
  now rewrite boot_formula_transform_code_quote.
Qed.

Lemma boot_formula_transform_code_some_iff : forall L X Y n m EL EX EY
    (f : semiformula L X n -> semiformula L Y m) code result,
  boot_formula_transform_code EL EX EY f code = Some result <->
  exists p : semiformula L X n,
    semiformula_decode EL EX n code = Some p /\
    result = semiformula_code EL EY (f p).
Proof.
  intros L X Y n m EL EX EY f code result.
  unfold boot_formula_transform_code.
  destruct (semiformula_decode EL EX n code) as [p|] eqn:Hdecode.
  - split.
    + intro H. injection H as Hresult. exists p. now split.
    + intros [q [Hq ->]]. injection Hq as <-. reflexivity.
  - split; [discriminate|]. intros [p [Hp _]]. discriminate Hp.
Qed.

Theorem boot_formula_transform_code_total_preserves : forall L Y n m EL EY
    (f : semiformula L nat n -> semiformula L Y m) code,
  boot_is_semiformula EL n code ->
  boot_is_semiformula EL m
    (boot_formula_transform_code_total EL boot_nat_encoding EY f code).
Proof.
  intros L Y n m EL EY f code Hcode.
  destruct (boot_is_semiformula_has_quote Hcode) as [p Hp].
  rewrite <- Hp, boot_formula_transform_code_total_quote.
  apply semiformula_code_is_semiformula.
Qed.

(** * Capture-avoiding rewrites *)

Definition boot_formula_rewrite_code {L X Y n m}
    (EL : language_encodable L) (EX : encoding X) (EY : encoding Y)
    (w : rew L X n Y m) (code : nat) : nat :=
  boot_formula_transform_code_total EL EX EY
    (semiformula_rewrite w) code.

Lemma boot_formula_rewrite_code_quote : forall L X Y n m EL EX EY
    (w : rew L X n Y m) (p : semiformula L X n),
  boot_formula_rewrite_code EL EX EY w (semiformula_code EL EX p) =
  semiformula_code EL EY (semiformula_rewrite w p).
Proof. intros. apply boot_formula_transform_code_total_quote. Qed.

Theorem boot_formula_rewrite_code_preserves : forall L Y n m EL EY
    (w : rew L nat n Y m) code,
  boot_is_semiformula EL n code ->
  boot_is_semiformula EL m
    (boot_formula_rewrite_code EL boot_nat_encoding EY w code).
Proof.
  intros. unfold boot_formula_rewrite_code.
  now apply boot_formula_transform_code_total_preserves.
Qed.

Theorem boot_formula_rewrite_code_comp : forall L X Y Z n m l
    EL EX EY EZ (v : rew L Y m Z l) (w : rew L X n Y m)
    (p : semiformula L X n),
  boot_formula_rewrite_code EL EY EZ v
    (boot_formula_rewrite_code EL EX EY w (semiformula_code EL EX p)) =
  boot_formula_rewrite_code EL EX EZ (rew_comp v w)
    (semiformula_code EL EX p).
Proof.
  intros. unfold boot_formula_rewrite_code.
  rewrite !boot_formula_transform_code_total_quote.
  now rewrite semiformula_rewrite_comp.
Qed.

(** * Simultaneous substitution and shifts *)

Definition boot_formula_subst_code {L n m}
    (EL : language_encodable L)
    (v : Fin.t n -> syntactic_semiterm L m) (code : nat) : nat :=
  boot_formula_rewrite_code EL boot_nat_encoding boot_nat_encoding
    (rew_subst v) code.

Definition boot_formula_shift_code {L}
    (EL : language_encodable L) (n code : nat) : nat :=
  boot_formula_rewrite_code EL boot_nat_encoding boot_nat_encoding
    (@rew_shift L n) code.

Definition boot_formula_bshift_code {L}
    (EL : language_encodable L) (n code : nat) : nat :=
  boot_formula_rewrite_code EL boot_nat_encoding boot_nat_encoding
    (@rew_bshift L nat n) code.

Lemma boot_formula_subst_code_quote : forall L n m EL
    (v : Fin.t n -> syntactic_semiterm L m)
    (p : semiproposition L n),
  boot_formula_subst_code EL v
      (semiformula_code EL boot_nat_encoding p) =
  semiformula_code EL boot_nat_encoding (semiformula_substitute v p).
Proof. intros. apply boot_formula_rewrite_code_quote. Qed.

Lemma boot_formula_shift_code_quote : forall L n EL
    (p : semiproposition L n),
  boot_formula_shift_code EL n (semiformula_code EL boot_nat_encoding p) =
  semiformula_code EL boot_nat_encoding (semiformula_shift p).
Proof. intros. apply boot_formula_rewrite_code_quote. Qed.

Lemma boot_formula_bshift_code_quote : forall L n EL
    (p : semiproposition L n),
  boot_formula_bshift_code EL n (semiformula_code EL boot_nat_encoding p) =
  semiformula_code EL boot_nat_encoding
    (semiformula_rewrite rew_bshift p).
Proof. intros. apply boot_formula_rewrite_code_quote. Qed.

Theorem boot_formula_subst_code_preserves : forall L n m EL
    (v : Fin.t n -> syntactic_semiterm L m) code,
  boot_is_semiformula EL n code ->
  boot_is_semiformula EL m (boot_formula_subst_code EL v code).
Proof.
  intros. unfold boot_formula_subst_code.
  now apply boot_formula_rewrite_code_preserves.
Qed.

Theorem boot_formula_shift_code_preserves : forall (L : language) n
    (EL : language_encodable L) code,
  boot_is_semiformula EL n code ->
  boot_is_semiformula EL n (boot_formula_shift_code EL n code).
Proof.
  intros. unfold boot_formula_shift_code.
  now apply boot_formula_rewrite_code_preserves.
Qed.

Theorem boot_formula_bshift_code_preserves : forall (L : language) n
    (EL : language_encodable L) code,
  boot_is_semiformula EL n code ->
  boot_is_semiformula EL (S n) (boot_formula_bshift_code EL n code).
Proof.
  intros. unfold boot_formula_bshift_code.
  now apply boot_formula_rewrite_code_preserves.
Qed.

Theorem boot_formula_subst_code_comp : forall L n m l EL
    (v : Fin.t n -> syntactic_semiterm L m)
    (w : Fin.t m -> syntactic_semiterm L l)
    (p : semiproposition L n),
  boot_formula_subst_code EL w
    (boot_formula_subst_code EL v
      (semiformula_code EL boot_nat_encoding p)) =
  boot_formula_subst_code EL
    (fun i => rew_apply (rew_subst w) (v i))
    (semiformula_code EL boot_nat_encoding p).
Proof.
  intros. rewrite !boot_formula_subst_code_quote.
  apply f_equal. apply semiformula_substitute_comp.
Qed.

(** * Negation *)

Definition boot_formula_neg_code {L}
    (EL : language_encodable L) (n code : nat) : nat :=
  boot_formula_transform_code_total EL boot_nat_encoding boot_nat_encoding
    (@semiformula_neg L nat n) code.

Lemma boot_formula_neg_code_quote : forall L n EL
    (p : semiproposition L n),
  boot_formula_neg_code EL n (semiformula_code EL boot_nat_encoding p) =
  semiformula_code EL boot_nat_encoding (semiformula_neg p).
Proof. intros. apply boot_formula_transform_code_total_quote. Qed.

Lemma boot_formula_neg_verum : forall (L : language)
    (EL : language_encodable L) n,
  boot_formula_neg_code EL n boot_qq_verum = boot_qq_falsum.
Proof.
  intros. rewrite <- (@boot_qq_verum_quote L nat n EL boot_nat_encoding),
    boot_formula_neg_code_quote. reflexivity.
Qed.

Lemma boot_formula_neg_falsum : forall (L : language)
    (EL : language_encodable L) n,
  boot_formula_neg_code EL n boot_qq_falsum = boot_qq_verum.
Proof.
  intros. rewrite <- (@boot_qq_falsum_quote L nat n EL boot_nat_encoding),
    boot_formula_neg_code_quote. reflexivity.
Qed.

Lemma boot_formula_neg_and_quote : forall L n EL
    (p q : semiproposition L n),
  boot_formula_neg_code EL n
      (boot_qq_and (semiformula_code EL boot_nat_encoding p)
        (semiformula_code EL boot_nat_encoding q)) =
  boot_qq_or
    (semiformula_code EL boot_nat_encoding (semiformula_neg p))
    (semiformula_code EL boot_nat_encoding (semiformula_neg q)).
Proof.
  intros. rewrite <- boot_qq_and_quote, boot_formula_neg_code_quote.
  reflexivity.
Qed.

Lemma boot_formula_neg_or_quote : forall L n EL
    (p q : semiproposition L n),
  boot_formula_neg_code EL n
      (boot_qq_or (semiformula_code EL boot_nat_encoding p)
        (semiformula_code EL boot_nat_encoding q)) =
  boot_qq_and
    (semiformula_code EL boot_nat_encoding (semiformula_neg p))
    (semiformula_code EL boot_nat_encoding (semiformula_neg q)).
Proof.
  intros. rewrite <- boot_qq_or_quote, boot_formula_neg_code_quote.
  reflexivity.
Qed.

Theorem boot_formula_neg_code_preserves : forall (L : language) n
    (EL : language_encodable L) code,
  boot_is_semiformula EL n code ->
  boot_is_semiformula EL n (boot_formula_neg_code EL n code).
Proof.
  intros. unfold boot_formula_neg_code.
  now apply boot_formula_transform_code_total_preserves.
Qed.

Theorem boot_formula_neg_code_involutive : forall (L : language) n
    (EL : language_encodable L) code,
  boot_is_semiformula EL n code ->
  boot_formula_neg_code EL n (boot_formula_neg_code EL n code) = code.
Proof.
  intros L n EL code Hcode.
  destruct (boot_is_semiformula_has_quote Hcode) as [p Hp].
  rewrite <- Hp. unfold boot_formula_neg_code.
  rewrite !boot_formula_transform_code_total_quote,
    semiformula_neg_involutive. reflexivity.
Qed.

Theorem boot_formula_neg_rewrite : forall L X n Y m EL EY
    (w : rew L X n Y m) (p : semiformula L X n),
  semiformula_code EL EY
    (semiformula_neg (semiformula_rewrite w p)) =
  semiformula_code EL EY
    (semiformula_rewrite w (semiformula_neg p)).
Proof. intros. now rewrite semiformula_rewrite_neg. Qed.
