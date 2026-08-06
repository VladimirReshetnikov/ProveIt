(**
  Executable transformations of bootstrapped term codes.

  This ports the standard-natural computational core of
  [Foundation/FirstOrder/Bootstrapping/Syntax/Term/Functions.lean].  One
  generic decode--rewrite--encode operation factors substitution, free
  variable shift, and bound-variable shift.  It is totalized only after its
  option-valued semantics is exposed; all mathematical laws are exact on the
  recognized-code domain, where the arbitrary invalid-code default is
  unreachable.
*)

From Stdlib Require Import Lia Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The generic code rewrite *)

Definition boot_rewrite_code {L X Y n m}
    (EL : language_encodable L) (EX : encoding X) (EY : encoding Y)
    (w : rew L X n Y m) (code : nat) : option nat :=
  match semiterm_decode EL EX n code with
  | Some t => Some (semiterm_code EL EY (rew_apply w t))
  | None => None
  end.

Definition boot_rewrite_code_total {L X Y n m}
    (EL : language_encodable L) (EX : encoding X) (EY : encoding Y)
    (w : rew L X n Y m) (code : nat) : nat :=
  match boot_rewrite_code EL EX EY w code with
  | Some result => result
  | None => 0
  end.

Lemma boot_rewrite_code_quote : forall L X Y n m EL EX EY
    (w : rew L X n Y m) (t : semiterm L X n),
  boot_rewrite_code EL EX EY w (semiterm_code EL EX t) =
  Some (semiterm_code EL EY (rew_apply w t)).
Proof.
  intros. unfold boot_rewrite_code. now rewrite semiterm_decode_code.
Qed.

Lemma boot_rewrite_code_total_quote : forall L X Y n m EL EX EY
    (w : rew L X n Y m) (t : semiterm L X n),
  boot_rewrite_code_total EL EX EY w (semiterm_code EL EX t) =
  semiterm_code EL EY (rew_apply w t).
Proof.
  intros. unfold boot_rewrite_code_total.
  now rewrite boot_rewrite_code_quote.
Qed.

Lemma boot_rewrite_code_some_iff : forall L X Y n m EL EX EY
    (w : rew L X n Y m) code result,
  boot_rewrite_code EL EX EY w code = Some result <->
  exists t : semiterm L X n,
    semiterm_decode EL EX n code = Some t /\
    result = semiterm_code EL EY (rew_apply w t).
Proof.
  intros L X Y n m EL EX EY w code result.
  unfold boot_rewrite_code.
  destruct (semiterm_decode EL EX n code) as [t|] eqn:Hdecode.
  - split.
    + intro H. injection H as Hresult. exists t. now split.
    + intros [u [Hu ->]]. injection Hu as <-.
      reflexivity.
  - split; [discriminate|]. intros [t [Ht _]].
    discriminate Ht.
Qed.

Lemma boot_is_semiterm_decode_quote : forall L EL n code,
  @boot_is_semiterm L EL n code ->
  exists t : semiterm L nat n,
    semiterm_decode EL boot_nat_encoding n code = Some t /\
    semiterm_code EL boot_nat_encoding t = code.
Proof.
  intros L EL n code H.
  destruct (boot_is_semiterm_has_quote H) as [t Hcode].
  exists t. split; [|exact Hcode].
  rewrite <- Hcode. apply semiterm_decode_code.
Qed.

Theorem boot_rewrite_code_total_preserves : forall L Y n m EL EY
    (w : rew L nat n Y m) code,
  boot_is_semiterm EL n code ->
  boot_is_semiterm EL m
    (boot_rewrite_code_total EL boot_nat_encoding EY w code).
Proof.
  intros L Y n m EL EY w code Hcode.
  destruct (boot_is_semiterm_has_quote Hcode) as [t Ht].
  rewrite <- Ht, boot_rewrite_code_total_quote.
  apply semiterm_code_is_semiterm.
Qed.

Theorem boot_rewrite_code_total_ext : forall L X Y n m EL EX EY
    (w v : rew L X n Y m),
  rew_equiv w v -> forall t : semiterm L X n,
  boot_rewrite_code_total EL EX EY w (semiterm_code EL EX t) =
  boot_rewrite_code_total EL EX EY v (semiterm_code EL EX t).
Proof.
  intros L X Y n m EL EX EY w v H t.
  rewrite !boot_rewrite_code_total_quote. now rewrite H.
Qed.

Theorem boot_rewrite_code_total_comp : forall L X Y Z n m l
    EL EX EY EZ (v : rew L Y m Z l) (w : rew L X n Y m)
    (t : semiterm L X n),
  boot_rewrite_code_total EL EY EZ v
    (boot_rewrite_code_total EL EX EY w (semiterm_code EL EX t)) =
  boot_rewrite_code_total EL EX EZ (rew_comp v w)
    (semiterm_code EL EX t).
Proof.
  intros. rewrite !boot_rewrite_code_total_quote. reflexivity.
Qed.

(** * Substitution *)

Definition boot_term_subst_code {L n m}
    (EL : language_encodable L)
    (v : Fin.t n -> syntactic_semiterm L m) (code : nat) : nat :=
  boot_rewrite_code_total EL boot_nat_encoding boot_nat_encoding
    (rew_subst v) code.

Lemma boot_term_subst_code_quote : forall L n m EL
    (v : Fin.t n -> syntactic_semiterm L m)
    (t : syntactic_semiterm L n),
  boot_term_subst_code EL v (semiterm_code EL boot_nat_encoding t) =
  semiterm_code EL boot_nat_encoding (rew_apply (rew_subst v) t).
Proof. intros. apply boot_rewrite_code_total_quote. Qed.

Lemma boot_term_subst_code_bvar : forall L n m EL
    (v : Fin.t n -> syntactic_semiterm L m) (i : Fin.t n),
  boot_term_subst_code EL v (boot_qq_bvar (fin_value i)) =
  semiterm_code EL boot_nat_encoding (v i).
Proof.
  intros L n m EL v i.
  rewrite <- (@boot_qq_bvar_quote L nat n EL boot_nat_encoding i),
    boot_term_subst_code_quote, rew_subst_bvar. reflexivity.
Qed.

Lemma boot_term_subst_code_fvar : forall L n m EL
    (v : Fin.t n -> syntactic_semiterm L m) x,
  boot_term_subst_code EL v (boot_qq_fvar x) = boot_qq_fvar x.
Proof.
  intros L n m EL v x.
  change (boot_term_subst_code EL v
    (@semiterm_code L nat n EL boot_nat_encoding (Semiterm_fvar x)) =
    @semiterm_code L nat m EL boot_nat_encoding (Semiterm_fvar x)).
  rewrite boot_term_subst_code_quote, rew_subst_fvar. reflexivity.
Qed.

Lemma boot_term_subst_code_func : forall L n m EL k
    (v : Fin.t n -> syntactic_semiterm L m)
    (f : language_func L k) (args : Fin.t k -> syntactic_semiterm L n),
  boot_term_subst_code EL v
      (semiterm_code EL boot_nat_encoding (Semiterm_func f args)) =
  semiterm_code EL boot_nat_encoding
    (Semiterm_func f (fun i => rew_apply (rew_subst v) (args i))).
Proof.
  intros. rewrite boot_term_subst_code_quote, rew_apply_func. reflexivity.
Qed.

Theorem boot_term_subst_code_preserves : forall L n m EL
    (v : Fin.t n -> syntactic_semiterm L m) code,
  boot_is_semiterm EL n code ->
  boot_is_semiterm EL m (boot_term_subst_code EL v code).
Proof.
  intros. unfold boot_term_subst_code.
  now apply boot_rewrite_code_total_preserves.
Qed.

Theorem boot_term_subst_code_comp : forall L n m l EL
    (v : Fin.t n -> syntactic_semiterm L m)
    (w : Fin.t m -> syntactic_semiterm L l)
    (t : syntactic_semiterm L n),
  boot_term_subst_code EL w
    (boot_term_subst_code EL v
      (semiterm_code EL boot_nat_encoding t)) =
  boot_term_subst_code EL
    (fun i => rew_apply (rew_subst w) (v i))
    (semiterm_code EL boot_nat_encoding t).
Proof.
  intros. rewrite !boot_term_subst_code_quote.
  apply f_equal. exact (@rew_subst_comp_subst L nat n m l v w t).
Qed.

(** * Shifting free and bound variables *)

Definition boot_term_shift_code {L} (EL : language_encodable L)
    (n code : nat) : nat :=
  boot_rewrite_code_total EL boot_nat_encoding boot_nat_encoding
    (@rew_shift L n) code.

Definition boot_term_bshift_code {L X} (EL : language_encodable L)
    (EX : encoding X) (n code : nat) : nat :=
  boot_rewrite_code_total EL EX EX (@rew_bshift L X n) code.

Lemma boot_term_shift_code_quote : forall L n EL
    (t : syntactic_semiterm L n),
  boot_term_shift_code EL n (semiterm_code EL boot_nat_encoding t) =
  semiterm_code EL boot_nat_encoding (rew_apply rew_shift t).
Proof. intros. apply boot_rewrite_code_total_quote. Qed.

Lemma boot_term_bshift_code_quote : forall L X n EL EX
    (t : semiterm L X n),
  boot_term_bshift_code EL EX n (semiterm_code EL EX t) =
  semiterm_code EL EX (rew_apply rew_bshift t).
Proof. intros. apply boot_rewrite_code_total_quote. Qed.

Lemma boot_term_shift_code_bvar : forall (L : language) n
    (EL : language_encodable L) (i : Fin.t n),
  boot_term_shift_code EL n (boot_qq_bvar (fin_value i)) =
  boot_qq_bvar (fin_value i).
Proof.
  intros L n EL i.
  rewrite <- (@boot_qq_bvar_quote L nat n EL boot_nat_encoding i),
    boot_term_shift_code_quote, rew_shift_bvar. reflexivity.
Qed.

Lemma boot_term_shift_code_fvar : forall (L : language) n
    (EL : language_encodable L) x,
  boot_term_shift_code EL n (boot_qq_fvar x) = boot_qq_fvar (S x).
Proof.
  intros L n EL x.
  change (boot_term_shift_code EL n
    (@semiterm_code L nat n EL boot_nat_encoding (Semiterm_fvar x)) =
    @semiterm_code L nat n EL boot_nat_encoding (Semiterm_fvar (S x))).
  rewrite boot_term_shift_code_quote, rew_shift_fvar. reflexivity.
Qed.

Lemma boot_term_bshift_code_bvar : forall (L : language) X n
    (EL : language_encodable L) (EX : encoding X) (i : Fin.t n),
  boot_term_bshift_code EL EX n (boot_qq_bvar (fin_value i)) =
  boot_qq_bvar (fin_value (Fin.FS i)).
Proof.
  intros L X n EL EX i.
  rewrite <- (@boot_qq_bvar_quote L X n EL EX i),
    boot_term_bshift_code_quote, rew_bshift_bvar. reflexivity.
Qed.

Lemma boot_term_bshift_code_fvar : forall (L : language) X n
    (EL : language_encodable L) (EX : encoding X) (x : X),
  boot_term_bshift_code EL EX n (boot_qq_fvar (encode EX x)) =
  boot_qq_fvar (encode EX x).
Proof.
  intros L X n EL EX x.
  rewrite <- (@boot_qq_fvar_quote L X n EL EX x),
    boot_term_bshift_code_quote, rew_bshift_fvar. reflexivity.
Qed.

Theorem boot_term_shift_code_preserves : forall (L : language) n
    (EL : language_encodable L) code,
  @boot_is_semiterm L EL n code ->
  boot_is_semiterm EL n (boot_term_shift_code EL n code).
Proof.
  intros. unfold boot_term_shift_code.
  now apply boot_rewrite_code_total_preserves.
Qed.

Theorem boot_term_bshift_code_preserves : forall (L : language) n
    (EL : language_encodable L) code,
  @boot_is_semiterm L EL n code ->
  boot_is_semiterm EL (S n)
    (boot_term_bshift_code EL boot_nat_encoding n code).
Proof.
  intros. unfold boot_term_bshift_code.
  now apply boot_rewrite_code_total_preserves.
Qed.

Lemma rew_bshift_shift_comm : forall L n,
  rew_equiv
    (rew_comp (@rew_bshift L nat n) (@rew_shift L n))
    (rew_comp (@rew_shift L (S n)) (@rew_bshift L nat n)).
Proof.
  intros. apply rew_equiv_of_variables; intros; reflexivity.
Qed.

Theorem boot_term_bshift_shift_comm : forall L n EL
    (t : syntactic_semiterm L n),
  boot_term_bshift_code EL boot_nat_encoding n
    (boot_term_shift_code EL n (semiterm_code EL boot_nat_encoding t)) =
  boot_term_shift_code EL (S n)
    (boot_term_bshift_code EL boot_nat_encoding n
      (semiterm_code EL boot_nat_encoding t)).
Proof.
  intros. unfold boot_term_bshift_code, boot_term_shift_code.
  rewrite !boot_rewrite_code_total_quote.
  apply f_equal. apply rew_bshift_shift_comm.
Qed.

Theorem boot_term_shift_subst : forall L n m EL
    (v : Fin.t n -> syntactic_semiterm L m)
    (t : syntactic_semiterm L n),
  boot_term_shift_code EL m
    (boot_term_subst_code EL v
      (semiterm_code EL boot_nat_encoding t)) =
  boot_term_subst_code EL
    (fun i => rew_apply rew_shift (v i))
    (boot_term_shift_code EL n (semiterm_code EL boot_nat_encoding t)).
Proof.
  intros. unfold boot_term_shift_code, boot_term_subst_code.
  rewrite !boot_rewrite_code_total_quote.
  apply f_equal. exact (@rew_shift_comp_subst L n m v t).
Qed.

(** Free-variable-freeness is represented directly by shift invariance. *)
Definition boot_term_fv_free {L n} (t : syntactic_semiterm L n) : Prop :=
  rew_apply rew_shift t = t.

Lemma boot_term_fv_free_bvar : forall L n (i : Fin.t n),
  boot_term_fv_free (@Semiterm_bvar L nat n i).
Proof. intros. unfold boot_term_fv_free. apply rew_shift_bvar. Qed.

Lemma boot_term_fv_free_fvar : forall L n x,
  ~ boot_term_fv_free (@Semiterm_fvar L nat n x).
Proof.
  intros L n x H. unfold boot_term_fv_free in H.
  rewrite rew_shift_fvar in H. injection H as Hx. lia.
Qed.

Lemma boot_term_fv_free_bshift : forall L n
    (t : syntactic_semiterm L n),
  boot_term_fv_free t ->
  boot_term_fv_free (rew_apply rew_bshift t).
Proof.
  intros L n t H. unfold boot_term_fv_free in *.
  change (rew_apply (rew_comp rew_shift rew_bshift) t =
    rew_apply rew_bshift t).
  rewrite <- (@rew_bshift_shift_comm L n t).
  change (rew_apply rew_bshift (rew_apply rew_shift t) =
    rew_apply rew_bshift t).
  now rewrite H.
Qed.
