(**
  Executable substitution operators used by syntactic diagonalization.

  Foundation defines these operations inside arbitrary nonstandard models of
  arithmetic and proves their quotation equations.  This module isolates the
  complete standard-natural computational core.  The definitions are
  deliberately more general than the arithmetic source: they work for every
  encodable first-order language and every chosen family of closed terms.

  All capture avoidance is inherited from the checked generic rewrite engine.
  Consequently the three source quotation laws and well-formedness theorems
  are short specializations of one simultaneous-substitution theorem rather
  than separate recursions over raw formula codes.
*)

From Stdlib Require Import Logic.FunctionalExtensionality Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Syntax.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Functions Typed Coding.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Substitution of one distinguished closed term *)

Definition boot_subst_numeral_code {L}
    (EL : language_encodable L)
    (numeral : forall n, nat -> syntactic_semiterm L n)
    (formula x : nat) : nat :=
  boot_formula_subst_code EL
    (fun _ : Fin.t 1 => numeral 0 x) formula.

Lemma boot_subst_numeral_code_def : forall L EL numeral formula x,
  @boot_subst_numeral_code L EL numeral formula x =
  boot_formula_subst_code EL
    (fun _ : Fin.t 1 => numeral 0 x) formula.
Proof. reflexivity. Qed.

Lemma boot_subst_numeral_code_quote : forall L EL numeral
    (p : boot_typed_semiformula L 1) x,
  boot_subst_numeral_code EL numeral
      (boot_typed_formula_quote EL p) x =
  boot_typed_formula_quote EL
    (boot_typed_formula_subst (fun _ : Fin.t 1 => numeral 0 x) p).
Proof.
  intros. unfold boot_subst_numeral_code, boot_typed_formula_quote.
  apply boot_formula_subst_code_quote.
Qed.

(** The argument substituted into a formula may itself be the code of syntax
    of any arity.  The source only needs the unary instance. *)
Lemma boot_subst_numeral_code_quote_quote : forall L EL numeral r
    (p : boot_typed_semiformula L 1)
    (q : boot_typed_semiformula L r),
  boot_subst_numeral_code EL numeral
      (boot_typed_formula_quote EL p)
      (boot_typed_formula_quote EL q) =
  boot_typed_formula_quote EL
    (boot_typed_formula_subst
      (fun _ : Fin.t 1 =>
        numeral 0 (boot_typed_formula_quote EL q)) p).
Proof. intros. apply boot_subst_numeral_code_quote. Qed.

Theorem boot_subst_numeral_code_recognized : forall L EL numeral formula x,
  @boot_is_semiformula L EL 1 formula ->
  boot_is_semiformula EL 0
    (boot_subst_numeral_code EL numeral formula x).
Proof.
  intros. unfold boot_subst_numeral_code.
  now apply boot_formula_subst_code_preserves.
Qed.

(** * Simultaneous substitution of distinguished closed terms *)

Definition boot_subst_numerals_code {L k}
    (EL : language_encodable L)
    (numeral : forall n, nat -> syntactic_semiterm L n)
    (formula : nat) (values : Fin.t k -> nat) : nat :=
  boot_formula_subst_code EL
    (fun i => numeral 0 (values i)) formula.

Lemma boot_subst_numerals_code_def : forall L k EL numeral formula values,
  @boot_subst_numerals_code L k EL numeral formula values =
  boot_formula_subst_code EL
    (fun i => numeral 0 (values i)) formula.
Proof. reflexivity. Qed.

Lemma boot_subst_numerals_code_quote : forall L k EL numeral
    (p : boot_typed_semiformula L k) (values : Fin.t k -> nat),
  boot_subst_numerals_code EL numeral
      (boot_typed_formula_quote EL p) values =
  boot_typed_formula_quote EL
    (boot_typed_formula_subst (fun i => numeral 0 (values i)) p).
Proof.
  intros. unfold boot_subst_numerals_code, boot_typed_formula_quote.
  apply boot_formula_subst_code_quote.
Qed.

(** This is the exact standard counterpart of Foundation's
    [substNumerals_app_quote_quote], generalized so the quoted family may
    have any common arity. *)
Lemma boot_subst_numerals_code_quote_quote : forall L k r EL numeral
    (p : boot_typed_semiformula L k)
    (q : Fin.t k -> boot_typed_semiformula L r),
  boot_subst_numerals_code EL numeral
      (boot_typed_formula_quote EL p)
      (fun i => boot_typed_formula_quote EL (q i)) =
  boot_typed_formula_quote EL
    (boot_typed_formula_subst
      (fun i => numeral 0 (boot_typed_formula_quote EL (q i))) p).
Proof. intros. apply boot_subst_numerals_code_quote. Qed.

Theorem boot_subst_numerals_code_recognized : forall L k EL numeral
    formula (values : Fin.t k -> nat),
  @boot_is_semiformula L EL k formula ->
  boot_is_semiformula EL 0
    (boot_subst_numerals_code EL numeral formula values).
Proof.
  intros. unfold boot_subst_numerals_code.
  now apply boot_formula_subst_code_preserves.
Qed.

(** Unary simultaneous substitution is definitionally the single-argument
    operation; no finite-vector extensionality or equality decision is needed. *)
Lemma boot_subst_numeral_code_as_numerals : forall L EL numeral formula x,
  @boot_subst_numeral_code L EL numeral formula x =
  boot_subst_numerals_code EL numeral formula
    (fun _ : Fin.t 1 => x).
Proof. reflexivity. Qed.

(** * Substitution preserving a parameter tail *)

Definition boot_subst_numeral_params_code {L}
    (EL : language_encodable L)
    (numeral : forall n, nat -> syntactic_semiterm L n)
    (k formula x : nat) : nat :=
  boot_formula_subst_code EL
    (fin_coding_cons (numeral k x)
      (fun i : Fin.t k => @Semiterm_bvar L nat k i)) formula.

Lemma boot_subst_numeral_params_code_def : forall L EL numeral k formula x,
  @boot_subst_numeral_params_code L EL numeral k formula x =
  boot_formula_subst_code EL
    (fin_coding_cons (numeral k x)
      (fun i : Fin.t k => @Semiterm_bvar L nat k i)) formula.
Proof. reflexivity. Qed.

Lemma boot_subst_numeral_params_code_quote : forall L EL numeral k
    (p : boot_typed_semiformula L (S k)) x,
  boot_subst_numeral_params_code EL numeral k
      (boot_typed_formula_quote EL p) x =
  boot_typed_formula_quote EL
    (boot_typed_formula_subst
      (fin_coding_cons (numeral k x)
        (fun i : Fin.t k => @Semiterm_bvar L nat k i)) p).
Proof.
  intros. unfold boot_subst_numeral_params_code,
    boot_typed_formula_quote.
  apply boot_formula_subst_code_quote.
Qed.

Lemma boot_subst_numeral_params_code_quote_quote : forall L EL numeral k r
    (p : boot_typed_semiformula L (S k))
    (q : boot_typed_semiformula L r),
  boot_subst_numeral_params_code EL numeral k
      (boot_typed_formula_quote EL p)
      (boot_typed_formula_quote EL q) =
  boot_typed_formula_quote EL
    (boot_typed_formula_subst
      (fin_coding_cons
        (numeral k (boot_typed_formula_quote EL q))
        (fun i : Fin.t k => @Semiterm_bvar L nat k i)) p).
Proof. intros. apply boot_subst_numeral_params_code_quote. Qed.

Theorem boot_subst_numeral_params_code_recognized : forall L EL numeral k
    formula x,
  @boot_is_semiformula L EL (S k) formula ->
  boot_is_semiformula EL k
    (boot_subst_numeral_params_code EL numeral k formula x).
Proof.
  intros. unfold boot_subst_numeral_params_code.
  now apply boot_formula_subst_code_preserves.
Qed.

(** With no retained parameters the parameterized operation reduces to the
    one-variable operation.  This convenience equation uses function
    extensionality to identify the two singleton vectors.  The quotation and
    recognition laws inherit only the finite-vector extensionality already
    exposed by the generic formula rewrite/coding layer; no classical choice
    or excluded middle is added here. *)
Lemma boot_subst_numeral_params_zero : forall L EL numeral formula x,
  @boot_subst_numeral_params_code L EL numeral 0 formula x =
  boot_subst_numeral_code EL numeral formula x.
Proof.
  intros. unfold boot_subst_numeral_params_code,
    boot_subst_numeral_code. f_equal.
  apply functional_extensionality. intro i.
  refine (@Fin.caseS' 0 i (fun j =>
    fin_coding_cons (numeral 0 x)
      (fun q : Fin.t 0 => @Semiterm_bvar L nat 0 q) j = numeral 0 x)
    eq_refl _).
  intros q; inversion q.
Qed.

(** * Ordered-ring specialization *)

Definition boot_arithmetic_numeral
    (n : nat) : nat -> syntactic_semiterm oring_language n :=
  @arithmetic_numeral_term nat n.

Definition boot_arithmetic_subst_numeral (formula x : nat) : nat :=
  boot_subst_numeral_code oring_language_encodable
    boot_arithmetic_numeral formula x.

Definition boot_arithmetic_subst_numerals {k}
    (formula : nat) (values : Fin.t k -> nat) : nat :=
  boot_subst_numerals_code oring_language_encodable
    boot_arithmetic_numeral formula values.

Definition boot_arithmetic_subst_numeral_params
    (k formula x : nat) : nat :=
  boot_subst_numeral_params_code oring_language_encodable
    boot_arithmetic_numeral k formula x.

Lemma boot_arithmetic_subst_numeral_quote : forall
    (p : boot_typed_semiformula oring_language 1) x,
  boot_arithmetic_subst_numeral
      (boot_typed_formula_quote oring_language_encodable p) x =
  boot_typed_formula_quote oring_language_encodable
    (boot_typed_formula_subst
      (fun _ : Fin.t 1 => @arithmetic_numeral_term nat 0 x) p).
Proof. intros. apply boot_subst_numeral_code_quote. Qed.

Lemma boot_arithmetic_subst_numerals_quote : forall k
    (p : boot_typed_semiformula oring_language k)
    (values : Fin.t k -> nat),
  boot_arithmetic_subst_numerals
      (boot_typed_formula_quote oring_language_encodable p) values =
  boot_typed_formula_quote oring_language_encodable
    (boot_typed_formula_subst
      (fun i => @arithmetic_numeral_term nat 0 (values i)) p).
Proof. intros. apply boot_subst_numerals_code_quote. Qed.

Lemma boot_arithmetic_subst_numeral_params_quote : forall k
    (p : boot_typed_semiformula oring_language (S k)) x,
  boot_arithmetic_subst_numeral_params k
      (boot_typed_formula_quote oring_language_encodable p) x =
  boot_typed_formula_quote oring_language_encodable
    (boot_typed_formula_subst
      (fin_coding_cons (@arithmetic_numeral_term nat k x)
        (fun i : Fin.t k =>
          @Semiterm_bvar oring_language nat k i)) p).
Proof. intros. apply boot_subst_numeral_params_code_quote. Qed.

(** The concrete diagonal, multi-diagonal, and parameterized diagonal
    constructions require an arithmetic formula representing the substitution
    graph in nonstandard models.  Their representation-independent theorem
    content is supplied by [pa_diagonalization] in
    [FirstOrder/Incompleteness/ProvabilityAbstraction.v]; this module does not
    postulate that missing graph formula. *)
