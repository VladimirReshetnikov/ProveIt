(**
  Structural recognition of bootstrapped formula codes.

  This ports the standard-natural constructor and well-formedness core of
  [Foundation/FirstOrder/Bootstrapping/Syntax/Formula/Basic.lean].  Formula
  recognition is indexed by the permitted number of bound variables, so
  quantifier scope is enforced by the type of the inductive relation rather
  than recovered later from a numerical bound calculation.

  The constructor tags agree exactly with the repository's already verified
  [semiformula_code]: truth, falsity, positive atom, negative atom, and, or,
  universal, existential use tags 0 through 7.  This differs from the
  source's representation-specific permutation of the first four tags.
*)

From Stdlib Require Import Cantor Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Language.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Raw constructors *)

Definition boot_qq_verum : nat := Cantor.to_nat (0, 0).
Definition boot_qq_falsum : nat := Cantor.to_nat (1, 0).

Definition boot_qq_rel (k r args : nat) : nat :=
  Cantor.to_nat (2, Cantor.to_nat (k, Cantor.to_nat (r, args))).

Definition boot_qq_nrel (k r args : nat) : nat :=
  Cantor.to_nat (3, Cantor.to_nat (k, Cantor.to_nat (r, args))).

Definition boot_qq_and (p q : nat) : nat :=
  Cantor.to_nat (4, Cantor.to_nat (p, q)).

Definition boot_qq_or (p q : nat) : nat :=
  Cantor.to_nat (5, Cantor.to_nat (p, q)).

Definition boot_qq_all (p : nat) : nat := Cantor.to_nat (6, p).
Definition boot_qq_exists (p : nat) : nat := Cantor.to_nat (7, p).

Lemma boot_qq_verum_quote : forall L X n EL EX,
  @semiformula_code L X n EL EX (Semiformula_verum n) = boot_qq_verum.
Proof. reflexivity. Qed.

Lemma boot_qq_falsum_quote : forall L X n EL EX,
  @semiformula_code L X n EL EX (Semiformula_falsum n) = boot_qq_falsum.
Proof. reflexivity. Qed.

Lemma boot_qq_rel_quote : forall L X n EL EX k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  semiformula_code EL EX (Semiformula_rel r v) =
  boot_qq_rel k (boot_rel_quote EL r)
    (fin_nat_code (fun i => semiterm_code EL EX (v i))).
Proof. reflexivity. Qed.

Lemma boot_qq_nrel_quote : forall L X n EL EX k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  semiformula_code EL EX (Semiformula_nrel r v) =
  boot_qq_nrel k (boot_rel_quote EL r)
    (fin_nat_code (fun i => semiterm_code EL EX (v i))).
Proof. reflexivity. Qed.

Lemma boot_qq_and_quote : forall L X n EL EX
    (p q : semiformula L X n),
  semiformula_code EL EX (Semiformula_and p q) =
  boot_qq_and (semiformula_code EL EX p) (semiformula_code EL EX q).
Proof. reflexivity. Qed.

Lemma boot_qq_or_quote : forall L X n EL EX
    (p q : semiformula L X n),
  semiformula_code EL EX (Semiformula_or p q) =
  boot_qq_or (semiformula_code EL EX p) (semiformula_code EL EX q).
Proof. reflexivity. Qed.

Lemma boot_qq_all_quote : forall L X n EL EX
    (p : semiformula L X (S n)),
  semiformula_code EL EX (Semiformula_all p) =
  boot_qq_all (semiformula_code EL EX p).
Proof. reflexivity. Qed.

Lemma boot_qq_exists_quote : forall L X n EL EX
    (p : semiformula L X (S n)),
  semiformula_code EL EX (Semiformula_exists p) =
  boot_qq_exists (semiformula_code EL EX p).
Proof. reflexivity. Qed.

(** * Bounded formula recognition *)

Inductive boot_is_semiformula {L : language}
    (EL : language_encodable L) : nat -> nat -> Prop :=
| Boot_formula_verum : forall n,
    boot_is_semiformula EL n boot_qq_verum
| Boot_formula_falsum : forall n,
    boot_is_semiformula EL n boot_qq_falsum
| Boot_formula_rel : forall n k r (v : Fin.t k -> nat),
    language_rel_code_valid EL k r ->
    boot_is_semiterm_vec EL n v ->
    boot_is_semiformula EL n (boot_qq_rel k r (fin_nat_code v))
| Boot_formula_nrel : forall n k r (v : Fin.t k -> nat),
    language_rel_code_valid EL k r ->
    boot_is_semiterm_vec EL n v ->
    boot_is_semiformula EL n (boot_qq_nrel k r (fin_nat_code v))
| Boot_formula_and : forall n p q,
    boot_is_semiformula EL n p ->
    boot_is_semiformula EL n q ->
    boot_is_semiformula EL n (boot_qq_and p q)
| Boot_formula_or : forall n p q,
    boot_is_semiformula EL n p ->
    boot_is_semiformula EL n q ->
    boot_is_semiformula EL n (boot_qq_or p q)
| Boot_formula_all : forall n p,
    boot_is_semiformula EL (S n) p ->
    boot_is_semiformula EL n (boot_qq_all p)
| Boot_formula_exists : forall n p,
    boot_is_semiformula EL (S n) p ->
    boot_is_semiformula EL n (boot_qq_exists p).

Definition boot_is_formula {L} (EL : language_encodable L) : nat -> Prop :=
  boot_is_semiformula EL 0.

Definition boot_is_uformula {L} (EL : language_encodable L)
    (code : nat) : Prop :=
  exists n, boot_is_semiformula EL n code.

Lemma boot_is_semiformula_case_iff : forall L EL n code,
  @boot_is_semiformula L EL n code <->
  code = boot_qq_verum \/
  code = boot_qq_falsum \/
  (exists k r (v : Fin.t k -> nat),
    language_rel_code_valid EL k r /\
    boot_is_semiterm_vec EL n v /\
    code = boot_qq_rel k r (fin_nat_code v)) \/
  (exists k r (v : Fin.t k -> nat),
    language_rel_code_valid EL k r /\
    boot_is_semiterm_vec EL n v /\
    code = boot_qq_nrel k r (fin_nat_code v)) \/
  (exists p q, boot_is_semiformula EL n p /\
    boot_is_semiformula EL n q /\ code = boot_qq_and p q) \/
  (exists p q, boot_is_semiformula EL n p /\
    boot_is_semiformula EL n q /\ code = boot_qq_or p q) \/
  (exists p, boot_is_semiformula EL (S n) p /\ code = boot_qq_all p) \/
  (exists p, boot_is_semiformula EL (S n) p /\
    code = boot_qq_exists p).
Proof.
  intros L EL n code; split.
  - intro H. destruct H as [n | n | n k r v Hr Hv | n k r v Hr Hv |
      n p q Hp Hq | n p q Hp Hq | n p Hp | n p Hp].
    + now left.
    + right; now left.
    + right; right; left. exists k, r, v. now repeat split.
    + right; right; right; left. exists k, r, v. now repeat split.
    + right; right; right; right; left. exists p, q. now repeat split.
    + right; right; right; right; right; left.
      exists p, q. now repeat split.
    + right; right; right; right; right; right; left.
      exists p. now split.
    + right; right; right; right; right; right; right.
      exists p. now split.
  - intros [-> | [-> | [[k [r [v [Hr [Hv ->]]]]] |
      [[k [r [v [Hr [Hv ->]]]]] |
      [[p [q [Hp [Hq ->]]]] |
      [[p [q [Hp [Hq ->]]]] |
      [[p [Hp ->]] | [p [Hp ->]]]]]]]]].
    + apply Boot_formula_verum.
    + apply Boot_formula_falsum.
    + now apply Boot_formula_rel.
    + now apply Boot_formula_nrel.
    + now apply Boot_formula_and.
    + now apply Boot_formula_or.
    + now apply Boot_formula_all.
    + now apply Boot_formula_exists.
Qed.

Lemma boot_is_semiformula_is_uformula : forall L EL n code,
  @boot_is_semiformula L EL n code -> boot_is_uformula EL code.
Proof. intros. now exists n. Qed.

(** * Exact quotation range *)

Theorem semiformula_code_is_semiformula : forall L X n EL EX
    (p : semiformula L X n),
  boot_is_semiformula EL n (semiformula_code EL EX p).
Proof.
  intros L X n EL EX p. induction p.
  - apply Boot_formula_verum.
  - apply Boot_formula_falsum.
  - rewrite boot_qq_rel_quote. apply Boot_formula_rel.
    + exists l. reflexivity.
    + intro i. apply semiterm_code_is_semiterm.
  - rewrite boot_qq_nrel_quote. apply Boot_formula_nrel.
    + exists l. reflexivity.
    + intro i. apply semiterm_code_is_semiterm.
  - rewrite boot_qq_and_quote. now apply Boot_formula_and.
  - rewrite boot_qq_or_quote. now apply Boot_formula_or.
  - rewrite boot_qq_all_quote. now apply Boot_formula_all.
  - rewrite boot_qq_exists_quote. now apply Boot_formula_exists.
Qed.

Theorem boot_is_semiformula_has_quote : forall L EL n code,
  @boot_is_semiformula L EL n code ->
  exists p : semiformula L nat n,
    semiformula_code EL boot_nat_encoding p = code.
Proof.
  intros L EL n code H. induction H as
      [n | n | n k rcode v Hr Hv | n k rcode v Hr Hv |
       n p q Hp IHp Hq IHq | n p q Hp IHp Hq IHq |
       n p Hp IHp | n p Hp IHp].
  - exists (Semiformula_verum n). reflexivity.
  - exists (Semiformula_falsum n). reflexivity.
  - destruct Hr as [r Hr].
    destruct (@fin_forall_exists_choice k (semiterm L nat n)
      (fun i t => semiterm_code EL boot_nat_encoding t = v i)
      (fun i => boot_is_semiterm_has_quote (Hv i))) as [terms Hterms].
    exists (Semiformula_rel r terms). rewrite boot_qq_rel_quote.
    unfold boot_rel_quote. rewrite Hr. f_equal. f_equal.
    apply functional_extensionality. intro i. apply Hterms.
  - destruct Hr as [r Hr].
    destruct (@fin_forall_exists_choice k (semiterm L nat n)
      (fun i t => semiterm_code EL boot_nat_encoding t = v i)
      (fun i => boot_is_semiterm_has_quote (Hv i))) as [terms Hterms].
    exists (Semiformula_nrel r terms). rewrite boot_qq_nrel_quote.
    unfold boot_rel_quote. rewrite Hr. f_equal. f_equal.
    apply functional_extensionality. intro i. apply Hterms.
  - destruct IHp as [p' Hpcode]. destruct IHq as [q' Hqcode].
    exists (Semiformula_and p' q').
    rewrite boot_qq_and_quote, Hpcode, Hqcode. reflexivity.
  - destruct IHp as [p' Hpcode]. destruct IHq as [q' Hqcode].
    exists (Semiformula_or p' q').
    rewrite boot_qq_or_quote, Hpcode, Hqcode. reflexivity.
  - destruct IHp as [p' Hpcode]. exists (Semiformula_all p').
    rewrite boot_qq_all_quote, Hpcode. reflexivity.
  - destruct IHp as [p' Hpcode]. exists (Semiformula_exists p').
    rewrite boot_qq_exists_quote, Hpcode. reflexivity.
Qed.

Theorem boot_is_semiformula_quote_iff : forall L EL n code,
  @boot_is_semiformula L EL n code <->
  exists p : semiformula L nat n,
    semiformula_code EL boot_nat_encoding p = code.
Proof.
  intros; split.
  - apply boot_is_semiformula_has_quote.
  - intros [p <-]. apply semiformula_code_is_semiformula.
Qed.

Theorem boot_is_semiformula_decode_quote : forall L EL n code,
  @boot_is_semiformula L EL n code ->
  exists p : semiformula L nat n,
    semiformula_decode EL boot_nat_encoding n code = Some p /\
    semiformula_code EL boot_nat_encoding p = code.
Proof.
  intros L EL n code H.
  destruct (boot_is_semiformula_has_quote H) as [p Hp].
  exists p. split; [|exact Hp]. rewrite <- Hp.
  apply semiformula_decode_code.
Qed.
