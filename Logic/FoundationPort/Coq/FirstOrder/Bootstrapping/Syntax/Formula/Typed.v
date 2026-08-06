(**
  Typed facade for bootstrapped standard-natural formulas.

  Foundation's nonstandard [Bootstrapping.Semiformula] stores a raw model
  value together with a bounded-code proof.  Coq's native [semiproposition]
  is stronger: its constructors enforce the bound-variable arity directly.
  We therefore expose the source operations over that native type, factoring
  their laws through the generic capture-avoiding rewrite calculus.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import
  Basic Typed.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Functions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition boot_typed_semiformula (L : language) (n : nat) : Type :=
  semiproposition L n.

Definition boot_typed_formula (L : language) : Type := proposition L.

Definition boot_typed_formula_neg {L n}
    (p : boot_typed_semiformula L n) : boot_typed_semiformula L n :=
  semiformula_neg p.

Definition boot_typed_formula_imp {L n}
    (p q : boot_typed_semiformula L n) : boot_typed_semiformula L n :=
  semiformula_imp p q.

Definition boot_typed_formula_iff {L n}
    (p q : boot_typed_semiformula L n) : boot_typed_semiformula L n :=
  semiformula_iff p q.

Definition boot_typed_formula_shift {L n}
    (p : boot_typed_semiformula L n) : boot_typed_semiformula L n :=
  semiformula_shift p.

Definition boot_typed_formula_subst {L n m}
    (v : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L n) : boot_typed_semiformula L m :=
  semiformula_substitute v p.

Definition boot_typed_formula_free {L}
    (p : boot_typed_semiformula L 1) : boot_typed_formula L :=
  @semiformula_free L 0 p.

(** * Boolean operations *)

Lemma boot_typed_formula_neg_involutive : forall L n
    (p : boot_typed_semiformula L n),
  boot_typed_formula_neg (boot_typed_formula_neg p) = p.
Proof. intros. apply semiformula_neg_involutive. Qed.

Lemma boot_typed_formula_neg_inj_iff : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_neg p = boot_typed_formula_neg q <-> p = q.
Proof. intros. apply semiformula_neg_injective. Qed.

Lemma boot_typed_formula_neg_verum : forall L n,
  boot_typed_formula_neg (@Semiformula_verum L nat n) =
  Semiformula_falsum n.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_neg_falsum : forall L n,
  boot_typed_formula_neg (@Semiformula_falsum L nat n) =
  Semiformula_verum n.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_neg_rel : forall L n k
    (r : language_rel L k) (v : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_neg (Semiformula_rel r v) = Semiformula_nrel r v.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_neg_nrel : forall L n k
    (r : language_rel L k) (v : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_neg (Semiformula_nrel r v) = Semiformula_rel r v.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_neg_and : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_neg (Semiformula_and p q) =
  Semiformula_or (boot_typed_formula_neg p) (boot_typed_formula_neg q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_neg_or : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_neg (Semiformula_or p q) =
  Semiformula_and (boot_typed_formula_neg p) (boot_typed_formula_neg q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_neg_all : forall L n
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_neg (Semiformula_all p) =
  Semiformula_exists (boot_typed_formula_neg p).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_neg_exists : forall L n
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_neg (Semiformula_exists p) =
  Semiformula_all (boot_typed_formula_neg p).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_imp_def : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_imp p q =
  Semiformula_or (boot_typed_formula_neg p) q.
Proof. reflexivity. Qed.

(** * Shift equations *)

Lemma boot_typed_formula_shift_verum : forall L n,
  boot_typed_formula_shift (@Semiformula_verum L nat n) =
  Semiformula_verum n.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_shift_falsum : forall L n,
  boot_typed_formula_shift (@Semiformula_falsum L nat n) =
  Semiformula_falsum n.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_shift_rel : forall L n k
    (r : language_rel L k) (v : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_shift (Semiformula_rel r v) =
  Semiformula_rel r (fun i => boot_typed_shift (v i)).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_shift_nrel : forall L n k
    (r : language_rel L k) (v : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_shift (Semiformula_nrel r v) =
  Semiformula_nrel r (fun i => boot_typed_shift (v i)).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_shift_and : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_shift (Semiformula_and p q) =
  Semiformula_and (boot_typed_formula_shift p)
    (boot_typed_formula_shift q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_shift_or : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_shift (Semiformula_or p q) =
  Semiformula_or (boot_typed_formula_shift p)
    (boot_typed_formula_shift q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_shift_all : forall L n
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_shift (Semiformula_all p) =
  Semiformula_all (boot_typed_formula_shift p).
Proof.
  intros. unfold boot_typed_formula_shift, semiformula_shift. simpl. f_equal.
  apply semiformula_rewrite_ext, rew_q_shift.
Qed.

Lemma boot_typed_formula_shift_exists : forall L n
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_shift (Semiformula_exists p) =
  Semiformula_exists (boot_typed_formula_shift p).
Proof.
  intros. unfold boot_typed_formula_shift, semiformula_shift. simpl. f_equal.
  apply semiformula_rewrite_ext, rew_q_shift.
Qed.

Lemma boot_typed_formula_shift_neg : forall L n
    (p : boot_typed_semiformula L n),
  boot_typed_formula_shift (boot_typed_formula_neg p) =
  boot_typed_formula_neg (boot_typed_formula_shift p).
Proof. intros. apply semiformula_rewrite_neg. Qed.

Lemma boot_typed_formula_shift_imp : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_shift (boot_typed_formula_imp p q) =
  boot_typed_formula_imp (boot_typed_formula_shift p)
    (boot_typed_formula_shift q).
Proof.
  intros. unfold boot_typed_formula_shift, boot_typed_formula_imp,
    boot_typed_formula_neg, semiformula_shift, semiformula_imp. simpl.
  now rewrite semiformula_rewrite_neg.
Qed.

Lemma boot_typed_formula_shift_iff : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_shift (boot_typed_formula_iff p q) =
  boot_typed_formula_iff (boot_typed_formula_shift p)
    (boot_typed_formula_shift q).
Proof.
  intros. unfold boot_typed_formula_shift, boot_typed_formula_iff,
    boot_typed_formula_imp, boot_typed_formula_neg, semiformula_shift,
    semiformula_iff, semiformula_imp. simpl.
  now rewrite !semiformula_rewrite_neg.
Qed.

(** * Simultaneous substitution *)

Lemma boot_typed_q_subst_equiv : forall L n m
    (v : boot_typed_semiterm_vec L n m),
  rew_equiv (rew_subst (boot_typed_q v)) (rew_q (rew_subst v)).
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i. apply boot_typed_q_as_rew_q.
  - intro x. reflexivity.
Qed.

Lemma boot_typed_formula_subst_verum : forall L n m
    (v : boot_typed_semiterm_vec L n m),
  boot_typed_formula_subst v (@Semiformula_verum L nat n) =
  Semiformula_verum m.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_subst_falsum : forall L n m
    (v : boot_typed_semiterm_vec L n m),
  boot_typed_formula_subst v (@Semiformula_falsum L nat n) =
  Semiformula_falsum m.
Proof. reflexivity. Qed.

Lemma boot_typed_formula_subst_rel : forall L n m k
    (v : boot_typed_semiterm_vec L n m)
    (r : language_rel L k) (args : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_subst v (Semiformula_rel r args) =
  Semiformula_rel r (fun i => boot_typed_subst v (args i)).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_subst_nrel : forall L n m k
    (v : boot_typed_semiterm_vec L n m)
    (r : language_rel L k) (args : Fin.t k -> syntactic_semiterm L n),
  boot_typed_formula_subst v (Semiformula_nrel r args) =
  Semiformula_nrel r (fun i => boot_typed_subst v (args i)).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_subst_and : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_subst v (Semiformula_and p q) =
  Semiformula_and (boot_typed_formula_subst v p)
    (boot_typed_formula_subst v q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_subst_or : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_subst v (Semiformula_or p q) =
  Semiformula_or (boot_typed_formula_subst v p)
    (boot_typed_formula_subst v q).
Proof. reflexivity. Qed.

Lemma boot_typed_formula_subst_all : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_subst v (Semiformula_all p) =
  Semiformula_all (boot_typed_formula_subst (boot_typed_q v) p).
Proof.
  intros. unfold boot_typed_formula_subst, semiformula_substitute. simpl.
  f_equal.
Qed.

Lemma boot_typed_formula_subst_exists : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)),
  boot_typed_formula_subst v (Semiformula_exists p) =
  Semiformula_exists (boot_typed_formula_subst (boot_typed_q v) p).
Proof.
  intros. unfold boot_typed_formula_subst, semiformula_substitute. simpl.
  f_equal.
Qed.

Lemma boot_typed_formula_subst_neg : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L n),
  boot_typed_formula_subst v (boot_typed_formula_neg p) =
  boot_typed_formula_neg (boot_typed_formula_subst v p).
Proof. intros. apply semiformula_rewrite_neg. Qed.

Lemma boot_typed_formula_subst_imp : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_subst v (boot_typed_formula_imp p q) =
  boot_typed_formula_imp (boot_typed_formula_subst v p)
    (boot_typed_formula_subst v q).
Proof.
  intros. unfold boot_typed_formula_subst, boot_typed_formula_imp,
    boot_typed_formula_neg, semiformula_substitute, semiformula_imp. simpl.
  now rewrite semiformula_rewrite_neg.
Qed.

Theorem boot_typed_formula_subst_id : forall L n
    (p : boot_typed_semiformula L n),
  boot_typed_formula_subst (fun i => Semiterm_bvar i) p = p.
Proof. intros. apply semiformula_substitute_id. Qed.

Theorem boot_typed_formula_subst_subst : forall L n m l
    (v : boot_typed_semiterm_vec L n m)
    (w : boot_typed_semiterm_vec L m l)
    (p : boot_typed_semiformula L n),
  boot_typed_formula_subst w (boot_typed_formula_subst v p) =
  boot_typed_formula_subst (fun i => boot_typed_subst w (v i)) p.
Proof. intros. apply semiformula_substitute_comp. Qed.

Theorem boot_typed_formula_shift_subst : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L n),
  boot_typed_formula_shift (boot_typed_formula_subst v p) =
  boot_typed_formula_subst (fun i => boot_typed_shift (v i))
    (boot_typed_formula_shift p).
Proof.
  intros. unfold boot_typed_formula_shift, boot_typed_formula_subst,
    semiformula_shift, semiformula_substitute.
  rewrite <- !semiformula_rewrite_comp.
  apply semiformula_rewrite_ext, rew_shift_comp_subst.
Qed.

(** The source defines freeing as shift followed by singleton substitution.
    The generic calculus proves that implementation equal to [rew_free]. *)
Lemma boot_typed_formula_free_as_shift_subst : forall L
    (p : boot_typed_semiformula L 1),
  boot_typed_formula_free p =
  boot_typed_formula_subst (fun _ : Fin.t 1 => Semiterm_fvar 0)
    (boot_typed_formula_shift p).
Proof.
  intros. symmetry. apply semiformula_substitute_shift_one_eq_free.
Qed.

Lemma boot_typed_formula_free_neg : forall L
    (p : boot_typed_semiformula L 1),
  boot_typed_formula_free (boot_typed_formula_neg p) =
  boot_typed_formula_neg (boot_typed_formula_free p).
Proof. intros. apply semiformula_free_neg. Qed.

(** * Free-variable-freeness *)

Definition boot_typed_formula_fv_free {L n}
    (p : boot_typed_semiformula L n) : Prop :=
  boot_typed_formula_shift p = p.

Lemma boot_typed_formula_fv_free_verum : forall L n,
  boot_typed_formula_fv_free (@Semiformula_verum L nat n).
Proof. intros. unfold boot_typed_formula_fv_free. apply boot_typed_formula_shift_verum. Qed.

Lemma boot_typed_formula_fv_free_falsum : forall L n,
  boot_typed_formula_fv_free (@Semiformula_falsum L nat n).
Proof. intros. unfold boot_typed_formula_fv_free. apply boot_typed_formula_shift_falsum. Qed.

Lemma boot_typed_formula_fv_free_and_iff : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_fv_free (Semiformula_and p q) <->
  boot_typed_formula_fv_free p /\ boot_typed_formula_fv_free q.
Proof.
  intros. unfold boot_typed_formula_fv_free.
  rewrite boot_typed_formula_shift_and. apply semiformula_and_injective.
Qed.

Lemma boot_typed_formula_fv_free_or_iff : forall L n
    (p q : boot_typed_semiformula L n),
  boot_typed_formula_fv_free (Semiformula_or p q) <->
  boot_typed_formula_fv_free p /\ boot_typed_formula_fv_free q.
Proof.
  intros. unfold boot_typed_formula_fv_free.
  rewrite boot_typed_formula_shift_or. apply semiformula_or_injective.
Qed.

Lemma boot_typed_formula_fv_free_neg_iff : forall L n
    (p : boot_typed_semiformula L n),
  boot_typed_formula_fv_free (boot_typed_formula_neg p) <->
  boot_typed_formula_fv_free p.
Proof.
  intros. unfold boot_typed_formula_fv_free.
  rewrite boot_typed_formula_shift_neg. apply semiformula_neg_injective.
Qed.

(** * Compatibility with executable codes *)

Lemma boot_typed_formula_subst_code : forall L n m EL
    (v : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L n),
  boot_formula_subst_code EL v
      (semiformula_code EL boot_nat_encoding p) =
  semiformula_code EL boot_nat_encoding (boot_typed_formula_subst v p).
Proof. intros. apply boot_formula_subst_code_quote. Qed.

Lemma boot_typed_formula_shift_code : forall L n EL
    (p : boot_typed_semiformula L n),
  boot_formula_shift_code EL n
      (semiformula_code EL boot_nat_encoding p) =
  semiformula_code EL boot_nat_encoding (boot_typed_formula_shift p).
Proof. intros. apply boot_formula_shift_code_quote. Qed.

Lemma boot_typed_formula_neg_code : forall L n EL
    (p : boot_typed_semiformula L n),
  boot_formula_neg_code EL n
      (semiformula_code EL boot_nat_encoding p) =
  semiformula_code EL boot_nat_encoding (boot_typed_formula_neg p).
Proof. intros. apply boot_formula_neg_code_quote. Qed.
