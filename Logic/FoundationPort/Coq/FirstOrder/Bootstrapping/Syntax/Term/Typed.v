(**
  Typed facade for bootstrapped standard-natural semiterms.

  Foundation's [Bootstrapping.Semiterm] stores a raw arithmetic value beside
  a proof that it is a bounded term code.  Coq's native [semiterm] already
  enforces the same arity invariant in its type, so duplicating that proof
  field would weaken the representation.  This module supplies the source
  facade directly over the stronger native type and connects every operation
  to the executable code transformations from [Functions].
*)

From Stdlib Require Import Lia Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic Functions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition boot_typed_semiterm (L : language) (n : nat) : Type :=
  syntactic_semiterm L n.

Definition boot_typed_term (L : language) : Type :=
  syntactic_term L.

Definition boot_typed_semiterm_vec (L : language) (k n : nat) : Type :=
  Fin.t k -> boot_typed_semiterm L n.

Definition boot_typed_shift {L n}
    (t : boot_typed_semiterm L n) : boot_typed_semiterm L n :=
  rew_apply rew_shift t.

Definition boot_typed_bshift {L n}
    (t : boot_typed_semiterm L n) : boot_typed_semiterm L (S n) :=
  rew_apply rew_bshift t.

Definition boot_typed_subst {L n m}
    (v : boot_typed_semiterm_vec L n m)
    (t : boot_typed_semiterm L n) : boot_typed_semiterm L m :=
  rew_apply (rew_subst v) t.

Definition boot_typed_free {L}
    (t : boot_typed_semiterm L 1) : boot_typed_term L :=
  rew_apply (@rew_free L 0) t.

Definition boot_typed_q {L k n}
    (v : boot_typed_semiterm_vec L k n) :
    boot_typed_semiterm_vec L (S k) (S n) :=
  fin_coding_cons (Semiterm_bvar Fin.F1)
    (fun i => boot_typed_bshift (v i)).

(** * Constructor equations *)

Lemma boot_typed_shift_bvar : forall L n (i : Fin.t n),
  boot_typed_shift (@Semiterm_bvar L nat n i) = Semiterm_bvar i.
Proof. intros. unfold boot_typed_shift. apply rew_shift_bvar. Qed.

Lemma boot_typed_shift_fvar : forall L n x,
  boot_typed_shift (@Semiterm_fvar L nat n x) = Semiterm_fvar (S x).
Proof. intros. unfold boot_typed_shift. apply rew_shift_fvar. Qed.

Lemma boot_typed_shift_func : forall L n k (f : language_func L k)
    (v : boot_typed_semiterm_vec L k n),
  boot_typed_shift (Semiterm_func f v) =
  Semiterm_func f (fun i => boot_typed_shift (v i)).
Proof. intros. unfold boot_typed_shift. apply rew_apply_func. Qed.

Lemma boot_typed_bshift_bvar : forall L n (i : Fin.t n),
  boot_typed_bshift (@Semiterm_bvar L nat n i) =
  Semiterm_bvar (Fin.FS i).
Proof. intros. unfold boot_typed_bshift. apply rew_bshift_bvar. Qed.

Lemma boot_typed_bshift_fvar : forall L n x,
  boot_typed_bshift (@Semiterm_fvar L nat n x) = Semiterm_fvar x.
Proof. intros. unfold boot_typed_bshift. apply rew_bshift_fvar. Qed.

Lemma boot_typed_bshift_func : forall L n k (f : language_func L k)
    (v : boot_typed_semiterm_vec L k n),
  boot_typed_bshift (Semiterm_func f v) =
  Semiterm_func f (fun i => boot_typed_bshift (v i)).
Proof. intros. unfold boot_typed_bshift. apply rew_apply_func. Qed.

Lemma boot_typed_subst_bvar : forall L n m
    (v : boot_typed_semiterm_vec L n m) (i : Fin.t n),
  boot_typed_subst v (Semiterm_bvar i) = v i.
Proof. intros. unfold boot_typed_subst. apply rew_subst_bvar. Qed.

Lemma boot_typed_subst_fvar : forall L n m
    (v : boot_typed_semiterm_vec L n m) x,
  boot_typed_subst v (Semiterm_fvar x) = Semiterm_fvar x.
Proof. intros. unfold boot_typed_subst. apply rew_subst_fvar. Qed.

Lemma boot_typed_subst_func : forall L n m k
    (f : language_func L k) (v : boot_typed_semiterm_vec L n m)
    (args : boot_typed_semiterm_vec L k n),
  boot_typed_subst v (Semiterm_func f args) =
  Semiterm_func f (fun i => boot_typed_subst v (args i)).
Proof. intros. unfold boot_typed_subst. apply rew_apply_func. Qed.

Lemma boot_typed_free_bvar : forall L (i : Fin.t 1),
  boot_typed_free (@Semiterm_bvar L nat 1 i) = Semiterm_fvar 0.
Proof.
  intros L i. pose proof (fin_one_eq_f1 i) as ->.
  unfold boot_typed_free. apply rew_free_bvar_last.
Qed.

Lemma boot_typed_free_fvar : forall L x,
  boot_typed_free (@Semiterm_fvar L nat 1 x) = Semiterm_fvar (S x).
Proof. intros. unfold boot_typed_free. apply rew_free_fvar. Qed.

(** * Lifted substitution vectors *)

Lemma boot_typed_q_zero : forall L k n
    (v : boot_typed_semiterm_vec L k n),
  boot_typed_q v Fin.F1 = Semiterm_bvar Fin.F1.
Proof. reflexivity. Qed.

Lemma boot_typed_q_succ : forall L k n
    (v : boot_typed_semiterm_vec L k n) (i : Fin.t k),
  boot_typed_q v (Fin.FS i) = boot_typed_bshift (v i).
Proof. reflexivity. Qed.

Lemma boot_typed_q_as_rew_q : forall L k n
    (v : boot_typed_semiterm_vec L k n) i,
  boot_typed_q v i = rew_apply (rew_q (rew_subst v)) (Semiterm_bvar i).
Proof.
  intros L k n v i.
  refine (@Fin.caseS' k i
    (fun j => boot_typed_q v j =
      rew_apply (rew_q (rew_subst v)) (Semiterm_bvar j)) _ _).
  - reflexivity.
  - intro j. reflexivity.
Qed.

Theorem boot_typed_bshift_subst_q : forall L n m
    (t : boot_typed_semiterm L n)
    (v : boot_typed_semiterm_vec L n m),
  boot_typed_subst (boot_typed_q v) (boot_typed_bshift t) =
  boot_typed_bshift (boot_typed_subst v t).
Proof.
  intros L n m t v.
  change (rew_apply (rew_subst (boot_typed_q v)) (rew_apply rew_bshift t) =
    rew_apply rew_bshift (rew_apply (rew_subst v) t)).
  assert (Hrew : rew_equiv (rew_subst (boot_typed_q v))
      (rew_q (rew_subst v))).
  { apply rew_equiv_of_variables.
    - intro i. apply boot_typed_q_as_rew_q.
    - intro x. reflexivity. }
  rewrite (Hrew (rew_apply rew_bshift t)).
  apply rew_q_bshift_apply.
Qed.

(** * Algebraic laws inherited from the generic rewrite calculus *)

Theorem boot_typed_bshift_shift_comm : forall L n
    (t : boot_typed_semiterm L n),
  boot_typed_bshift (boot_typed_shift t) =
  boot_typed_shift (boot_typed_bshift t).
Proof.
  intros. exact (@rew_bshift_shift_comm L n t).
Qed.

Theorem boot_typed_shift_subst : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (t : boot_typed_semiterm L n),
  boot_typed_shift (boot_typed_subst v t) =
  boot_typed_subst (fun i => boot_typed_shift (v i))
    (boot_typed_shift t).
Proof.
  intros. exact (@rew_shift_comp_subst L n m v t).
Qed.

Theorem boot_typed_subst_subst : forall L n m l
    (v : boot_typed_semiterm_vec L n m)
    (w : boot_typed_semiterm_vec L m l)
    (t : boot_typed_semiterm L n),
  boot_typed_subst w (boot_typed_subst v t) =
  boot_typed_subst (fun i => boot_typed_subst w (v i)) t.
Proof.
  intros. exact (@rew_subst_comp_subst L nat n m l v w t).
Qed.

Lemma boot_typed_free_bshift : forall L
    (t : boot_typed_term L),
  boot_typed_free (boot_typed_bshift t) = boot_typed_shift t.
Proof.
  intros. exact (@rew_free_bshift_eq_shift L t).
Qed.

(** * Free-variable-freeness *)

Definition boot_typed_fv_free {L n}
    (t : boot_typed_semiterm L n) : Prop :=
  boot_typed_shift t = t.

Lemma boot_typed_fv_free_bvar : forall L n (i : Fin.t n),
  boot_typed_fv_free (@Semiterm_bvar L nat n i).
Proof. intros. unfold boot_typed_fv_free. apply boot_typed_shift_bvar. Qed.

Lemma boot_typed_fv_free_fvar : forall L n x,
  ~ boot_typed_fv_free (@Semiterm_fvar L nat n x).
Proof.
  intros L n x H. unfold boot_typed_fv_free in H.
  rewrite boot_typed_shift_fvar in H. injection H as Hx. lia.
Qed.

Lemma boot_typed_fv_free_bshift : forall L n
    (t : boot_typed_semiterm L n),
  boot_typed_fv_free t -> boot_typed_fv_free (boot_typed_bshift t).
Proof. apply boot_term_fv_free_bshift. Qed.

(** * Compatibility with executable codes *)

Lemma boot_typed_subst_code : forall L n m EL
    (v : boot_typed_semiterm_vec L n m)
    (t : boot_typed_semiterm L n),
  boot_term_subst_code EL v (semiterm_code EL boot_nat_encoding t) =
  semiterm_code EL boot_nat_encoding (boot_typed_subst v t).
Proof. apply boot_term_subst_code_quote. Qed.

Lemma boot_typed_shift_code : forall L n EL
    (t : boot_typed_semiterm L n),
  boot_term_shift_code EL n (semiterm_code EL boot_nat_encoding t) =
  semiterm_code EL boot_nat_encoding (boot_typed_shift t).
Proof. apply boot_term_shift_code_quote. Qed.

Lemma boot_typed_bshift_code : forall L n EL
    (t : boot_typed_semiterm L n),
  boot_term_bshift_code EL boot_nat_encoding n
      (semiterm_code EL boot_nat_encoding t) =
  semiterm_code EL boot_nat_encoding (boot_typed_bshift t).
Proof.
  intros L n EL t.
  exact (@boot_term_bshift_code_quote L nat n EL boot_nat_encoding t).
Qed.
