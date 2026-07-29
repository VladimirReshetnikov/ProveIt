(**
  Syntactic rewrites and finite quantifier blocks under Tarski semantics.

  This completes the high-value convenience layer from
  [Foundation/FirstOrder/Basic/Semantics/Semantics.lean].  The proofs reduce
  all syntactic rewrites to [semiterm_val_rewrite] and
  [semiformula_eval_rewrite], and use one shared finite-environment append for
  both universal and existential quantifier blocks.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Term Quantifier Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Add a distinguished value at free-variable index zero. *)
Definition nat_env_cons {M} (a : M) (f : nat -> M) (x : nat) : M :=
  match x with
  | 0 => a
  | S y => f y
  end.

(** Append a value at the last bound-variable index. *)
Definition fin_env_snoc {M n} (b : Fin.t n -> M) (a : M)
    (i : Fin.t (n + 1)) : M :=
  @Fin.case_L_R' n 1 (fun _ => M) i b (fun _ => a).

Lemma fin_env_snoc_left : forall M n (b : Fin.t n -> M) a (i : Fin.t n),
  fin_env_snoc b a (Fin.L 1 i) = b i.
Proof. intros; unfold fin_env_snoc; now rewrite Fin.case_L_R'_L. Qed.

Lemma fin_env_snoc_right : forall M n (b : Fin.t n -> M) a (i : Fin.t 1),
  fin_env_snoc b a (Fin.R n i) = a.
Proof. intros; unfold fin_env_snoc; now rewrite Fin.case_L_R'_R. Qed.

Lemma fin_env_cons_eta : forall M n (e : Fin.t (S n) -> M),
  fin_env_cons (e Fin.F1) (fun i => e (Fin.FS i)) = e.
Proof.
  intros M n e. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    fin_env_cons (e Fin.F1) (fun u => e (Fin.FS u)) j = e j)
    eq_refl _).
  intro j. reflexivity.
Qed.

(** Concatenate a newly quantified environment on the left of an existing
    bound-variable environment. *)
Fixpoint fin_env_append {M} (k n : nat) (e : Fin.t k -> M)
    (b : Fin.t n -> M) : Fin.t (k + n) -> M :=
  match k as j return (Fin.t j -> M) -> Fin.t (j + n) -> M with
  | 0 => fun _ => b
  | S j => fun e0 =>
      fin_env_cons (e0 Fin.F1)
        (@fin_env_append M j n (fun i => e0 (Fin.FS i)) b)
  end e.

Arguments fin_env_append {M} k n e b.

Lemma fin_env_append_cons : forall M k n (x : M) (e : Fin.t k -> M)
    (b : Fin.t n -> M),
  fin_env_append (S k) n (fin_env_cons x e) b =
  fin_env_cons x (fin_env_append k n e b).
Proof. reflexivity. Qed.

Lemma fin_env_append_left : forall M k n (e : Fin.t k -> M)
    (b : Fin.t n -> M) (i : Fin.t k),
  fin_env_append k n e b (Fin.L n i) = e i.
Proof.
  intros M k; induction k as [|k IH]; intros n e b i.
  - inversion i.
  - refine (@Fin.caseS' k i (fun j =>
      fin_env_append (S k) n e b (Fin.L n j) = e j) _ _).
    + reflexivity.
    + intro j. simpl. apply IH.
Qed.

Lemma fin_env_append_right : forall M k n (e : Fin.t k -> M)
    (b : Fin.t n -> M) (i : Fin.t n),
  fin_env_append k n e b (Fin.R k i) = b i.
Proof.
  intros M k; induction k as [|k IH]; intros n e b i.
  - reflexivity.
  - simpl. apply IH.
Qed.

Lemma fin_env_append_left_eta : forall M k n (e : Fin.t k -> M)
    (b : Fin.t n -> M),
  (fun i => fin_env_append k n e b (Fin.L n i)) = e.
Proof.
  intros. apply functional_extensionality. intro i.
  apply fin_env_append_left.
Qed.

Lemma fin_env_append_right_eta : forall M k n (e : Fin.t k -> M)
    (b : Fin.t n -> M),
  (fun i => fin_env_append k n e b (Fin.R k i)) = b.
Proof.
  intros. apply functional_extensionality. intro i.
  apply fin_env_append_right.
Qed.

(** * Standard syntactic term rewrites *)

Lemma semiterm_val_shift :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (t : syntactic_semiterm L n),
    semiterm_val Str b f (rew_apply rew_shift t) =
    semiterm_val Str b (fun x => f (S x)) t.
Proof. intros; rewrite semiterm_val_rewrite; reflexivity. Qed.

Lemma semiterm_val_rew_free_bvars :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M),
    (fun i => semiterm_val Str b (nat_env_cons a f)
      (rew_apply rew_free (@Semiterm_bvar L nat (n + 1) i))) =
    fin_env_snoc b a.
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.case_L_R' n 1 (fun j =>
    semiterm_val Str b (nat_env_cons a f)
      (rew_apply rew_free (@Semiterm_bvar L nat (n + 1) j)) =
    fin_env_snoc b a j) i _ _).
  - intro j. rewrite rew_free_bvar_old, fin_env_snoc_left. reflexivity.
  - intro j. assert (Hj : j = Fin.F1) by apply fin_one_eq_f1.
    subst j. rewrite rew_free_bvar_last, fin_env_snoc_right. reflexivity.
Qed.

Lemma semiterm_val_rew_free_fvars :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M),
    (fun x => semiterm_val Str b (nat_env_cons a f)
      (rew_apply rew_free (@Semiterm_fvar L nat (n + 1) x))) = f.
Proof.
  intros. apply functional_extensionality. intro x.
  rewrite rew_free_fvar. reflexivity.
Qed.

Lemma semiterm_val_rew_fix_bvars :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M),
    (fun i => semiterm_val Str (fin_env_snoc b a) f
      (rew_apply rew_fix (@Semiterm_bvar L nat n i))) = b.
Proof.
  intros. apply functional_extensionality. intro i.
  rewrite rew_fix_bvar. simpl. apply fin_env_snoc_left.
Qed.

Lemma semiterm_val_rew_fix_fvars :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M),
    (fun x => semiterm_val Str (fin_env_snoc b a) f
      (rew_apply rew_fix (@Semiterm_fvar L nat n x))) = nat_env_cons a f.
Proof.
  intros. apply functional_extensionality. intros [|x].
  - rewrite rew_fix_fvar_zero. simpl. apply fin_env_snoc_right.
  - rewrite rew_fix_fvar_succ. reflexivity.
Qed.

Lemma semiterm_val_free :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M)
         (t : syntactic_semiterm L (n + 1)),
    semiterm_val Str b (nat_env_cons a f) (rew_apply rew_free t) =
    semiterm_val Str (fin_env_snoc b a) f t.
Proof.
  intros L M n Str b f a t. rewrite semiterm_val_rewrite.
  now rewrite semiterm_val_rew_free_bvars, semiterm_val_rew_free_fvars.
Qed.

Lemma semiterm_val_fix :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M)
         (t : syntactic_semiterm L n),
    semiterm_val Str (fin_env_snoc b a) f (rew_apply rew_fix t) =
    semiterm_val Str b (nat_env_cons a f) t.
Proof.
  intros L M n Str b f a t. rewrite semiterm_val_rewrite.
  now rewrite semiterm_val_rew_fix_bvars, semiterm_val_rew_fix_fvars.
Qed.

(** * Standard syntactic formula rewrites *)

Lemma semiformula_eval_free :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M)
         (p : semiproposition L (n + 1)),
    semiformula_eval Str b (nat_env_cons a f) (semiformula_free p) <->
    semiformula_eval Str (fin_env_snoc b a) f p.
Proof.
  intros L M n Str b f a p. unfold semiformula_free.
  rewrite semiformula_eval_rewrite.
  now rewrite semiterm_val_rew_free_bvars, semiterm_val_rew_free_fvars.
Qed.

Lemma semiformula_eval_shift :
  forall L M n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : nat -> M) (a : M)
         (p : semiproposition L n),
    semiformula_eval Str b (nat_env_cons a f) (semiformula_shift p) <->
    semiformula_eval Str b f p.
Proof.
  intros. unfold semiformula_shift. rewrite semiformula_eval_rewrite.
  reflexivity.
Qed.

(** * Finite blocks of quantifiers *)

Theorem semiformula_eval_all_iter :
  forall L M X k n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (p : semiformula L X (k + n)),
    semiformula_eval Str b f
      (first_all_iter (semiformula_universal_quantifier L X) k n p) <->
    forall e : Fin.t k -> M,
      semiformula_eval Str (fin_env_append k n e b) f p.
Proof.
  intros L M X k; induction k as [|k IH]; intros n Str b f p; simpl.
  - split.
    + intros H e. exact H.
    + intro H. exact (H (fun i : Fin.t 0 => match i with end)).
  - rewrite IH. split.
    + intros H e. exact (H (fun i => e (Fin.FS i)) (e Fin.F1)).
    + intros H e x. specialize (H (fin_env_cons x e)). exact H.
Qed.

Theorem semiformula_eval_exists_iter :
  forall L M X k n (Str : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (p : semiformula L X (k + n)),
    semiformula_eval Str b f
      (first_exists_iter (semiformula_existential_quantifier L X) k n p) <->
    exists e : Fin.t k -> M,
      semiformula_eval Str (fin_env_append k n e b) f p.
Proof.
  intros L M X k; induction k as [|k IH]; intros n Str b f p; simpl.
  - split.
    + intro H. exists (fun i : Fin.t 0 => match i with end). exact H.
    + intros [e H]. exact H.
  - rewrite IH. split.
    + intros [e [x H]]. exists (fin_env_cons x e).
      exact H.
    + intros [e H]. exists (fun i => e (Fin.FS i)), (e Fin.F1).
      exact H.
Qed.

Theorem semiformula_eval_all_closure :
  forall L M X k (Str : first_order_structure L M)
         (b : Fin.t 0 -> M) (f : X -> M) (p : semiformula L X k),
    semiformula_eval Str b f
      (first_all_closure (semiformula_universal_quantifier L X) k p) <->
    forall e : Fin.t k -> M, semiformula_eval Str e f p.
Proof.
  intros L M X k; induction k as [|k IH]; intros Str b f p; simpl.
  - split.
    + intros H e. assert (He : e = b).
      { apply functional_extensionality. intro i.
        exact (Fin.case0 (fun j => e j = b j) i). }
      now rewrite He.
    + intro H. apply H.
  - rewrite IH. split.
    + intros H e. specialize (H (fun i => e (Fin.FS i)) (e Fin.F1)).
      now rewrite fin_env_cons_eta in H.
    + intros H e x. apply H.
Qed.

Theorem semiformula_eval_exists_closure :
  forall L M X k (Str : first_order_structure L M)
         (b : Fin.t 0 -> M) (f : X -> M) (p : semiformula L X k),
    semiformula_eval Str b f
      (first_exists_closure (semiformula_existential_quantifier L X) k p) <->
    exists e : Fin.t k -> M, semiformula_eval Str e f p.
Proof.
  intros L M X k; induction k as [|k IH]; intros Str b f p; simpl.
  - split.
    + intro H. exists b. exact H.
    + intros [e H]. assert (He : e = b).
      { apply functional_extensionality. intro i.
        exact (Fin.case0 (fun j => e j = b j) i). }
      now rewrite He in H.
  - rewrite IH. split.
    + intros [e [x H]]. exists (fin_env_cons x e). exact H.
    + intros [e H]. exists (fun i => e (Fin.FS i)), (e Fin.F1).
      now rewrite fin_env_cons_eta.
Qed.
