(**
  Mathematical core of Foundation's first-order binder notation layer.

  The Lean source is mostly parser, macro, and pretty-printer support.  Its
  substantive declarations are two syntax constructors that nest a formula
  behind a finite family of graph-like premises, together with their exact
  semantics.  Coq does not need the elaborator machinery, so this module
  exposes those constructors directly and factors their index bookkeeping
  through finite-environment append.

  We choose the native Coq layout [new variables ++ retained parameters].
  This is propositionally the same de Bruijn layout as the source while
  avoiding arithmetic casts between [m + n] and [n + m].
*)

From Stdlib Require Import Logic.FunctionalExtensionality Vectors.Fin.
From FoundationModal Require Import GenericLogicSymbol.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator Eq.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics RewriteClosure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Ordinary predicate-style nesting *)

Definition semiformula_nest_argument_terms {L X n m}
    (i : Fin.t n) : Fin.t (S m) -> semiterm L X (n + m) :=
  fun j => @Fin.caseS' m j (fun _ => semiterm L X (n + m))
    (Semiterm_bvar (Fin.L m i))
    (fun q => Semiterm_bvar (Fin.R n q)).

Definition semiformula_nest_result_terms {L X n m} :
    Fin.t n -> semiterm L X (n + m) :=
  fun i => Semiterm_bvar (Fin.L m i).

Definition semiformula_nest_body {L X n m}
    (p : semiformula L X n)
    (premises : Fin.t n -> semiformula L X (S m)) :
    semiformula L X (n + m) :=
  semiformula_imp
    (generic_matrix_conj (semiformula_connectives L X (n + m)) n
      (fun i => semiformula_substitute
        (semiformula_nest_argument_terms i) (premises i)))
    (semiformula_substitute semiformula_nest_result_terms p).

Definition semiformula_nest {L X n m}
    (p : semiformula L X n)
    (premises : Fin.t n -> semiformula L X (S m)) :
    semiformula L X m :=
  first_all_iter (semiformula_universal_quantifier L X) n m
    (semiformula_nest_body p premises).

Lemma semiformula_nest_argument_terms_eval : forall L M X n m
    (Str : first_order_structure L M) (v : Fin.t n -> M)
    (e : Fin.t m -> M) (f : X -> M) i,
  (fun j => semiterm_val Str (fin_env_append n m v e) f
      (@semiformula_nest_argument_terms L X n m i j)) =
  fin_env_cons (v i) e.
Proof.
  intros. apply functional_extensionality. intro j.
  refine (@Fin.caseS' m j (fun q =>
    semiterm_val Str (fin_env_append n m v e) f
      (semiformula_nest_argument_terms i q) =
    fin_env_cons (v i) e q) _ _).
  - simpl. apply fin_env_append_left.
  - intro q. simpl. apply fin_env_append_right.
Qed.

Lemma semiformula_nest_result_terms_eval : forall L M X n m
    (Str : first_order_structure L M) (v : Fin.t n -> M)
    (e : Fin.t m -> M) (f : X -> M),
  (fun i => semiterm_val Str (fin_env_append n m v e) f
      (@semiformula_nest_result_terms L X n m i)) = v.
Proof.
  intros. apply functional_extensionality. intro i.
  simpl. apply fin_env_append_left.
Qed.

Theorem semiformula_eval_nest : forall L M X n m
    (Str : first_order_structure L M) (e : Fin.t m -> M)
    (f : X -> M) (p : semiformula L X n)
    (premises : Fin.t n -> semiformula L X (S m)),
  semiformula_eval Str e f (semiformula_nest p premises) <->
  forall v : Fin.t n -> M,
    (forall i, semiformula_eval Str (fin_env_cons (v i) e) f
      (premises i)) ->
    semiformula_eval Str v f p.
Proof.
  intros L M X n m Str e f p premises.
  unfold semiformula_nest. rewrite semiformula_eval_all_iter.
  split.
  - intros Hall v Hpremises. specialize (Hall v).
    unfold semiformula_nest_body in Hall.
    rewrite semiformula_eval_imp in Hall.
    assert (Hresult : semiformula_eval Str (fin_env_append n m v e) f
      (semiformula_substitute semiformula_nest_result_terms p)).
    { apply Hall. rewrite first_order_matrix_conj_eval.
      intro i. change (semiformula_eval Str (fin_env_append n m v e) f
        (semiformula_rewrite
          (rew_subst (semiformula_nest_argument_terms i)) (premises i))).
      rewrite semiformula_eval_substitute,
        semiformula_nest_argument_terms_eval.
      apply Hpremises. }
    change (semiformula_eval Str (fin_env_append n m v e) f
      (semiformula_rewrite (rew_subst semiformula_nest_result_terms) p))
      in Hresult.
    rewrite semiformula_eval_substitute,
      semiformula_nest_result_terms_eval in Hresult.
    exact Hresult.
  - intros H v. unfold semiformula_nest_body.
    rewrite semiformula_eval_imp.
    intro Hpremises.
    change (semiformula_eval Str (fin_env_append n m v e) f
      (semiformula_rewrite (rew_subst semiformula_nest_result_terms) p)).
    rewrite semiformula_eval_substitute,
      semiformula_nest_result_terms_eval.
    apply H. intro i.
    rewrite first_order_matrix_conj_eval in Hpremises.
    specialize (Hpremises i).
    change (semiformula_eval Str (fin_env_append n m v e) f
      (semiformula_rewrite
        (rew_subst (semiformula_nest_argument_terms i)) (premises i)))
      in Hpremises.
    rewrite semiformula_eval_substitute,
      semiformula_nest_argument_terms_eval in Hpremises.
    exact Hpremises.
Qed.

(** * Function-style nesting with one distinguished leading parameter *)

Definition semiformula_nest_func_argument_terms {L X n m}
    (i : Fin.t n) : Fin.t (S m) -> semiterm L X (n + S m) :=
  fun j => @Fin.caseS' m j (fun _ => semiterm L X (n + S m))
    (Semiterm_bvar (Fin.L (S m) i))
    (fun q => Semiterm_bvar (Fin.R n (Fin.FS q))).

Definition semiformula_nest_func_result_terms {L X n m} :
    Fin.t (S n) -> semiterm L X (n + S m) :=
  fun j => @Fin.caseS' n j (fun _ => semiterm L X (n + S m))
    (Semiterm_bvar (Fin.R n Fin.F1))
    (fun i => Semiterm_bvar (Fin.L (S m) i)).

Definition semiformula_nest_func_body {L X n m}
    (p : semiformula L X (S n))
    (premises : Fin.t n -> semiformula L X (S m)) :
    semiformula L X (n + S m) :=
  semiformula_imp
    (generic_matrix_conj (semiformula_connectives L X (n + S m)) n
      (fun i => semiformula_substitute
        (semiformula_nest_func_argument_terms i) (premises i)))
    (semiformula_substitute semiformula_nest_func_result_terms p).

Definition semiformula_nest_func {L X n m}
    (p : semiformula L X (S n))
    (premises : Fin.t n -> semiformula L X (S m)) :
    semiformula L X (S m) :=
  first_all_iter (semiformula_universal_quantifier L X) n (S m)
    (semiformula_nest_func_body p premises).

Lemma semiformula_nest_func_argument_terms_eval : forall L M X n m
    (Str : first_order_structure L M) (v : Fin.t n -> M)
    z (e : Fin.t m -> M) (f : X -> M) i,
  (fun j => semiterm_val Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (@semiformula_nest_func_argument_terms L X n m i j)) =
  fin_env_cons (v i) e.
Proof.
  intros. apply functional_extensionality. intro j.
  refine (@Fin.caseS' m j (fun q =>
    semiterm_val Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (semiformula_nest_func_argument_terms i q) =
    fin_env_cons (v i) e q) _ _).
  - simpl. apply fin_env_append_left.
  - intro q. simpl. rewrite fin_env_append_right. reflexivity.
Qed.

Lemma semiformula_nest_func_result_terms_eval : forall L M X n m
    (Str : first_order_structure L M) (v : Fin.t n -> M)
    z (e : Fin.t m -> M) (f : X -> M),
  (fun j => semiterm_val Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (@semiformula_nest_func_result_terms L X n m j)) =
  fin_env_cons z v.
Proof.
  intros. apply functional_extensionality. intro j.
  refine (@Fin.caseS' n j (fun q =>
    semiterm_val Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (semiformula_nest_func_result_terms q) =
    fin_env_cons z v q) _ _).
  - simpl. rewrite fin_env_append_right. reflexivity.
  - intro i. simpl. apply fin_env_append_left.
Qed.

Theorem semiformula_eval_nest_func : forall L M X n m
    (Str : first_order_structure L M) z (e : Fin.t m -> M)
    (f : X -> M) (p : semiformula L X (S n))
    (premises : Fin.t n -> semiformula L X (S m)),
  semiformula_eval Str (fin_env_cons z e) f
      (semiformula_nest_func p premises) <->
  forall v : Fin.t n -> M,
    (forall i, semiformula_eval Str (fin_env_cons (v i) e) f
      (premises i)) ->
    semiformula_eval Str (fin_env_cons z v) f p.
Proof.
  intros L M X n m Str z e f p premises.
  unfold semiformula_nest_func. rewrite semiformula_eval_all_iter.
  split.
  - intros Hall v Hpremises. specialize (Hall v).
    unfold semiformula_nest_func_body in Hall.
    rewrite semiformula_eval_imp in Hall.
    assert (Hresult : semiformula_eval Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (semiformula_substitute semiformula_nest_func_result_terms p)).
    { apply Hall. rewrite first_order_matrix_conj_eval.
      intro i. change (semiformula_eval Str
        (fin_env_append n (S m) v (fin_env_cons z e)) f
        (semiformula_rewrite
          (rew_subst (semiformula_nest_func_argument_terms i))
          (premises i))).
      rewrite semiformula_eval_substitute,
        semiformula_nest_func_argument_terms_eval.
      apply Hpremises. }
    change (semiformula_eval Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (semiformula_rewrite
        (rew_subst semiformula_nest_func_result_terms) p)) in Hresult.
    rewrite semiformula_eval_substitute,
      semiformula_nest_func_result_terms_eval in Hresult.
    exact Hresult.
  - intros H v. unfold semiformula_nest_func_body.
    rewrite semiformula_eval_imp.
    intro Hpremises.
    change (semiformula_eval Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (semiformula_rewrite
        (rew_subst semiformula_nest_func_result_terms) p)).
    rewrite semiformula_eval_substitute,
      semiformula_nest_func_result_terms_eval.
    apply H. intro i.
    rewrite first_order_matrix_conj_eval in Hpremises.
    specialize (Hpremises i).
    change (semiformula_eval Str
      (fin_env_append n (S m) v (fin_env_cons z e)) f
      (semiformula_rewrite
        (rew_subst (semiformula_nest_func_argument_terms i))
        (premises i))) in Hpremises.
    rewrite semiformula_eval_substitute,
      semiformula_nest_func_argument_terms_eval in Hpremises.
    exact Hpremises.
Qed.
