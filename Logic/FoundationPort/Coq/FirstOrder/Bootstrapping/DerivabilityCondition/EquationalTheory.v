(**
  Semantic core of the bootstrapping equality theory.

  Foundation's source file proves equality replacement inside an
  internalized proof calculus.  The reusable mathematical content is more
  general: in any model whose equality operator satisfies the equality
  axioms, term and formula substitution respect pointwise equality.  The
  vector-parametric statements below factor that content once and subsume
  the source's separate term, equality, order, negated-order, and arbitrary
  formula replacement lemmas.
*)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Basic Require Import Eq Operator.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Every term is invariant under replacing each bound-variable image by an
    equality-equivalent term.  The free-variable environment is unchanged;
    this is the semantic counterpart of [term_replace]. *)
Theorem bootstrapping_term_replace : forall L M X n k
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (b : Fin.t n -> M) (f : X -> M)
    (e e' : Fin.t k -> semiterm L X n)
    (t : semiterm L X k),
  (forall i, first_order_eqv Str Heq
      (semiterm_val Str b f (e i))
      (semiterm_val Str b f (e' i))) ->
  first_order_eqv Str Heq
    (semiterm_val Str b f (rew_apply (rew_subst e) t))
    (semiterm_val Str b f (rew_apply (rew_subst e') t)).
Proof.
  intros L M X n k Str Heq H b f e e' t He.
  rewrite (semiterm_val_substitute Str b f e t),
    (semiterm_val_substitute Str b f e' t).
  apply (@semiterm_val_eqv L M X k Str Heq H).
  - exact He.
  - intro x. apply (first_order_eqv_refl H).
Qed.

(** Formula truth is invariant under the same pointwise replacement.  This
    is strictly stronger than the source's four operator-specific lemmas:
    equality, strict order, their negations, and all compound formulas are
    all instances. *)
Theorem bootstrapping_formula_replace : forall L M X n k
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (b : Fin.t n -> M) (f : X -> M)
    (e e' : Fin.t k -> semiterm L X n)
    (p : semiformula L X k),
  (forall i, first_order_eqv Str Heq
      (semiterm_val Str b f (e i))
      (semiterm_val Str b f (e' i))) ->
  (semiformula_eval Str b f (semiformula_substitute e p) <->
   semiformula_eval Str b f (semiformula_substitute e' p)).
Proof.
  intros L M X n k Str Heq H b f e e' p He.
  unfold semiformula_substitute.
  rewrite (semiformula_eval_substitute Str b f e p),
    (semiformula_eval_substitute Str b f e' p).
  apply (@semiformula_eval_eqv L M X k Str Heq H).
  - exact He.
  - intro x. apply (first_order_eqv_refl H).
Qed.

Corollary bootstrapping_formula_replace_forward : forall L M X n k
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (b : Fin.t n -> M) (f : X -> M)
    (e e' : Fin.t k -> semiterm L X n)
    (p : semiformula L X k),
  (forall i, first_order_eqv Str Heq
      (semiterm_val Str b f (e i))
      (semiterm_val Str b f (e' i))) ->
  semiformula_eval Str b f (semiformula_substitute e p) ->
  semiformula_eval Str b f (semiformula_substitute e' p).
Proof.
  intros L M X n k Str Heq H b f e e' p He Htruth.
  exact ((proj1 (@bootstrapping_formula_replace L M X n k
    Str Heq H b f e e' p He)) Htruth).
Qed.
