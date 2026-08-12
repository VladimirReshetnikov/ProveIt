From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantMultinomials.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The polynomial ring as a module over its full symmetric subring.

    We present the symmetric coefficient ring by another copy of the
    multivariate polynomial ring, embedded through elementary-symmetric
    substitution [sym_eval].  Injectivity and exact image characterization of
    that embedding were proved in [LazardInvariantMultinomials].  A newtype is
    used for the ambient module so that its scalar action can be the faithful
    action [a * p := sym_eval a * p] without colliding with the ordinary
    self-module instance of the polynomial ring.

    The unconditional finite-free Artin construction built from this module
    now lives in [LazardInvariantArtinSuccessor]; no coordinate or basis
    hypothesis is packaged here. *)
Module PolynomialFormulasLazardInvariantSymmetricModule.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.

Section SymmetricModule.

Variables (R : comRingType) (n : nat).

Definition symmetric_polynomial_module : Type := {mpoly R[n]}.

HB.instance Definition _ := GRing.Zmodule.on symmetric_polynomial_module.

Definition symmetric_scalar
    (a : {mpoly R[n]}) (p : symmetric_polynomial_module) :
    symmetric_polynomial_module :=
  IM.sym_eval a * p.

Local Infix "*S:" := symmetric_scalar (at level 40).

Fact symmetric_scalarA a b p : a *S: (b *S: p) = (a * b) *S: p.
Proof. by rewrite /symmetric_scalar IM.sym_evalM mulrA. Qed.

Fact symmetric_scalar1 p : 1 *S: p = p.
Proof. by rewrite /symmetric_scalar IM.sym_eval1 mul1r. Qed.

Fact symmetric_scalarDr a p q : a *S: (p + q) = a *S: p + a *S: q.
Proof. exact: mulrDr. Qed.

Fact symmetric_scalarDl p a b : (a + b) *S: p = a *S: p + b *S: p.
Proof. by rewrite /symmetric_scalar IM.sym_evalD mulrDl. Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build
  {mpoly R[n]} symmetric_polynomial_module
  symmetric_scalarA symmetric_scalar1 symmetric_scalarDr symmetric_scalarDl.

Lemma symmetric_scalarE (a : {mpoly R[n]})
    (p : symmetric_polynomial_module) :
  a *: p = IM.sym_eval a * p :> {mpoly R[n]}.
Proof. by []. Qed.

Lemma symmetric_scalar_faithful :
  injective (fun a : {mpoly R[n]} =>
    a *: (1 : symmetric_polynomial_module)).
Proof.
move=> a b hab.
apply: IM.sym_eval_injective.
move: hab.
by rewrite !symmetric_scalarE !mulr1.
Qed.

(** Scalars represented here are exactly the fully symmetric ambient
    polynomials. *)
Lemma symmetric_scalar_imageP p :
  reflect
    (exists a : {mpoly R[n]},
      a *: (1 : symmetric_polynomial_module) = p)
    (p \is symmetric).
Proof.
apply: (iffP (IM.sym_eval_imageP p)).
- move=> [a ha]; exists a.
  by rewrite symmetric_scalarE mulr1 ha.
- move=> [a <-].
  exists a.
  by rewrite symmetric_scalarE mulr1.
Qed.

(** Permuting variables is linear over the symmetric coefficient ring.  The
    wrapper keeps the result in the newtype carrying the symmetric scalar
    action; the underlying multinomial action is the honest left action from
    [LazardInvariantMultinomials]. *)
Definition symmetric_mpoly_left_action (s : 'S_n)
    (p : symmetric_polynomial_module) :
    symmetric_polynomial_module :=
  IM.mpoly_left_action s p.

Lemma symmetric_mpoly_left_action1 p :
  symmetric_mpoly_left_action 1 p = p.
Proof. exact: IM.mpoly_left_action1. Qed.

Lemma symmetric_mpoly_left_actionM (s1 s2 : 'S_n) p :
  symmetric_mpoly_left_action (s1 * s2) p =
    symmetric_mpoly_left_action s1
      (symmetric_mpoly_left_action s2 p).
Proof. exact: IM.mpoly_left_actionM. Qed.

Lemma symmetric_mpoly_left_action0 s :
  symmetric_mpoly_left_action s 0 = 0.
Proof. exact: IM.mpoly_left_action0. Qed.

Lemma symmetric_mpoly_left_actionD s p q :
  symmetric_mpoly_left_action s (p + q) =
    symmetric_mpoly_left_action s p +
      symmetric_mpoly_left_action s q.
Proof. exact: IM.mpoly_left_actionD. Qed.

Lemma symmetric_mpoly_left_action_sum
    (I : finType) s (p : I -> symmetric_polynomial_module) :
  symmetric_mpoly_left_action s (\sum_i p i) =
    \sum_i symmetric_mpoly_left_action s (p i).
Proof.
rewrite /symmetric_mpoly_left_action /IM.mpoly_left_action.
exact: raddf_sum.
Qed.

Lemma symmetric_mpoly_left_actionZ s a p :
  symmetric_mpoly_left_action s (a *: p) =
    a *: symmetric_mpoly_left_action s p.
Proof.
rewrite /symmetric_mpoly_left_action !symmetric_scalarE
  IM.mpoly_left_action_mul.
have hfixed : IM.mpoly_left_action s (IM.sym_eval a) = IM.sym_eval a.
  move/IM.full_symmetricP: (IM.sym_eval_symmetric a) => hs.
  exact: hs s.
by rewrite hfixed.
Qed.

Lemma symmetric_mpoly_left_action_homogeneous s p d :
  (p : {mpoly R[n]}) \is d.-homog ->
  (symmetric_mpoly_left_action s p : {mpoly R[n]}) \is d.-homog.
Proof. exact: IM.mpoly_left_action_homogeneous. Qed.

End SymmetricModule.

(** Ordinary homogeneity after forgetting the symmetric-scalar wrapper. *)
Definition symmetric_module_homogeneous (R : comRingType) n
    (p : symmetric_polynomial_module R n) (d : nat) : Prop :=
  (p : {mpoly R[n]}) \is d.-homog.

End PolynomialFormulasLazardInvariantSymmetricModule.
