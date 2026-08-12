From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantSymmetricModule LazardInvariantArtinSuccessor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The exact target module in Lazard's Theorem 2.

    For a subgroup [H <= S_n], this file constructs the type of polynomials
    fixed by [H] as an honest module over the full symmetric polynomial ring.
    It then states Theorem 2 in its literal finite-free, homogeneous,
    degree-bounded form.

    The ambient finite-free Artin decomposition below is unconditional: its
    coordinates and their uniqueness are constructed by the ordered-root
    successor induction.  Thus the remaining gap is no longer a supplied
    ambient coordinate/basis hypothesis.  It is exactly the graded
    fixed-space theorem for the homogeneous Reynolds projection. *)
Module PolynomialFormulasLazardInvariantSubgroupModule.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module AS := PolynomialFormulasLazardInvariantArtinSuccessor.

Section InvariantModule.

Variables (F : fieldType) (n : nat) (H : {group 'S_n}).

(** Fixedness under every element of the subgroup, represented through the
    finite group type [[subg H]]. *)
Definition lazard_subgroup_invariant_pred :
    pred (SM.symmetric_polynomial_module F n) :=
  fun p =>
    [forall g : [subg H],
      SM.symmetric_mpoly_left_action (sgval g) p == p].

Lemma lazard_subgroup_invariantP p :
  reflect
    (forall g : [subg H],
      SM.symmetric_mpoly_left_action (sgval g) p = p)
    (p \in lazard_subgroup_invariant_pred).
Proof.
apply: (iffP forallP).
- move=> hp g.
  apply/eqP.
  exact: hp g.
- move=> hp g.
  apply/eqP.
  exact: hp g.
Qed.

(** The fixed polynomials are closed under symmetric-polynomial scalars.
    This is where linearity of variable permutation over the symmetric
    coefficient ring is used. *)
Fact lazard_subgroup_invariant_submod_closed :
  @submod_closed {mpoly F[n]}
    (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
      F n)
    lazard_subgroup_invariant_pred.
Proof.
split.
- apply/lazard_subgroup_invariantP=> g.
  exact: SM.symmetric_mpoly_left_action0.
- move=> a p q /lazard_subgroup_invariantP hp
    /lazard_subgroup_invariantP hq.
  apply/lazard_subgroup_invariantP=> g.
  by rewrite SM.symmetric_mpoly_left_actionD
    SM.symmetric_mpoly_left_actionZ hp hq.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build
  {mpoly F[n]}
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F n)
  lazard_subgroup_invariant_pred
  lazard_subgroup_invariant_submod_closed.

(** An actual module type, rather than merely an ambient predicate. *)
Inductive lazard_subgroup_invariant_module : predArgType :=
  LazardSubgroupInvariant p & p \in lazard_subgroup_invariant_pred.

Definition lazard_subgroup_invariant_val
    (p : lazard_subgroup_invariant_module) :
    SM.symmetric_polynomial_module F n :=
  let: LazardSubgroupInvariant q _ := p in q.

HB.instance Definition _ :=
  [isSub for lazard_subgroup_invariant_val].
HB.instance Definition _ :=
  [Choice of lazard_subgroup_invariant_module by <:].
HB.instance Definition _ :=
  [SubChoice_isSubZmodule of lazard_subgroup_invariant_module by <:].
HB.instance Definition _ :=
  GRing.SubZmodule_isSubLmodule.Build
    {mpoly F[n]}
    (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
      F n)
    lazard_subgroup_invariant_pred
    lazard_subgroup_invariant_module
    (GRing.submod_closed_semi lazard_subgroup_invariant_submod_closed).

Lemma lazard_subgroup_invariant_valP
    (p : lazard_subgroup_invariant_module) :
  lazard_subgroup_invariant_val p \in lazard_subgroup_invariant_pred.
Proof. exact: valP. Qed.

Lemma lazard_subgroup_invariant_val_injective :
  injective lazard_subgroup_invariant_val.
Proof. exact: val_inj. Qed.

Lemma lazard_subgroup_invariant_val_is_linear :
  forall (a : {mpoly F[n]}) p q,
    lazard_subgroup_invariant_val (a *: p + q) =
      SM.symmetric_scalar a (lazard_subgroup_invariant_val p) +
        lazard_subgroup_invariant_val q.
Proof. by []. Qed.

HB.instance Definition _ := GRing.isLinear.Build
  {mpoly F[n]} lazard_subgroup_invariant_module
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F n)
  *:%R lazard_subgroup_invariant_val
  lazard_subgroup_invariant_val_is_linear.

Lemma lazard_subgroup_invariant_val_fixed
    (p : lazard_subgroup_invariant_module) (g : [subg H]) :
  SM.symmetric_mpoly_left_action (sgval g)
      (lazard_subgroup_invariant_val p) =
    lazard_subgroup_invariant_val p.
Proof.
move/lazard_subgroup_invariantP:
  (lazard_subgroup_invariant_valP p) => hp.
exact: hp g.
Qed.

(** Homogeneity is measured after forgetting the fixed-submodule wrapper. *)
Definition lazard_invariant_homogeneous
    (p : lazard_subgroup_invariant_module) (d : nat) : Prop :=
  (lazard_subgroup_invariant_val p : {mpoly F[n]}) \is d.-homog.

(** The data asserted by Lazard's Theorem 2: a finite free basis of the
    subgroup invariants over the full symmetric ring, every basis vector
    homogeneous and of degree at most [n(n-1)/2]. *)
Definition lazard_homogeneous_invariant_basis :=
  @FF.homogeneous_finite_free_decomposition
    {mpoly F[n]} lazard_subgroup_invariant_module
    lazard_invariant_homogeneous (IM.lazard_degree_bound n).

Definition lazard_theorem_two_statement : Prop :=
  ([pchar F] =i pred0) ->
  inhabited lazard_homogeneous_invariant_basis.

(** The ambient input to Reynolds is now fully constructed, including its
    coordinates, reconstruction, uniqueness, homogeneous degrees, and the
    uniform degree bound. *)
Definition lazard_ambient_artin_homogeneous_decomposition :=
  AS.lazard_reverse_artin_homogeneous_decomposition F n.

Lemma lazard_ambient_artin_rank :
  #|FF.ffd_index
    (FF.hffd_free lazard_ambient_artin_homogeneous_decomposition)| = n`!.
Proof. exact: AS.lazard_reverse_artin_index_card. Qed.

Lemma lazard_ambient_artin_reconstruct
    (p : SM.symmetric_polynomial_module F n) :
  p = \sum_i
    (FF.ffd_coeff
      (FF.hffd_free lazard_ambient_artin_homogeneous_decomposition)
      p i) *:
    FF.ffd_basis
      (FF.hffd_free lazard_ambient_artin_homogeneous_decomposition) i.
Proof.
exact: (FF.hffd_reconstruct
  lazard_ambient_artin_homogeneous_decomposition p).
Qed.

Lemma lazard_ambient_artin_basis_homogeneous i :
  SM.symmetric_module_homogeneous
    (FF.ffd_basis
      (FF.hffd_free lazard_ambient_artin_homogeneous_decomposition) i)
    (FF.hffd_degree lazard_ambient_artin_homogeneous_decomposition i).
Proof.
exact: (AS.lazard_reverse_artin_basis_homogeneous
  (F := F) (n := n) i).
Qed.

Lemma lazard_ambient_artin_basis_degree_le i :
  (FF.hffd_degree lazard_ambient_artin_homogeneous_decomposition i <=
    IM.lazard_degree_bound n)%N.
Proof.
exact: (AS.lazard_reverse_artin_degree_le
  (F := F) (n := n) i).
Qed.

End InvariantModule.

End PolynomialFormulasLazardInvariantSubgroupModule.
