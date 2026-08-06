From Stdlib.Logic Require Import ConstructiveEpsilon.
From Stdlib.Arith Require Import PeanoNat.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticSparseResolvents SexticNewtonPowerSums SexticComputedResolvents
  SexticSeparatingSearch SexticSeparatingExistence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Total certified minimization for the separating-parameter search.

    [first_true_index] is the standard constructive linear search from
    [ConstructiveEpsilon].  Its last argument is a proof that the Boolean
    test eventually succeeds.  That argument lives in [Prop], so extraction
    erases it and leaves an ordinary unbounded search through [0, 1, ...].
    In the kernel, termination is justified by the structurally recursive
    [before_witness] certificate used by [epsilon_smallest]; there is no
    axiom or special reduction rule for this search.

    This module deliberately separates the executable search (which only
    sees a monic sextic) from the algebraic proof of termination (which uses
    a tuple of distinct complex roots and Vieta's identities). *)
Module PolynomialFormulasSexticSeparatingSelector.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticComputedResolvents.
Import PolynomialFormulasSexticSeparatingSearch.
Import PolynomialFormulasSexticSeparatingExistence.

Definition bool_eq_true_dec (b : bool) : {b = true} + {b <> true}.
Proof. by case: b; [left | right]. Defined.

(** The least index at which a decidable Boolean test succeeds. *)
Definition first_true_choice (test : nat -> bool)
    (eventually : exists n, test n = true) :
    {n : nat | test n = true /\
      forall k, test k = true -> Nat.le n k} :=
  epsilon_smallest (fun n => test n = true)
    (fun n => bool_eq_true_dec (test n)) eventually.

Arguments first_true_choice test eventually : clear implicits.

Definition first_true_index (test : nat -> bool)
    (eventually : exists n, test n = true) : nat :=
  sval (first_true_choice test eventually).

Arguments first_true_index test eventually : clear implicits.

Lemma first_true_indexP test eventually :
  test (first_true_index test eventually) = true.
Proof.
exact: (proj1 (proj2_sig (first_true_choice test eventually))).
Qed.

Lemma first_true_index_minimal test eventually k :
  test k = true -> Nat.le (first_true_index test eventually) k.
Proof.
exact: (proj2 (proj2_sig (first_true_choice test eventually)) k).
Qed.

(** Although a termination proof occurs in the Coq term, the returned
    least index is independent of which proof was supplied. *)
Lemma first_true_index_proof_irrelevant test eventually1 eventually2 :
  first_true_index test eventually1 = first_true_index test eventually2.
Proof.
apply: Nat.le_antisymm.
- apply: first_true_index_minimal.
  exact: first_true_indexP.
- apply: first_true_index_minimal.
  exact: first_true_indexP.
Qed.

Section ExecutableSelectors.

(** These are the extraction-facing selectors.  The only computational
    input is [f]; [eventually] is a termination certificate in [Prop]. *)
Definition pair_separating_index (f : monic_sextic)
    (eventually : exists n,
      pair_separatesb f (parameter_at n) = true) : nat :=
  first_true_index
    (fun n => pair_separatesb f (parameter_at n)) eventually.

Arguments pair_separating_index f eventually : clear implicits.

Definition triple_separating_index (f : monic_sextic)
    (eventually : exists n,
      triple_separatesb f (parameter_at n) = true) : nat :=
  first_true_index
    (fun n => triple_separatesb f (parameter_at n)) eventually.

Arguments triple_separating_index f eventually : clear implicits.

Definition pair_separating_parameter (f : monic_sextic)
    (eventually : exists n,
      pair_separatesb f (parameter_at n) = true) : parameter :=
  parameter_at (pair_separating_index f eventually).

Arguments pair_separating_parameter f eventually : clear implicits.

Definition triple_separating_parameter (f : monic_sextic)
    (eventually : exists n,
      triple_separatesb f (parameter_at n) = true) : parameter :=
  parameter_at (triple_separating_index f eventually).

Arguments triple_separating_parameter f eventually : clear implicits.

Lemma pair_separating_indexP f eventually :
  pair_separatesb f (parameter_at
    (pair_separating_index f eventually)) = true.
Proof.
exact (@first_true_indexP
  (fun n => pair_separatesb f (parameter_at n)) eventually).
Qed.

Lemma triple_separating_indexP f eventually :
  triple_separatesb f (parameter_at
    (triple_separating_index f eventually)) = true.
Proof.
exact (@first_true_indexP
  (fun n => triple_separatesb f (parameter_at n)) eventually).
Qed.

Lemma pair_separating_parameterP f eventually :
  pair_separatesb f (pair_separating_parameter f eventually) = true.
Proof.
rewrite /pair_separating_parameter.
exact: pair_separating_indexP.
Qed.

Lemma triple_separating_parameterP f eventually :
  triple_separatesb f (triple_separating_parameter f eventually) = true.
Proof.
rewrite /triple_separating_parameter.
exact: triple_separating_indexP.
Qed.

Lemma pair_separating_index_minimal f eventually k :
  pair_separatesb f (parameter_at k) = true ->
  Nat.le (pair_separating_index f eventually) k.
Proof.
exact (@first_true_index_minimal
  (fun n => pair_separatesb f (parameter_at n)) eventually k).
Qed.

Lemma triple_separating_index_minimal f eventually k :
  triple_separatesb f (parameter_at k) = true ->
  Nat.le (triple_separating_index f eventually) k.
Proof.
exact (@first_true_index_minimal
  (fun n => triple_separatesb f (parameter_at n)) eventually k).
Qed.

End ExecutableSelectors.

Section AlgebraicTermination.

(** The earlier fuel-termination theorem implies termination of the more
    efficient index-by-index search used above. *)
Lemma pair_separating_eventually_true roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) :
  exists n, pair_separatesb f (parameter_at n) = true.
Proof.
have [fuel hfuel] := pair_separating_search_terminates hvieta hroots.
rewrite /pair_separating_up_to in hfuel.
move/hasP: hfuel=> [n _ hsep].
by exists n.
Qed.

Lemma triple_separating_eventually_true roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) :
  exists n, triple_separatesb f (parameter_at n) = true.
Proof.
have [fuel hfuel] := triple_separating_search_terminates hvieta hroots.
rewrite /triple_separating_up_to in hfuel.
move/hasP: hfuel=> [n _ hsep].
by exists n.
Qed.

Definition pair_separating_index_from_roots roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) : nat :=
  @pair_separating_index f
    (@pair_separating_eventually_true roots f hvieta hroots).

Definition triple_separating_index_from_roots roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) : nat :=
  @triple_separating_index f
    (@triple_separating_eventually_true roots f hvieta hroots).

Definition pair_separating_parameter_from_roots roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) : parameter :=
  @pair_separating_parameter f
    (@pair_separating_eventually_true roots f hvieta hroots).

Definition triple_separating_parameter_from_roots roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) : parameter :=
  @triple_separating_parameter f
    (@triple_separating_eventually_true roots f hvieta hroots).

Lemma pair_separating_parameter_from_rootsP roots f hvieta hroots :
  pair_separatesb f
    (@pair_separating_parameter_from_roots roots f hvieta hroots) = true.
Proof. exact: pair_separating_parameterP. Qed.

Lemma triple_separating_parameter_from_rootsP roots f hvieta hroots :
  triple_separatesb f
    (@triple_separating_parameter_from_roots roots f hvieta hroots) = true.
Proof. exact: triple_separating_parameterP. Qed.

Lemma pair_separating_parameter_from_roots_injective roots f hvieta hroots :
  pair_descriptor_injective roots
    (@pair_separating_parameter_from_roots roots f hvieta hroots).
Proof.
apply: (elimT (@pair_separatesP roots f
  (@pair_separating_parameter_from_roots roots f hvieta hroots) hvieta)).
exact: pair_separating_parameter_from_rootsP.
Qed.

Lemma triple_separating_parameter_from_roots_injective roots f hvieta hroots :
  triple_descriptor_injective roots
    (@triple_separating_parameter_from_roots roots f hvieta hroots).
Proof.
apply: (elimT (@triple_separatesP roots f
  (@triple_separating_parameter_from_roots roots f hvieta hroots) hvieta)).
exact: triple_separating_parameter_from_rootsP.
Qed.

End AlgebraicTermination.

End PolynomialFormulasSexticSeparatingSelector.
