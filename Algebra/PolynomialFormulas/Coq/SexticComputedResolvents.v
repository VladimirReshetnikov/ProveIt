From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticSparsePolynomials SexticSparseResolvents SexticNewtonPowerSums
  SexticResolventSymmetry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Integer coefficient lists for the two sextic block-system resolvents.

    [newton_symmetrize] returns the sum over all 720 root permutations.  Thus
    an invariant resolvent coefficient is represented with the common factor
    720.  Retaining that common factor avoids division in [Z]; it does not
    change the roots of either resolvent in characteristic zero. *)
Module PolynomialFormulasSexticComputedResolvents.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticResolventSymmetry.

(** Vieta coordinates [e1,...,e6] for
    [X^6 + f5 X^5 + ... + f0]. *)
Definition monic_elementary_values (f : monic_sextic) : 6.-tuple int :=
  [tuple - f`_5; f`_4; - f`_3; f`_2; - f`_1; f`_0].

Definition scaled_symmetric_value
    (f : monic_sextic) (p : sparse_polynomial) : int :=
  sparse_eval_ring (R := int) (monic_elementary_values f)
    (newton_symmetrize p).

Definition pair_scaled_resolvent_coefficient
    (f : monic_sextic) (x : parameter) (i : 'I_16) : int :=
  scaled_symmetric_value f (pair_sparse_resolvent_coefficient x i).

Definition triple_scaled_resolvent_coefficient
    (f : monic_sextic) (x : parameter) (i : 'I_11) : int :=
  scaled_symmetric_value f (triple_sparse_resolvent_coefficient x i).

Definition pair_scaled_resolvent
    (f : monic_sextic) (x : parameter) : seq int :=
  [seq pair_scaled_resolvent_coefficient f x i | i <- enum 'I_16].

Definition triple_scaled_resolvent
    (f : monic_sextic) (x : parameter) : seq int :=
  [seq triple_scaled_resolvent_coefficient f x i | i <- enum 'I_11].

Lemma size_pair_scaled_resolvent f x :
  size (pair_scaled_resolvent f x) = 16%N.
Proof. by rewrite /pair_scaled_resolvent size_map size_enum_ord. Qed.

Lemma size_triple_scaled_resolvent f x :
  size (triple_scaled_resolvent f x) = 11%N.
Proof. by rewrite /triple_scaled_resolvent size_map size_enum_ord. Qed.

Section CastCorrectness.

Variable R : comPzRingType.

Definition cast_int_values (values : 6.-tuple int) : 6.-tuple R :=
  [tuple (tnth values i)%:~R | i < 6].

Lemma exponent_value_ring_cast values e :
  (exponent_value_ring (R := int) values e)%:~R =
    exponent_value_ring (cast_int_values values) e.
Proof.
rewrite /exponent_value_ring rmorph_prod.
apply: eq_bigr=> i _.
by rewrite rmorphXn /cast_int_values tnth_mktuple.
Qed.

Lemma sparse_eval_ring_cast values p :
  (sparse_eval_ring (R := int) values p)%:~R =
    sparse_eval_ring (cast_int_values values) p.
Proof.
rewrite /sparse_eval_ring rmorph_sum.
apply: eq_bigr=> t ht.
rewrite rmorphM.
apply f_equal2; first by rewrite rmorph_int.
exact: exponent_value_ring_cast.
Qed.

Theorem scaled_symmetric_value_correct roots f p :
  cast_int_values (monic_elementary_values f) = elementary_values roots ->
  permutation_invariant_at roots p ->
  (scaled_symmetric_value f p)%:~R =
    720%:R * sparse_eval_ring roots p.
Proof.
move=> hvieta hinv.
rewrite /scaled_symmetric_value sparse_eval_ring_cast hvieta.
exact: newton_symmetrize_invariant_correct.
Qed.

Theorem pair_scaled_resolvent_coefficient_correct roots f x i :
  cast_int_values (monic_elementary_values f) = elementary_values roots ->
  permutation_invariant_at roots (pair_sparse_resolvent_coefficient x i) ->
  (pair_scaled_resolvent_coefficient f x i)%:~R =
    720%:R *
      sparse_eval_ring roots (pair_sparse_resolvent_coefficient x i).
Proof. exact: scaled_symmetric_value_correct. Qed.

Theorem triple_scaled_resolvent_coefficient_correct roots f x i :
  cast_int_values (monic_elementary_values f) = elementary_values roots ->
  permutation_invariant_at roots (triple_sparse_resolvent_coefficient x i) ->
  (triple_scaled_resolvent_coefficient f x i)%:~R =
    720%:R *
      sparse_eval_ring roots (triple_sparse_resolvent_coefficient x i).
Proof. exact: scaled_symmetric_value_correct. Qed.

End CastCorrectness.

Section UnconditionalCorrectness.

Variable R : comNzRingType.

Theorem pair_scaled_resolvent_coefficient_correct_unconditional
    roots f x i :
  @cast_int_values R (monic_elementary_values f) =
      elementary_values roots ->
  (pair_scaled_resolvent_coefficient f x i)%:~R =
    720%:R *
      sparse_eval_ring roots (pair_sparse_resolvent_coefficient x i).
Proof.
move=> hvieta.
apply: (@pair_scaled_resolvent_coefficient_correct R roots f x i).
- exact hvieta.
exact: pair_sparse_resolvent_coefficient_invariant.
Qed.

Theorem triple_scaled_resolvent_coefficient_correct_unconditional
    roots f x i :
  @cast_int_values R (monic_elementary_values f) =
      elementary_values roots ->
  (triple_scaled_resolvent_coefficient f x i)%:~R =
    720%:R *
      sparse_eval_ring roots (triple_sparse_resolvent_coefficient x i).
Proof.
move=> hvieta.
apply: (@triple_scaled_resolvent_coefficient_correct R roots f x i).
- exact hvieta.
exact: triple_sparse_resolvent_coefficient_invariant.
Qed.

End UnconditionalCorrectness.

End PolynomialFormulasSexticComputedResolvents.
