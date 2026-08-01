From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From PolynomialFormulas Require Import SexticSparsePolynomials
  SexticSparseResolvents SexticNewtonPowerSums SexticResolventSymmetry
  SexticComputedResolvents SexticRationalRootSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.
Local Open Scope ring_scope.

(** The executable integer coefficient lists compute the semantic pair and
    triple resolvents, up to the common factor [720] introduced by summing
    over all root permutations. *)
Module PolynomialFormulasSexticComputedResolventBridge.

Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticResolventSymmetry.
Import PolynomialFormulasSexticComputedResolvents.
Import PolynomialFormulasSexticRationalRootSearch.

Section Correctness.

Variable R : comNzRingType.

Theorem pair_scaled_resolvent_poly_correct roots f x :
  @cast_int_values R (monic_elementary_values f) =
      elementary_values roots ->
  map_poly (intr : int -> R)
      (coefficient_list_poly_int (pair_scaled_resolvent f x)) =
    720%:R *: coefficient_list_poly roots (pair_sparse_resolvent x).
Proof.
move=> hvieta; apply/polyP=> i.
rewrite coef_map coefficient_list_poly_int_coef coefZ
  coefficient_list_poly_coef.
case hi: (i < 16)%N.
- rewrite /pair_scaled_resolvent (nth_map ord0) ?size_enum_ord //.
  have hoi : nth ord0 (enum 'I_16) i = Ordinal hi.
    by apply: val_inj; rewrite /= nth_enum_ord.
  rewrite hoi /pair_sparse_resolvent_coefficient.
  exact: (@pair_scaled_resolvent_coefficient_correct_unconditional
    R roots f x (Ordinal hi) hvieta).
- have h16i : (16 <= i)%N by rewrite leqNgt hi.
  rewrite nth_default ?size_pair_scaled_resolvent //.
  rewrite nth_default ?size_pair_sparse_resolvent //.
  by rewrite sparse_eval_ring_zero mulr0.
Qed.

Theorem triple_scaled_resolvent_poly_correct roots f x :
  @cast_int_values R (monic_elementary_values f) =
      elementary_values roots ->
  map_poly (intr : int -> R)
      (coefficient_list_poly_int (triple_scaled_resolvent f x)) =
    720%:R *: coefficient_list_poly roots (triple_sparse_resolvent x).
Proof.
move=> hvieta; apply/polyP=> i.
rewrite coef_map coefficient_list_poly_int_coef coefZ
  coefficient_list_poly_coef.
case hi: (i < 11)%N.
- rewrite /triple_scaled_resolvent (nth_map ord0) ?size_enum_ord //.
  have hoi : nth ord0 (enum 'I_11) i = Ordinal hi.
    by apply: val_inj; rewrite /= nth_enum_ord.
  rewrite hoi /triple_sparse_resolvent_coefficient.
  exact: (@triple_scaled_resolvent_coefficient_correct_unconditional
    R roots f x (Ordinal hi) hvieta).
- have h11i : (11 <= i)%N by rewrite leqNgt hi.
  rewrite nth_default ?size_triple_scaled_resolvent //.
  rewrite nth_default ?size_triple_sparse_resolvent //.
  by rewrite sparse_eval_ring_zero mulr0.
Qed.

End Correctness.

Section RationalRoots.

Local Notation ratrC := (@ratr algC).

Definition pair_semantic_has_rational_root
    (roots : 6.-tuple algC) (x : parameter) : Prop :=
  exists q : rat,
    (coefficient_list_poly roots (pair_sparse_resolvent x)).[ratrC q] = 0.

Definition triple_semantic_has_rational_root
    (roots : 6.-tuple algC) (x : parameter) : Prop :=
  exists q : rat,
    (coefficient_list_poly roots (triple_sparse_resolvent x)).[ratrC q] = 0.

Definition pair_has_rational_descriptor
    (roots : 6.-tuple algC) (x : parameter) : Prop :=
  exists p : pair_partition, exists q : rat,
    sparse_eval_ring roots (pair_sparse_descriptor_value x p) = ratrC q.

Definition triple_has_rational_descriptor
    (roots : 6.-tuple algC) (x : parameter) : Prop :=
  exists p : triple_partition, exists q : rat,
    sparse_eval_ring roots (triple_sparse_descriptor_value x p) = ratrC q.

Lemma pair_semantic_root_iff_rational_descriptor roots x :
  pair_semantic_has_rational_root roots x <->
    pair_has_rational_descriptor roots x.
Proof.
rewrite /pair_semantic_has_rational_root /pair_has_rational_descriptor.
split.
- move=> [q hq].
  rewrite coefficient_list_poly_pair_resolvent horner_prod in hq.
  have hprod :
      (\prod_(p : pair_partition)
        ('X - (sparse_eval_ring roots
          (pair_sparse_descriptor_value x p))%:P).[ratrC q]) == 0
      by exact/eqP.
  move/prodf_eq0: hprod=> [p _ hp].
  exists p, q; move: hp.
  rewrite hornerXsubC subr_eq0=> /eqP hp.
  exact: esym hp.
- move=> [p [q hp]]; exists q.
  rewrite coefficient_list_poly_pair_resolvent horner_prod.
  apply/eqP; apply/prodf_eq0; exists p=> //.
  apply/eqP.
  by rewrite hornerXsubC hp subrr.
Qed.

Lemma triple_semantic_root_iff_rational_descriptor roots x :
  triple_semantic_has_rational_root roots x <->
    triple_has_rational_descriptor roots x.
Proof.
rewrite /triple_semantic_has_rational_root /triple_has_rational_descriptor.
split.
- move=> [q hq].
  rewrite coefficient_list_poly_triple_resolvent horner_prod in hq.
  have hprod :
      (\prod_(p : triple_partition)
        ('X - (sparse_eval_ring roots
          (triple_sparse_descriptor_value x p))%:P).[ratrC q]) == 0
      by exact/eqP.
  move/prodf_eq0: hprod=> [p _ hp].
  exists p, q; move: hp.
  rewrite hornerXsubC subr_eq0=> /eqP hp.
  exact: esym hp.
- move=> [p [q hp]]; exists q.
  rewrite coefficient_list_poly_triple_resolvent horner_prod.
  apply/eqP; apply/prodf_eq0; exists p=> //.
  apply/eqP.
  by rewrite hornerXsubC hp subrr.
Qed.

Lemma int_poly_horner_ratr (p : {poly int}) q :
  (map_poly (intr : int -> algC) p).[ratrC q] =
    ratrC ((map_poly (intr : int -> rat) p).[q]).
Proof.
rewrite -horner_map -map_poly_comp.
apply: (congr1 (fun r : {poly algC} => r.[ratrC q])).
apply/polyP=> i.
by rewrite !coef_map /= ratr_int.
Qed.

Theorem pair_scaled_resolvent_has_rational_root_correct roots f x :
  @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots ->
  has_rational_root (pair_scaled_resolvent f x) <->
    pair_semantic_has_rational_root roots x.
Proof.
move=> hvieta; split=> [[q hq]|[q hq]]; exists q.
- have hp := congr1 (fun p : {poly algC} => p.[ratrC q])
    (@pair_scaled_resolvent_poly_correct algC roots f x hvieta).
  rewrite int_poly_horner_ratr hq rmorph0 hornerZ in hp.
  have h720 : (720%:R : algC) != 0 by rewrite pnatr_eq0.
  have hprod : 720%:R *
      (coefficient_list_poly roots (pair_sparse_resolvent x)).[ratrC q] = 0
      by exact: esym hp.
  move/eqP: hprod; rewrite mulf_eq0 (negPf h720) /=.
  by move=> /eqP.
- have hp := congr1 (fun p : {poly algC} => p.[ratrC q])
    (@pair_scaled_resolvent_poly_correct algC roots f x hvieta).
  rewrite int_poly_horner_ratr hornerZ hq mulr0 in hp.
  apply: (fmorph_inj ratrC).
  by rewrite rmorph0.
Qed.

Theorem triple_scaled_resolvent_has_rational_root_correct roots f x :
  @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots ->
  has_rational_root (triple_scaled_resolvent f x) <->
    triple_semantic_has_rational_root roots x.
Proof.
move=> hvieta; split=> [[q hq]|[q hq]]; exists q.
- have hp := congr1 (fun p : {poly algC} => p.[ratrC q])
    (@triple_scaled_resolvent_poly_correct algC roots f x hvieta).
  rewrite int_poly_horner_ratr hq rmorph0 hornerZ in hp.
  have h720 : (720%:R : algC) != 0 by rewrite pnatr_eq0.
  have hprod : 720%:R *
      (coefficient_list_poly roots (triple_sparse_resolvent x)).[ratrC q] = 0
      by exact: esym hp.
  move/eqP: hprod; rewrite mulf_eq0 (negPf h720) /=.
  by move=> /eqP.
- have hp := congr1 (fun p : {poly algC} => p.[ratrC q])
    (@triple_scaled_resolvent_poly_correct algC roots f x hvieta).
  rewrite int_poly_horner_ratr hornerZ hq mulr0 in hp.
  apply: (fmorph_inj ratrC).
  by rewrite rmorph0.
Qed.

Theorem pair_scaled_semantic_rational_rootP roots f x
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  reflect (pair_semantic_has_rational_root roots x)
    (pair_scaled_rational_rootb f x).
Proof.
apply: (iffP (pair_scaled_rational_rootP f x)).
- exact: (proj1 (@pair_scaled_resolvent_has_rational_root_correct
    roots f x hvieta)).
- exact: (proj2 (@pair_scaled_resolvent_has_rational_root_correct
    roots f x hvieta)).
Qed.

Theorem triple_scaled_semantic_rational_rootP roots f x
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  reflect (triple_semantic_has_rational_root roots x)
    (triple_scaled_rational_rootb f x).
Proof.
apply: (iffP (triple_scaled_rational_rootP f x)).
- exact: (proj1 (@triple_scaled_resolvent_has_rational_root_correct
    roots f x hvieta)).
- exact: (proj2 (@triple_scaled_resolvent_has_rational_root_correct
    roots f x hvieta)).
Qed.

Theorem pair_scaled_rational_descriptorP roots f x
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  reflect (pair_has_rational_descriptor roots x)
    (pair_scaled_rational_rootb f x).
Proof.
apply: (iffP (@pair_scaled_semantic_rational_rootP roots f x hvieta)).
- exact: (proj1 (pair_semantic_root_iff_rational_descriptor roots x)).
- exact: (proj2 (pair_semantic_root_iff_rational_descriptor roots x)).
Qed.

Theorem triple_scaled_rational_descriptorP roots f x
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  reflect (triple_has_rational_descriptor roots x)
    (triple_scaled_rational_rootb f x).
Proof.
apply: (iffP (@triple_scaled_semantic_rational_rootP roots f x hvieta)).
- exact: (proj1 (triple_semantic_root_iff_rational_descriptor roots x)).
- exact: (proj2 (triple_semantic_root_iff_rational_descriptor roots x)).
Qed.

End RationalRoots.

End PolynomialFormulasSexticComputedResolventBridge.
