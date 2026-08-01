From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From PolynomialFormulas Require Import SexticRecursiveCore SexticSparsePolynomials
  SexticSparseResolvents SexticNewtonPowerSums SexticResolventSymmetry
  SexticComputedResolvents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.
Local Open Scope ring_scope.

(** Executable collision products for finding scalar specializations whose
    pair- and triple-partition descriptor values are all distinct. *)
Module PolynomialFormulasSexticSeparatingSearch.

Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticResolventSymmetry.
Import PolynomialFormulasSexticComputedResolvents.

Definition pair_sparse_collision (x : parameter) : sparse_polynomial :=
  sparse_product
    [seq sparse_product
      [seq if p == q then sparse_const 1 else
        sparse_sub (pair_sparse_descriptor_value x p)
          (pair_sparse_descriptor_value x q)
      | q <- enum pair_partition]
    | p <- enum pair_partition].

Definition triple_sparse_collision (x : parameter) : sparse_polynomial :=
  sparse_product
    [seq sparse_product
      [seq if p == q then sparse_const 1 else
        sparse_sub (triple_sparse_descriptor_value x p)
          (triple_sparse_descriptor_value x q)
      | q <- enum triple_partition]
    | p <- enum triple_partition].

Section CollisionEvaluation.

Variable R : comNzRingType.

Definition collision_product {I : finType} (v : I -> R) : R :=
  \prod_(p : I) \prod_(q : I)
    if p == q then 1 else v p - v q.

Lemma pair_sparse_collision_eval values x :
  sparse_eval_ring values (pair_sparse_collision x) =
    collision_product (fun p : pair_partition =>
      sparse_eval_ring values (pair_sparse_descriptor_value x p)).
Proof.
rewrite /pair_sparse_collision /collision_product sparse_eval_ring_product
  big_map big_enum.
apply: eq_bigr=> p _.
rewrite sparse_eval_ring_product big_map big_enum.
apply: eq_bigr=> q _.
case hpq: (p == q).
- by rewrite sparse_eval_ring_const rmorph1.
- by rewrite sparse_eval_ring_sub.
Qed.

Lemma triple_sparse_collision_eval values x :
  sparse_eval_ring values (triple_sparse_collision x) =
    collision_product (fun p : triple_partition =>
      sparse_eval_ring values (triple_sparse_descriptor_value x p)).
Proof.
rewrite /triple_sparse_collision /collision_product sparse_eval_ring_product
  big_map big_enum.
apply: eq_bigr=> p _.
rewrite sparse_eval_ring_product big_map big_enum.
apply: eq_bigr=> q _.
case hpq: (p == q).
- by rewrite sparse_eval_ring_const rmorph1.
- by rewrite sparse_eval_ring_sub.
Qed.

End CollisionEvaluation.

Section CollisionInjectivity.

Variable R : idomainType.
Variable I : finType.

Lemma collision_product_neq0_iff (v : I -> R) :
  @collision_product R I v != 0 <-> injective v.
Proof.
split.
- move=> h a b hvab.
  case hab: (a == b); first exact: eqP hab.
  move: h; rewrite /collision_product.
  move/prodf_neq0=> houter.
  have hinner := houter a erefl.
  move/prodf_neq0: hinner=> hinner.
  have hfactor := hinner b erefl.
  by rewrite hab hvab subrr eqxx in hfactor.
- move=> hv; rewrite /collision_product.
  apply/prodf_neq0=> a _; apply/prodf_neq0=> b _.
  case hab: (a == b).
  + by rewrite oner_neq0.
  + rewrite subr_eq0; apply/negP=> /eqP heq.
    by move: hab; rewrite (hv a b heq) eqxx.
Qed.

End CollisionInjectivity.

Section CollisionSymmetry.

Variable R : comNzRingType.

Lemma pair_sparse_collision_tperm (roots : 6.-tuple R) x j :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (pair_sparse_collision x) =
    sparse_eval_ring roots (pair_sparse_collision x).
Proof.
rewrite !pair_sparse_collision_eval /collision_product.
under [LHS]eq_bigr=> p _ do
  under eq_bigr=> q _ do rewrite !pair_descriptor_tperm.
under [LHS]eq_bigr=> p _ do
  under eq_bigr=> q _ do
    rewrite -(inj_eq (@pair_partition_map_injective j)).
symmetry.
rewrite (reindex_inj (@pair_partition_map_injective j)).
under [LHS]eq_bigr=> p _ do
  rewrite (reindex_inj (@pair_partition_map_injective j)).
done.
Qed.

Lemma triple_sparse_collision_tperm (roots : 6.-tuple R) x j :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (triple_sparse_collision x) =
    sparse_eval_ring roots (triple_sparse_collision x).
Proof.
rewrite !triple_sparse_collision_eval /collision_product.
under [LHS]eq_bigr=> p _ do
  under eq_bigr=> q _ do rewrite !triple_descriptor_tperm.
under [LHS]eq_bigr=> p _ do
  under eq_bigr=> q _ do
    rewrite -(inj_eq (@triple_partition_map_injective j)).
symmetry.
rewrite (reindex_inj (@triple_partition_map_injective j)).
under [LHS]eq_bigr=> p _ do
  rewrite (reindex_inj (@triple_partition_map_injective j)).
done.
Qed.

Lemma pair_sparse_collision_perm x g :
  @sparse_permutation_invariant R (pair_sparse_collision x) g.
Proof.
apply: sparse_permutation_invariant_all=> j roots.
exact: pair_sparse_collision_tperm.
Qed.

Lemma triple_sparse_collision_perm x g :
  @sparse_permutation_invariant R (triple_sparse_collision x) g.
Proof.
apply: sparse_permutation_invariant_all=> j roots.
exact: triple_sparse_collision_tperm.
Qed.

Theorem pair_sparse_collision_invariant (roots : 6.-tuple R) x :
  permutation_invariant_at roots (pair_sparse_collision x).
Proof.
move=> a ha.
rewrite assignment_code_injectiveb in ha.
have hainj : injective a := elimT (@injectiveP _ _ a) ha.
pose g : {perm 'I_6} := perm hainj.
have havals : assignment_values roots a =
    assignment_values roots (finfun g).
  apply: eq_from_tnth=> k.
  by rewrite /assignment_values !tnth_mktuple !ffunE /g permE.
rewrite havals.
exact: pair_sparse_collision_perm.
Qed.

Theorem triple_sparse_collision_invariant (roots : 6.-tuple R) x :
  permutation_invariant_at roots (triple_sparse_collision x).
Proof.
move=> a ha.
rewrite assignment_code_injectiveb in ha.
have hainj : injective a := elimT (@injectiveP _ _ a) ha.
pose g : {perm 'I_6} := perm hainj.
have havals : assignment_values roots a =
    assignment_values roots (finfun g).
  apply: eq_from_tnth=> k.
  by rewrite /assignment_values !tnth_mktuple !ffunE /g permE.
rewrite havals.
exact: triple_sparse_collision_perm.
Qed.

End CollisionSymmetry.

Definition pair_scaled_collision_value
    (f : monic_sextic) (x : parameter) : int :=
  scaled_symmetric_value f (pair_sparse_collision x).

Definition triple_scaled_collision_value
    (f : monic_sextic) (x : parameter) : int :=
  scaled_symmetric_value f (triple_sparse_collision x).

Definition pair_separatesb (f : monic_sextic) (x : parameter) : bool :=
  pair_scaled_collision_value f x != 0.

Definition triple_separatesb (f : monic_sextic) (x : parameter) : bool :=
  triple_scaled_collision_value f x != 0.

Section ScaledCollisionCorrectness.

Variable R : comNzRingType.

Theorem pair_scaled_collision_value_correct roots f x :
  @cast_int_values R (monic_elementary_values f) =
      elementary_values roots ->
  (pair_scaled_collision_value f x)%:~R =
    720%:R * collision_product (fun p : pair_partition =>
      sparse_eval_ring roots (pair_sparse_descriptor_value x p)).
Proof.
move=> hvieta.
rewrite /pair_scaled_collision_value.
rewrite (@scaled_symmetric_value_correct R roots f
  (pair_sparse_collision x) hvieta
  (pair_sparse_collision_invariant roots x)).
by rewrite pair_sparse_collision_eval.
Qed.

Theorem triple_scaled_collision_value_correct roots f x :
  @cast_int_values R (monic_elementary_values f) =
      elementary_values roots ->
  (triple_scaled_collision_value f x)%:~R =
    720%:R * collision_product (fun p : triple_partition =>
      sparse_eval_ring roots (triple_sparse_descriptor_value x p)).
Proof.
move=> hvieta.
rewrite /triple_scaled_collision_value.
rewrite (@scaled_symmetric_value_correct R roots f
  (triple_sparse_collision x) hvieta
  (triple_sparse_collision_invariant roots x)).
by rewrite triple_sparse_collision_eval.
Qed.

End ScaledCollisionCorrectness.

Section SeparatingReflection.

Definition pair_descriptor_injective
    (roots : 6.-tuple algC) (x : parameter) : Prop :=
  injective (fun p : pair_partition =>
    sparse_eval_ring roots (pair_sparse_descriptor_value x p)).

Definition triple_descriptor_injective
    (roots : 6.-tuple algC) (x : parameter) : Prop :=
  injective (fun p : triple_partition =>
    sparse_eval_ring roots (triple_sparse_descriptor_value x p)).

Theorem pair_separatesP roots f x
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  reflect (pair_descriptor_injective roots x) (pair_separatesb f x).
Proof.
apply: (iffP idP).
- rewrite /pair_separatesb=> hvalue.
  have hcast : ((pair_scaled_collision_value f x)%:~R : algC) != 0.
    by rewrite intr_eq0.
  rewrite (@pair_scaled_collision_value_correct algC roots f x hvieta)
    mulf_eq0 negb_or in hcast.
  move/andP: hcast=> [_ hcollision].
  exact: (proj1 (collision_product_neq0_iff _)) hcollision.
- move=> hinjective.
  have hcollision :
      @collision_product algC pair_partition (fun p =>
        sparse_eval_ring roots (pair_sparse_descriptor_value x p)) != 0.
    exact: (proj2 (collision_product_neq0_iff _)) hinjective.
  have h720 : (720%:R : algC) != 0 by rewrite pnatr_eq0.
  have hcast : ((pair_scaled_collision_value f x)%:~R : algC) != 0.
    rewrite (@pair_scaled_collision_value_correct algC roots f x hvieta).
    exact: mulf_neq0 h720 hcollision.
  by move: hcast; rewrite intr_eq0.
Qed.

Theorem triple_separatesP roots f x
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  reflect (triple_descriptor_injective roots x) (triple_separatesb f x).
Proof.
apply: (iffP idP).
- rewrite /triple_separatesb=> hvalue.
  have hcast : ((triple_scaled_collision_value f x)%:~R : algC) != 0.
    by rewrite intr_eq0.
  rewrite (@triple_scaled_collision_value_correct algC roots f x hvieta)
    mulf_eq0 negb_or in hcast.
  move/andP: hcast=> [_ hcollision].
  exact: (proj1 (collision_product_neq0_iff _)) hcollision.
- move=> hinjective.
  have hcollision :
      @collision_product algC triple_partition (fun p =>
        sparse_eval_ring roots (triple_sparse_descriptor_value x p)) != 0.
    exact: (proj2 (collision_product_neq0_iff _)) hinjective.
  have h720 : (720%:R : algC) != 0 by rewrite pnatr_eq0.
  have hcast : ((triple_scaled_collision_value f x)%:~R : algC) != 0.
    rewrite (@triple_scaled_collision_value_correct algC roots f x hvieta).
    exact: mulf_neq0 h720 hcollision.
  by move: hcast; rewrite intr_eq0.
Qed.

End SeparatingReflection.

Section ParameterEnumeration.

Definition zero_parameter : parameter := [tuple 0; 0].

Definition parameter_at (n : nat) : parameter :=
  odflt zero_parameter (unpickle n).

Lemma parameter_at_pickle x : parameter_at (pickle x) = x.
Proof. by rewrite /parameter_at pickleK. Qed.

Definition pair_separating_up_to
    (f : monic_sextic) (fuel : nat) : bool :=
  has (fun n => pair_separatesb f (parameter_at n)) (iota 0 fuel).

Definition triple_separating_up_to
    (f : monic_sextic) (fuel : nat) : bool :=
  has (fun n => triple_separatesb f (parameter_at n)) (iota 0 fuel).

Lemma pair_separating_up_toP roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) fuel :
  reflect
    (exists n, (n < fuel)%N /\
      pair_descriptor_injective roots (parameter_at n))
    (pair_separating_up_to f fuel).
Proof.
apply: (iffP hasP).
- move=> [n].
  rewrite mem_iota add0n=> hn hsep.
  exists n; split=> //.
  exact: (elimT (@pair_separatesP roots f (parameter_at n) hvieta) hsep).
- move=> [n [hn hinj]].
  exists n; first by rewrite mem_iota add0n.
  exact: (introT (@pair_separatesP roots f (parameter_at n) hvieta) hinj).
Qed.

Lemma triple_separating_up_toP roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) fuel :
  reflect
    (exists n, (n < fuel)%N /\
      triple_descriptor_injective roots (parameter_at n))
    (triple_separating_up_to f fuel).
Proof.
apply: (iffP hasP).
- move=> [n].
  rewrite mem_iota add0n=> hn hsep.
  exists n; split=> //.
  exact: (elimT (@triple_separatesP roots f (parameter_at n) hvieta) hsep).
- move=> [n [hn hinj]].
  exists n; first by rewrite mem_iota add0n.
  exact: (introT (@triple_separatesP roots f (parameter_at n) hvieta) hinj).
Qed.

Theorem pair_separating_search_eventually roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  (exists x, pair_descriptor_injective roots x) ->
  exists fuel, pair_separating_up_to f fuel.
Proof.
move=> [x hx].
exists (pickle x).+1.
apply: (introT (@pair_separating_up_toP roots f hvieta (pickle x).+1)).
exists (pickle x); split; first exact: ltnSn.
by rewrite parameter_at_pickle.
Qed.

Theorem triple_separating_search_eventually roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  (exists x, triple_descriptor_injective roots x) ->
  exists fuel, triple_separating_up_to f fuel.
Proof.
move=> [x hx].
exists (pickle x).+1.
apply: (introT (@triple_separating_up_toP roots f hvieta (pickle x).+1)).
exists (pickle x); split; first exact: ltnSn.
by rewrite parameter_at_pickle.
Qed.

End ParameterEnumeration.

End PolynomialFormulasSexticSeparatingSearch.
