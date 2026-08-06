From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticSparseResolvents SexticNewtonPowerSums SexticComputedResolvents
  SexticRationalRootSearch SexticSeparatingSearch
  SexticComputedResolventBridge SexticSeparatingExistence
  SexticBlockStabilizers SexticDescriptorAction SexticGaloisAction
  SexticSolvableCriterion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.
Local Notation ratrC := (@ratr algC).

(** A separating pair or triple descriptor detects exactly the corresponding
    block stabilizer inside the concrete permutation representation of an
    irreducible rational sextic's Galois group. *)
Module PolynomialFormulasSexticDescriptorGaloisCriterion.

Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticComputedResolvents.
Import PolynomialFormulasSexticRationalRootSearch.
Import PolynomialFormulasSexticSeparatingSearch.
Import PolynomialFormulasSexticSeparatingExistence.
Import PolynomialFormulasSexticComputedResolventBridge.
Import PolynomialFormulasSexticBlockStabilizers.
Import PolynomialFormulasSexticDescriptorAction.
Import PolynomialFormulasSexticGaloisAction.
Import PolynomialFormulasSexticSolvableCriterion.

Section MapEvaluation.

Variables (R S : comPzRingType) (h : {rmorphism R -> S}).

Lemma exponent_value_ring_map (values : 6.-tuple R) d :
  h (exponent_value_ring values d) =
    exponent_value_ring (map_tuple h values) d.
Proof.
rewrite /exponent_value_ring rmorph_prod.
apply: eq_bigr=> i _.
by rewrite rmorphXn tnth_map.
Qed.

Lemma sparse_eval_ring_map (values : 6.-tuple R) q :
  h (sparse_eval_ring values q) =
    sparse_eval_ring (map_tuple h values) q.
Proof.
rewrite /sparse_eval_ring rmorph_sum.
apply: eq_bigr=> t _.
by rewrite rmorphM rmorph_int exponent_value_ring_map.
Qed.

End MapEvaluation.

Section IrreducibleSextic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 7%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.
Let iota : {rmorphism L -> algC} := numfield_inC p.

Definition sextic_complex_root_tuple : 6.-tuple algC :=
  map_tuple iota (@sextic_root_tuple p p_size).

Lemma sextic_complex_root_tuple_injective :
  injective (tnth sextic_complex_root_tuple).
Proof.
move=> i j; rewrite /sextic_complex_root_tuple !tnth_map=> hij.
apply: (@sextic_root_tuple_injective p p_size p_irr).
exact: (fmorph_inj iota hij).
Qed.

Definition pair_descriptor_L (x : parameter) (q : pair_partition) : L :=
  sparse_eval_ring (@sextic_root_tuple p p_size)
    (pair_sparse_descriptor_value x q).

Definition triple_descriptor_L (x : parameter) (q : triple_partition) : L :=
  sparse_eval_ring (@sextic_root_tuple p p_size)
    (triple_sparse_descriptor_value x q).

Definition pair_descriptor_C (x : parameter) (q : pair_partition) : algC :=
  sparse_eval_ring sextic_complex_root_tuple
    (pair_sparse_descriptor_value x q).

Definition triple_descriptor_C
    (x : parameter) (q : triple_partition) : algC :=
  sparse_eval_ring sextic_complex_root_tuple
    (triple_sparse_descriptor_value x q).

Lemma pair_descriptor_inC x q :
  iota (pair_descriptor_L x q) = pair_descriptor_C x q.
Proof. exact: sparse_eval_ring_map. Qed.

Lemma triple_descriptor_inC x q :
  iota (triple_descriptor_L x q) = triple_descriptor_C x q.
Proof. exact: sparse_eval_ring_map. Qed.

Lemma map_tuple_sextic_gal (g : gal_of {:L}) :
  map_tuple g (@sextic_root_tuple p p_size) =
    assignment_values (@sextic_root_tuple p p_size)
      (finfun (@sextic_gal_perm p p_size g)).
Proof.
apply: eq_from_tnth=> i.
rewrite tnth_map /assignment_values tnth_mktuple ffunE.
by rewrite (@sextic_gal_permP p p_size g i).
Qed.

Lemma pair_descriptor_gal (g : gal_of {:L}) x q :
  g (pair_descriptor_L x q) =
    pair_descriptor_L x
      (pair_partition_action (@sextic_gal_perm p p_size g) q).
Proof.
rewrite /pair_descriptor_L
  (@sparse_eval_ring_map L L g) map_tuple_sextic_gal.
exact: pair_descriptor_perm.
Qed.

Lemma triple_descriptor_gal (g : gal_of {:L}) x q :
  g (triple_descriptor_L x q) =
    triple_descriptor_L x
      (triple_partition_action (@sextic_gal_perm p p_size g) q).
Proof.
rewrite /triple_descriptor_L
  (@sparse_eval_ring_map L L g) map_tuple_sextic_gal.
exact: triple_descriptor_perm.
Qed.

Lemma pair_descriptor_rational_iff_stabilizer x q
    (hsep : pair_descriptor_injective sextic_complex_root_tuple x) :
  (exists r : rat, pair_descriptor_C x q = ratrC r) <->
  @sextic_galois_image p p_size p_irr \subset pair_table_group q.
Proof.
split.
- move=> [r hr].
  have hfixed : forall g, g \in 'Gal({:L} / 1%AS)%G ->
      g (pair_descriptor_L x q) = pair_descriptor_L x q.
    apply: (proj2 (@fixed_iff_rational p (pair_descriptor_L x q))).
    exists r.
    by rewrite pair_descriptor_inC.
  apply/subsetP=> s.
  rewrite /sextic_galois_image.
  move=> /morphimP[g _ gg hs]; subst s.
  apply/pair_partition_action_fixedP.
  apply: hsep.
  change (pair_descriptor_C x
    (pair_partition_action (@sextic_gal_perm p p_size g) q) =
    pair_descriptor_C x q).
  rewrite -!pair_descriptor_inC.
  by rewrite -pair_descriptor_gal (hfixed g gg).
- move=> hsub.
  have hfixed : forall g, g \in 'Gal({:L} / 1%AS)%G ->
      g (pair_descriptor_L x q) = pair_descriptor_L x q.
    move=> g gg.
    rewrite pair_descriptor_gal.
    have hgimage : @sextic_gal_perm p p_size g \in
        @sextic_galois_image p p_size p_irr.
      rewrite /sextic_galois_image.
      apply/morphimP; by exists g.
    have hgstab := subsetP hsub _ hgimage.
    by move/pair_partition_action_fixedP: hgstab=> ->.
  have [r hr] :=
    (proj1 (@fixed_iff_rational p (pair_descriptor_L x q)) hfixed).
  exists r.
  by rewrite -pair_descriptor_inC.
Qed.

Lemma triple_descriptor_rational_iff_stabilizer x q
    (hsep : triple_descriptor_injective sextic_complex_root_tuple x) :
  (exists r : rat, triple_descriptor_C x q = ratrC r) <->
  @sextic_galois_image p p_size p_irr \subset triple_table_group q.
Proof.
split.
- move=> [r hr].
  have hfixed : forall g, g \in 'Gal({:L} / 1%AS)%G ->
      g (triple_descriptor_L x q) = triple_descriptor_L x q.
    apply: (proj2 (@fixed_iff_rational p (triple_descriptor_L x q))).
    exists r.
    by rewrite triple_descriptor_inC.
  apply/subsetP=> s.
  rewrite /sextic_galois_image.
  move=> /morphimP[g _ gg hs]; subst s.
  apply/triple_partition_action_fixedP.
  apply: hsep.
  change (triple_descriptor_C x
    (triple_partition_action (@sextic_gal_perm p p_size g) q) =
    triple_descriptor_C x q).
  rewrite -!triple_descriptor_inC.
  by rewrite -triple_descriptor_gal (hfixed g gg).
- move=> hsub.
  have hfixed : forall g, g \in 'Gal({:L} / 1%AS)%G ->
      g (triple_descriptor_L x q) = triple_descriptor_L x q.
    move=> g gg.
    rewrite triple_descriptor_gal.
    have hgimage : @sextic_gal_perm p p_size g \in
        @sextic_galois_image p p_size p_irr.
      rewrite /sextic_galois_image.
      apply/morphimP; by exists g.
    have hgstab := subsetP hsub _ hgimage.
    by move/triple_partition_action_fixedP: hgstab=> ->.
  have [r hr] :=
    (proj1 (@fixed_iff_rational p (triple_descriptor_L x q)) hfixed).
  exists r.
  by rewrite -triple_descriptor_inC.
Qed.

Lemma pair_has_rational_descriptor_iff_stabilizer x
    (hsep : pair_descriptor_injective sextic_complex_root_tuple x) :
  pair_has_rational_descriptor sextic_complex_root_tuple x <->
    exists q, @sextic_galois_image p p_size p_irr \subset
      pair_table_group q.
Proof.
rewrite /pair_has_rational_descriptor.
split.
- move=> [q [r hr]]; exists q.
  have hrat : exists r0 : rat, pair_descriptor_C x q = ratrC r0.
    exists r.
    change (pair_descriptor_C x q = ratrC r) in hr.
    exact: hr.
  have hstab := (proj1 (@pair_descriptor_rational_iff_stabilizer
    x q hsep) hrat).
  exact: hstab.
- move=> [q hq]; exists q.
  have [r hr] :=
    (proj2 (@pair_descriptor_rational_iff_stabilizer
      x q hsep) hq).
  exists r.
  change (pair_descriptor_C x q = ratrC r).
  exact: hr.
Qed.

Lemma triple_has_rational_descriptor_iff_stabilizer x
    (hsep : triple_descriptor_injective sextic_complex_root_tuple x) :
  triple_has_rational_descriptor sextic_complex_root_tuple x <->
    exists q, @sextic_galois_image p p_size p_irr \subset
      triple_table_group q.
Proof.
rewrite /triple_has_rational_descriptor.
split.
- move=> [q [r hr]]; exists q.
  have hrat : exists r0 : rat, triple_descriptor_C x q = ratrC r0.
    exists r.
    change (triple_descriptor_C x q = ratrC r) in hr.
    exact: hr.
  exact: (proj1 (@triple_descriptor_rational_iff_stabilizer
    x q hsep) hrat).
- move=> [q hq]; exists q.
  have [r hr] :=
    (proj2 (@triple_descriptor_rational_iff_stabilizer
      x q hsep) hq).
  exists r.
  change (triple_descriptor_C x q = ratrC r).
  exact: hr.
Qed.

Theorem sextic_galois_solvable_iff_rational_descriptors xpair xtriple
    (hpair : pair_descriptor_injective sextic_complex_root_tuple xpair)
    (htriple : triple_descriptor_injective sextic_complex_root_tuple xtriple) :
  solvable 'Gal({:L} / 1%AS) <->
    pair_has_rational_descriptor sextic_complex_root_tuple xpair \/
    triple_has_rational_descriptor sextic_complex_root_tuple xtriple.
Proof.
rewrite (pair_has_rational_descriptor_iff_stabilizer hpair).
rewrite (triple_has_rational_descriptor_iff_stabilizer htriple).
rewrite -(@sextic_galois_image_solvableE p p_size p_irr).
exact: solvable_transitive_S6_criterion
  (@sextic_galois_image_transitive p p_size p_irr).
Qed.

Theorem sextic_scaled_resolvent_solvableP
    (f : monic_sextic) xpair xtriple
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values sextic_complex_root_tuple)
    (hpair : pair_descriptor_injective sextic_complex_root_tuple xpair)
    (htriple : triple_descriptor_injective sextic_complex_root_tuple xtriple) :
  reflect (solvable 'Gal({:L} / 1%AS))
    (pair_scaled_rational_rootb f xpair ||
      triple_scaled_rational_rootb f xtriple).
Proof.
have hcriterion :=
  @sextic_galois_solvable_iff_rational_descriptors
    xpair xtriple hpair htriple.
apply: (iffP orP).
- move=> [hpair_root | htriple_root].
  + apply: (proj2 hcriterion); left.
    exact: (elimT (@pair_scaled_rational_descriptorP
      sextic_complex_root_tuple f xpair hvieta) hpair_root).
  + apply: (proj2 hcriterion); right.
    exact: (elimT (@triple_scaled_rational_descriptorP
      sextic_complex_root_tuple f xtriple hvieta) htriple_root).
- move=> hsolvable.
  case: (proj1 hcriterion hsolvable)=> [hpair_rat | htriple_rat].
  + have hb := (introT (@pair_scaled_rational_descriptorP
      sextic_complex_root_tuple f xpair hvieta) hpair_rat).
    by left.
  + have hb := (introT (@triple_scaled_rational_descriptorP
      sextic_complex_root_tuple f xtriple hvieta) htriple_rat).
    by right.
Qed.

End IrreducibleSextic.

End PolynomialFormulasSexticDescriptorGaloisCriterion.
