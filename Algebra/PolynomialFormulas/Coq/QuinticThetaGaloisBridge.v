From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaOrbit QuinticThetaValues
  QuinticGaloisAction QuinticGaloisCriterion
  SexticGaloisAction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The scalar theta values inherit the permutation action on the five
    canonical roots.  Injectivity of the six specialized values then turns
    a fixed theta value into exactly a stable inverse-representative orbit. *)
Module PolynomialFormulasQuinticThetaGaloisBridge.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasQuinticThetaOrbit.
Import PolynomialFormulasQuinticThetaValues.
Import PolynomialFormulasQuinticGaloisAction.
Import PolynomialFormulasQuinticGaloisCriterion.
Import PolynomialFormulasSexticGaloisAction.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.
Local Notation ratrC := (@ratr algC).

Section MapValues.

Variables (R S : comNzRingType) (h : {rmorphism R -> S}).

Lemma quintic_monomial_value_map (roots : 5.-tuple R) d :
  h (quintic_monomial_value roots d) =
    quintic_monomial_value (map_tuple h roots) d.
Proof.
rewrite /quintic_monomial_value rmorph_prod.
apply: eq_bigr=> i _.
by rewrite rmorphXn tnth_map.
Qed.

Lemma quintic_table_value_map (roots : 5.-tuple R) table :
  h (quintic_table_value roots table) =
    quintic_table_value (map_tuple h roots) table.
Proof.
rewrite /quintic_table_value rmorph_sum.
apply: eq_bigr=> d _.
exact: quintic_monomial_value_map.
Qed.

Lemma quintic_theta_value_map (roots : 5.-tuple R) i :
  h (quintic_theta_value roots i) =
    quintic_theta_value (map_tuple h roots) i.
Proof. exact: quintic_table_value_map. Qed.

End MapValues.

Section IrreducibleQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.
Let iota : {rmorphism L -> algC} := numfield_inC p.
Let roots := @quintic_root_tuple p p_size.
Let G := @quintic_galois_image p p_size p_irr.

Definition quintic_complex_root_tuple : 5.-tuple algC :=
  map_tuple iota roots.

Lemma quintic_theta_value_inC i :
  iota (quintic_theta_value roots i) =
    quintic_theta_value quintic_complex_root_tuple i.
Proof. exact: quintic_theta_value_map. Qed.

Lemma map_tuple_quintic_gal (g : gal_of {:L}) :
  map_tuple g roots =
    permute_quintic_roots (@quintic_gal_perm p p_size g) roots.
Proof.
apply: eq_from_tnth=> i.
rewrite tnth_map tnth_permute_quintic_roots.
exact: esym (@quintic_gal_permP p p_size g i).
Qed.

(** Applying a field automorphism to a theta value is exactly the explicit
    six-point index action induced by its permutation of the five roots. *)
Lemma quintic_theta_value_gal (g : gal_of {:L}) i :
  g (quintic_theta_value roots i) =
    quintic_theta_value roots
      (quintic_theta_index_action
        (@quintic_gal_perm p p_size g) i).
Proof.
rewrite quintic_theta_value_map map_tuple_quintic_gal.
exact: quintic_theta_value_permute.
Qed.

(** Fixing index [i] in the explicit six-point action is the pointwise form
    of stabilizing its inverse-representative theta orbit. *)
Lemma quintic_theta_index_action_fixedP g i :
  reflect (quintic_theta_index_action g i = i)
    (g \in (standard_F20 :^ (representative i)^-1)).
Proof.
apply: (iffP idP).
- move=> hg.
  have hperm : perm_eq
      (act_theta_table g^-1 (inverse_representative_theta_orbit i))
      (inverse_representative_theta_orbit i).
    move: hg.
    by rewrite act_inverse_representative_theta_orbitP groupV.
  have horbit :=
    theta_table_orbit_exhaustive (((representative i)^-1 * g)%g).
  have horbit0 : perm_eq
      (theta_table_image (((representative i)^-1 * g)%g))
      (theta_table_image
        ((representative
          (quintic_theta_index_action g i))^-1)).
    exact: horbit.
  have hraw : perm_eq
      (theta_table_image (((representative i)^-1 * g)%g))
      (theta_table_image ((representative i)^-1)).
    move: hperm.
    by rewrite /act_theta_table /inverse_representative_theta_orbit
      invgK -theta_table_image_mul.
  have horbit' : perm_eq
      (theta_table_image
        ((representative
          (quintic_theta_index_action g i))^-1))
      (theta_table_image ((representative i)^-1)).
    move/seq.permP: horbit0=> horbit0P.
    move/seq.permP: hraw=> hrawP.
    apply/seq.permP.
    move=> d.
    exact: eq_trans (esym (horbit0P d)) (hrawP d).
  exact: inverse_representative_theta_orbits_perm_injective horbit'.
- move=> hindex.
  rewrite /quintic_theta_index_action in hindex.
  have horbit :=
    theta_table_orbit_exhaustive (((representative i)^-1 * g)%g).
  have hperm : perm_eq
      (act_theta_table g^-1 (inverse_representative_theta_orbit i))
      (inverse_representative_theta_orbit i).
    rewrite /act_theta_table /inverse_representative_theta_orbit
      invgK -theta_table_image_mul.
    move: horbit.
    by rewrite hindex.
  move: hperm.
  by rewrite act_inverse_representative_theta_orbitP groupV.
Qed.

Hypothesis theta_injective :
  injective (quintic_theta_value roots).

(** A specialized theta value is fixed by the full Galois group exactly
    when the corresponding inverse-representative orbit is stable under the
    concrete permutation image. *)
Theorem quintic_theta_value_fixed_iff_stable i :
  ((forall g : gal_of {:L}, g \in 'Gal({:L} / 1%AS)%G ->
      g (quintic_theta_value roots i) = quintic_theta_value roots i) <->
    theta_orbit_stableb G i).
Proof.
rewrite theta_orbit_stablebE.
split.
- move=> hfixed.
  apply/subsetP=> s.
  rewrite /G /quintic_galois_image.
  move=> /morphimP[g _ gg ->].
  apply/quintic_theta_index_action_fixedP.
  apply: theta_injective.
  rewrite -quintic_theta_value_gal.
  exact: hfixed g gg.
- move=> hstable g gg.
  have hgimage : @quintic_gal_perm p p_size g \in G.
    rewrite /G /quintic_galois_image.
    apply/morphimP; by exists g.
  have hindex :
      quintic_theta_index_action (@quintic_gal_perm p p_size g) i = i.
    apply/quintic_theta_index_action_fixedP.
    exact: subsetP hstable _ hgimage.
  by rewrite quintic_theta_value_gal hindex.
Qed.

Theorem exists_fixed_quintic_theta_value_iff_galois_solvable :
  ((exists i : 'I_6,
      forall g : gal_of {:L}, g \in 'Gal({:L} / 1%AS)%G ->
        g (quintic_theta_value roots i) = quintic_theta_value roots i) <->
    solvable 'Gal({:L} / 1%AS)).
Proof.
rewrite (@quintic_galois_solvable_iff_stable_theta_orbit
  p p_size p_irr).
split.
- move=> [i hi]; exists i.
  exact: (proj1 (quintic_theta_value_fixed_iff_stable i) hi).
- move=> [i hi]; exists i.
  exact: (proj2 (quintic_theta_value_fixed_iff_stable i) hi).
Qed.

Lemma quintic_theta_value_rational_iff_fixed i :
  ((exists q : rat, quintic_theta_value roots i = in_alg L q) <->
    forall g : gal_of {:L}, g \in 'Gal({:L} / 1%AS)%G ->
      g (quintic_theta_value roots i) = quintic_theta_value roots i).
Proof.
rewrite (@fixed_iff_rational p (quintic_theta_value roots i)).
split.
- move=> [q ->]; exists q.
  exact: numfield_inC_in_alg.
- move=> [q hq]; exists q.
  apply: (fmorph_inj iota).
  by rewrite hq numfield_inC_in_alg.
Qed.

(** One of the six theta values lies in the rational prime field exactly
    when the quintic Galois group is solvable. *)
Theorem exists_rational_quintic_theta_value_iff_galois_solvable :
  ((exists i : 'I_6, exists q : rat,
      quintic_theta_value roots i = in_alg L q) <->
    solvable 'Gal({:L} / 1%AS)).
Proof.
rewrite -exists_fixed_quintic_theta_value_iff_galois_solvable.
split.
- move=> [i hi]; exists i.
  exact: (proj1 (quintic_theta_value_rational_iff_fixed i) hi).
- move=> [i hi]; exists i.
  exact: (proj2 (quintic_theta_value_rational_iff_fixed i) hi).
Qed.

(** Equivalently, the scalar resolvent has a root in the rational prime
    field exactly when the quintic Galois group is solvable. *)
Theorem quintic_scalar_resolvent_has_rational_root_iff_galois_solvable :
  ((exists q : rat,
      root (quintic_scalar_resolvent roots) (in_alg L q)) <->
    solvable 'Gal({:L} / 1%AS)).
Proof.
rewrite -exists_rational_quintic_theta_value_iff_galois_solvable.
split.
- move=> [q hq].
  have [i hi] :=
    (proj1 (quintic_scalar_resolvent_root_iff roots (in_alg L q)) hq).
  by exists i; exists q.
- move=> [i [q hi]]; exists q.
  apply: (proj2 (quintic_scalar_resolvent_root_iff roots (in_alg L q))).
  by exists i.
Qed.

End IrreducibleQuintic.

End PolynomialFormulasQuinticThetaGaloisBridge.
