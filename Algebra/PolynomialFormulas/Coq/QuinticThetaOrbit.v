From mathcomp Require Import all_ssreflect all_fingroup all_solvable.
From PolynomialFormulas Require Import QuinticF20Data.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The six values in the Dummit resolvent are indexed by inverse left-coset
    representatives.  This inverse is forced by the convention

      [act_exponent (s * t) = act_exponent t \o act_exponent s].

    The lemmas below isolate that orientation issue from the later polynomial
    argument. *)
Module PolynomialFormulasQuinticThetaOrbit.

Import PolynomialFormulasQuinticF20Data.

Local Open Scope group_scope.

(** Applying the same exponent permutation to two permutation-equal tables
    preserves permutation equality.  Consequently, equality of two theta
    orbits is measured by the indicated right quotient. *)
Lemma theta_table_images_perm_implies_F20 s t :
  perm_eq (theta_table_image s) (theta_table_image t) ->
  t * s^-1 \in standard_F20.
Proof.
move=> hst.
have hmap := perm_map (act_exponent s^-1) hst.
rewrite -!theta_table_image_mul mulgV theta_table_image_one in hmap.
have hstab : theta_stabilizesb (t * s^-1).
  apply: theta_perm_stabilizesb.
  by move: hmap; rewrite perm_sym.
have hmem : t * s^-1 \in theta_stabilizer.
  by rewrite mem_theta_stabilizer.
by move: hmem; rewrite theta_stabilizerE.
Qed.

Lemma theta_table_images_perm_of_F20 s t :
  t * s^-1 \in standard_F20 ->
  perm_eq (theta_table_image s) (theta_table_image t).
Proof.
move=> hquot.
have hmem : t * s^-1 \in theta_stabilizer.
  by rewrite theta_stabilizerE.
have hstab : theta_stabilizesb (t * s^-1).
  by move: hmem; rewrite mem_theta_stabilizer.
have hperm := theta_stabilizesb_perm hstab.
have hmap := perm_map (act_exponent s) hperm.
rewrite -!theta_table_image_mul in hmap.
fold (theta_table_image s) in hmap.
have hts : (t * s^-1) * s = t by rewrite -mulgA mulVg mulg1.
rewrite hts in hmap.
by move: hmap; rewrite perm_sym.
Qed.

Lemma theta_table_images_perm_iff s t :
  perm_eq (theta_table_image s) (theta_table_image t) =
    (t * s^-1 \in standard_F20).
Proof.
apply/idP/idP.
- exact: theta_table_images_perm_implies_F20.
- exact: theta_table_images_perm_of_F20.
Qed.

(** If [representative i] represents the left coset of [g^-1], then
    [g * representative i] lies in [F20], and hence

      [g = (g * representative i) * (representative i)^-1].

    The first factor permutes the original theta table; the anti-homomorphic
    action then leaves precisely the orbit indexed by the inverse
    representative. *)
Lemma theta_table_image_same_inverse_coset g i :
  same_left_cosetb g^-1 (representative i) ->
  perm_eq (theta_table_image g)
    (theta_table_image ((representative i)^-1)).
Proof.
move=> hcoset.
have hk : g * representative i \in standard_F20.
  move: hcoset.
  by rewrite /same_left_cosetb invgK.
have hkT : g * representative i \in theta_stabilizer.
  exact: subsetP standard_F20_sub_theta_stabilizer _ hk.
have hkstab : theta_stabilizesb (g * representative i).
  by move: hkT; rewrite mem_theta_stabilizer.
have hkperm := theta_stabilizesb_perm hkstab.
have hmap := perm_map (act_exponent (representative i)^-1) hkperm.
rewrite -!theta_table_image_mul in hmap.
fold (theta_table_image ((representative i)^-1)) in hmap.
have hgi : (g * representative i) * (representative i)^-1 = g.
  by rewrite -mulgA mulgV mulg1.
by rewrite hgi in hmap.
Qed.

(** A transparent, orientation-correct index for the orbit of [g]. *)
Definition inverse_representative_index (g : S5) : 'I_6 :=
  representative_index g^-1.

Lemma inverse_representative_indexP g :
  same_left_cosetb g^-1
    (representative (inverse_representative_index g)).
Proof. exact: representative_indexP. Qed.

Theorem theta_table_orbit_exhaustive g :
  perm_eq (theta_table_image g)
    (theta_table_image
      ((representative (inverse_representative_index g))^-1)).
Proof.
apply: theta_table_image_same_inverse_coset.
exact: inverse_representative_indexP.
Qed.

Corollary theta_table_orbit_exhaustive_exists g :
  exists i : 'I_6,
    perm_eq (theta_table_image g)
      (theta_table_image ((representative i)^-1)).
Proof.
exists (inverse_representative_index g).
exact: theta_table_orbit_exhaustive.
Qed.

(** The six inverse-representative orbits are pairwise distinct, up to
    permutation of their ten rows.  This is the resolvent-root distinctness
    certificate needed downstream. *)
Lemma inverse_representative_theta_orbits_distinct :
  [forall i : 'I_6, [forall j : 'I_6,
    perm_eq
      (theta_table_image ((representative i)^-1))
      (theta_table_image ((representative j)^-1)) == (i == j)]].
Proof.
apply/forallP=> i; apply/forallP=> j; apply/eqP.
rewrite theta_table_images_perm_iff invgK.
have hcosets := forallP (forallP representative_cosets_distinct j) i.
move/eqP: hcosets.
by rewrite /same_left_cosetb eq_sym.
Qed.

Lemma inverse_representative_theta_image_injective :
  injective (fun i : 'I_6 =>
    theta_table_image ((representative i)^-1)).
Proof.
move=> i j hij.
have hp : perm_eq
    (theta_table_image ((representative i)^-1))
    (theta_table_image ((representative j)^-1)).
  by rewrite hij perm_refl.
have hdistinct :=
  forallP (forallP inverse_representative_theta_orbits_distinct i) j.
have hijb : i == j.
  by move: hdistinct; rewrite hp /=.
exact/eqP.
Qed.

End PolynomialFormulasQuinticThetaOrbit.
