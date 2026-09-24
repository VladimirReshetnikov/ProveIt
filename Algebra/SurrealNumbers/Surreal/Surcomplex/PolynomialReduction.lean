import Surreal.Surcomplex.Valuation
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Valuation.Integral

/-!
# Polynomial roots and reduction in the actual finite surcomplex ring

This instantiates the root/coefficient assertions preceding
`polynomial:eq:reductionfactor` on the constructed surcomplex field.
A root of a monic polynomial with finite coefficients is finite. Conversely,
a split monic polynomial with finite roots has finite coefficients.
Standard part preserves split linear factorizations and their root multisets,
including multiplicities when distinct roots have the same standard part.

Splitting remains an explicit hypothesis: algebraic closedness of the
surcomplex field has not yet been proved.
-/

universe u

namespace Surreal.Surcomplex

noncomputable section

open Polynomial

/-- The existing finite subring is the ring of integers of the actual valuation. -/
theorem finiteSubring_integers : valuation.toValuation.Integers finiteSubring.{u} where
  hom_inj := Subtype.val_injective
  map_le_one z := (isFinite_iff_valuation_nonneg z.1).mp z.2
  exists_of_le_one {z} hz := ⟨⟨z, (isFinite_iff_valuation_nonneg z).mpr hz⟩, rfl⟩

/-- No element outside the finite ring is integral over it. -/
theorem finite_of_integral {z : Surcomplex.{u}} (hz : IsIntegral finiteSubring z) : IsFinite z :=
  (isFinite_iff_valuation_nonneg z).mpr (finiteSubring_integers.isIntegral_iff_v_le_one.mp hz)

/-- A root in the actual field of a monic polynomial over the finite ring is finite. -/
theorem finite_of_monic_root (p : Polynomial finiteSubring.{u}) (hp : p.Monic)
    (z : Surcomplex.{u}) (hz : (p.map finiteSubring.subtype).IsRoot z) : IsFinite z := by
  apply finite_of_integral
  refine ⟨p, hp, ?_⟩
  change p.eval₂ finiteSubring.subtype z = 0
  simpa only [IsRoot.def, eval_map] using hz

/-- The root bound with finiteness stated on the actual polynomial coefficients. -/
theorem finite_of_monic_root_of_coeff_finite (p : Polynomial Surcomplex.{u}) (hp : p.Monic)
    (hc : ∀ n, IsFinite (p.coeff n)) (z : Surcomplex.{u}) (hz : p.IsRoot z) : IsFinite z := by
  have hlift : p ∈ lifts finiteSubring.subtype := by
    apply (lifts_iff_coeff_lifts p).mpr
    intro n
    exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
  obtain ⟨q, hq, _, hqm⟩ := lifts_and_degree_eq_and_monic hlift hp
  apply finite_of_monic_root q hqm z
  simpa only [hq] using hz

/-- Finite roots of a split monic polynomial give finite coefficients. -/
theorem coeff_finite_of_monic_split_roots (p : Polynomial Surcomplex.{u}) (hp : p.Monic)
    (hs : p.Splits) (hr : ∀ z ∈ p.roots, IsFinite z) (n : ℕ) : IsFinite (p.coeff n) := by
  have hlift : p ∈ lifts finiteSubring.subtype :=
    hs.mem_lift_of_roots_mem_range hp finiteSubring.subtype
      (fun z hz => ⟨⟨z, hr z hz⟩, rfl⟩)
  obtain ⟨a, ha⟩ := (lifts_iff_coeff_lifts p).mp hlift n
  rw [← ha]
  exact a.property

/-- In particular, products of monic linear factors with finite roots have finite coefficients. -/
theorem coeff_finite_multiset_prod (roots : Multiset Surcomplex.{u})
    (hr : ∀ z ∈ roots, IsFinite z) (n : ℕ) :
    IsFinite ((roots.map fun z => X - C z).prod.coeff n) := by
  apply coeff_finite_of_monic_split_roots _ (monic_multisetProd_X_sub_C roots)
  · exact Splits.multisetProd fun p hp => by
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hp
      exact Splits.X_sub_C z
  · simpa only [roots_multiset_prod_X_sub_C] using hr

/-- Splitting of a monic finite polynomial in the ambient field descends to its finite ring. -/
theorem splits_finite_of_splits (p : Polynomial finiteSubring.{u}) (hp : p.Monic)
    (hs : (p.map finiteSubring.subtype).Splits) : p.Splits := by
  apply hs.of_splits_map_of_injective Subtype.val_injective
  intro z hz
  refine ⟨⟨z, ?_⟩, rfl⟩
  exact finite_of_monic_root p hp z
    ((mem_roots (hp.map finiteSubring.subtype).ne_zero).mp hz)

/-- Actual standard-part reduction preserves a split monic linear factorization. -/
theorem standardPart_factorization (p : Polynomial finiteSubring.{u}) (hp : p.Monic)
    (hs : (p.map finiteSubring.subtype).Splits) :
    p.map standardPartHom = (p.roots.map fun z => X - C (standardPartHom z)).prod := by
  have h := congrArg (Polynomial.map standardPartHom)
    ((splits_finite_of_splits p hp hs).eq_prod_roots_of_monic hp)
  simpa only [Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.map_sub,
    map_X, map_C, Function.comp_def] using h

/-- Coincident standard parts add multiplicities in the reduced root multiset. -/
theorem roots_standardPart (p : Polynomial finiteSubring.{u}) (hp : p.Monic)
    (hs : (p.map finiteSubring.subtype).Splits) :
    (p.map standardPartHom).roots = p.roots.map standardPartHom :=
  (splits_finite_of_splits p hp hs).roots_map_of_ne_zero (hp.map standardPartHom).ne_zero

/-- Any finite root reduces to a root of the ordinary complex reduction. -/
theorem isRoot_standardPart (p : Polynomial finiteSubring.{u}) (z : finiteSubring.{u})
    (hz : (p.map finiteSubring.subtype).IsRoot z.1) :
    (p.map standardPartHom).IsRoot (standardPartHom z) := by
  have hroot : p.IsRoot z := hz.of_map (f := finiteSubring.subtype) Subtype.val_injective
  exact hroot.map (f := standardPartHom)

end

end Surreal.Surcomplex
