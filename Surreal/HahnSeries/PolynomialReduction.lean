import Surreal.HahnSeries.StandardPart
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Valuation.Integral

/-!
# Polynomial roots and standard-part reduction

This file proves the paragraph preceding `polynomial:eq:reductionfactor` and
the reduction factorization itself in the generic Hahn setting. Roots of a
monic polynomial with nonnegative-order coefficients have nonnegative order.
Conversely, a split monic polynomial whose roots have nonnegative order has
nonnegative-order coefficients. Mapping a split monic polynomial through
standard part preserves its complete factorization, including multiplicities.

Splitting is an explicit hypothesis. No algebraic closedness of the Hahn field
or identification of valuation bounds with surreal modulus bounds is assumed.
-/

namespace Surreal.HahnSeries

noncomputable section

open Polynomial
open scoped _root_.HahnSeries

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The root-bound assertion preceding `polynomial:eq:reductionfactor`:
roots in the Hahn ring of a monic polynomial over the nonnegative-order
subring again have nonnegative order. -/
theorem orderTop_nonneg_of_monic_root
    (p : Polynomial (nonnegativeSubring Γ K)) (hp : p.Monic)
    (x : K⟦Γ⟧)
    (hx : (p.map (nonnegativeSubring Γ K).subtype).IsRoot x) :
    0 ≤ x.orderTop := by
  apply (Valuation.integer.integers
    (AddValuation.toValuation (_root_.HahnSeries.addVal Γ K))).isIntegral_iff_v_le_one.mp
  refine ⟨p, hp, ?_⟩
  change p.eval₂ (nonnegativeSubring Γ K).subtype x = 0
  simpa only [IsRoot.def, eval_map] using hx

/-- The same root bound stated coefficientwise for an ambient Hahn
polynomial, as in the paragraph preceding `polynomial:eq:reductionfactor`. -/
theorem orderTop_nonneg_of_monic_root_of_coeff_nonneg
    (p : Polynomial K⟦Γ⟧) (hp : p.Monic)
    (hc : ∀ n, 0 ≤ (p.coeff n).orderTop) (x : K⟦Γ⟧) (hx : p.IsRoot x) :
    0 ≤ x.orderTop := by
  have hlift : p ∈ lifts (nonnegativeSubring Γ K).subtype := by
    apply (lifts_iff_coeff_lifts p).mpr
    intro n
    exact ⟨⟨p.coeff n, (mem_nonnegativeSubring _).mpr (hc n)⟩, rfl⟩
  obtain ⟨q, hq, _, hqm⟩ := lifts_and_degree_eq_and_monic hlift hp
  apply orderTop_nonneg_of_monic_root q hqm x
  simpa only [hq] using hx

/-- The converse assertion preceding `polynomial:eq:reductionfactor`:
all coefficients of a split monic polynomial are valuation-nonnegative
when every root is valuation-nonnegative. -/
theorem coeff_orderTop_nonneg_of_monic_split_roots
    (p : Polynomial K⟦Γ⟧) (hp : p.Monic) (hs : p.Splits)
    (hr : ∀ x ∈ p.roots, 0 ≤ x.orderTop) (n : ℕ) :
    0 ≤ (p.coeff n).orderTop := by
  have hlift : p ∈ lifts (nonnegativeSubring Γ K).subtype :=
    hs.mem_lift_of_roots_mem_range hp (nonnegativeSubring Γ K).subtype
      (fun x hx => ⟨⟨x, (mem_nonnegativeSubring _).mpr (hr x hx)⟩, rfl⟩)
  obtain ⟨a, ha⟩ := (lifts_iff_coeff_lifts p).mp hlift n
  rw [← ha]
  exact (mem_nonnegativeSubring _).mp a.property

/-- A finite product of monic linear factors with nonnegative-order roots
has nonnegative-order coefficients. This is the product formulation of the
converse preceding `polynomial:eq:reductionfactor`. -/
theorem coeff_orderTop_nonneg_multiset_prod
    (roots : Multiset K⟦Γ⟧) (hr : ∀ x ∈ roots, 0 ≤ x.orderTop) (n : ℕ) :
    0 ≤ ((roots.map fun x => X - C x).prod.coeff n).orderTop := by
  apply coeff_orderTop_nonneg_of_monic_split_roots _
    (monic_multisetProd_X_sub_C roots)
  · exact Splits.multisetProd fun p hp => by
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hp
      exact Splits.X_sub_C x
  · simpa only [roots_multiset_prod_X_sub_C] using hr

/-- A monic polynomial over the nonnegative-order subring that splits in
the ambient Hahn ring already splits over that subring, because every root
has nonnegative order. -/
theorem splits_nonnegative_of_splits
    (p : Polynomial (nonnegativeSubring Γ K)) (hp : p.Monic)
    (hs : (p.map (nonnegativeSubring Γ K).subtype).Splits) : p.Splits := by
  apply hs.of_splits_map_of_injective Subtype.val_injective
  intro x hx
  refine ⟨⟨x, (mem_nonnegativeSubring _).mpr ?_⟩, rfl⟩
  exact orderTop_nonneg_of_monic_root p hp x
    ((mem_roots (hp.map (nonnegativeSubring Γ K).subtype).ne_zero).mp hx)

/-- `polynomial:eq:reductionfactor`: reduction is the product of the
reductions of the linear factors. The roots are a multiset in the
nonnegative-order subring, so coincident reductions retain multiplicity. -/
theorem standardPart_factorization
    (p : Polynomial (nonnegativeSubring Γ K)) (hp : p.Monic)
    (hs : (p.map (nonnegativeSubring Γ K).subtype).Splits) :
    p.map (standardPart Γ K) =
      (p.roots.map fun x => X - C (standardPart Γ K x)).prod := by
  have h := congrArg (Polynomial.map (standardPart Γ K))
    ((splits_nonnegative_of_splits p hp hs).eq_prod_roots_of_monic hp)
  simpa only [Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.map_sub, map_X, map_C,
    Function.comp_def] using h

/-- The exact root-multiset identity in `polynomial:eq:reductionfactor`.
The map can identify distinct roots, while their multiplicities add in the
resulting multiset. -/
theorem roots_standardPart
    (p : Polynomial (nonnegativeSubring Γ K)) (hp : p.Monic)
    (hs : (p.map (nonnegativeSubring Γ K).subtype).Splits) :
    (p.map (standardPart Γ K)).roots = p.roots.map (standardPart Γ K) :=
  (splits_nonnegative_of_splits p hp hs).roots_map_of_ne_zero
    (hp.map (standardPart Γ K)).ne_zero

end
end Surreal.HahnSeries
