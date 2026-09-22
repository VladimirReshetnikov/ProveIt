import Surreal.Algebra.PolynomialFactorUniqueness
import Surreal.HahnSeries.StandardPart
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Coprime reduction and uniqueness of Hahn polynomial factors

Standard part on the nonnegative-order Hahn ring reflects units. Consequently
coprime monic residue factors lift to coprime polynomials, and any two monic
factorizations with the same coprime reductions agree. This is the binary
uniqueness clause of `polynomial:thm:hensel`, with no assumption that the
candidate supports lie in a prescribed monoid or arise from one formal lift.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Units of the nonnegative-order ring are precisely its nonzero residues. -/
theorem isUnit_iff_standardPart_ne_zero (x : nonnegativeSubring Γ K) :
    IsUnit x ↔ standardPart Γ K x ≠ 0 := by
  have hv : (AddValuation.toValuation (_root_.HahnSeries.addVal Γ K)).Integers
      (nonnegativeSubring Γ K) :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun y => y.property
      exists_of_le_one := fun {y} hy => ⟨⟨y, hy⟩, rfl⟩ }
  rw [hv.isUnit_iff_valuation_eq_one]
  change (x : K⟦Γ⟧).orderTop = 0 ↔ (x : K⟦Γ⟧).coeff 0 ≠ 0
  rw [ne_eq, coeff_zero_eq_zero_iff_orderTop_pos _ x.property, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h x.property⟩

/-- The standard-part homomorphism reflects units. -/
theorem standardPart_reflects_units (x : nonnegativeSubring Γ K)
    (hx : IsUnit (standardPart Γ K x)) : IsUnit x :=
  (isUnit_iff_standardPart_ne_zero x).mpr hx.ne_zero

/-- Coprimeness of monic standard-part reductions gives a Bézout identity
already over the nonnegative-order ring. -/
theorem isCoprime_of_monic_standardPart {p q : Polynomial (nonnegativeSubring Γ K)}
    (hp : p.Monic) (hq : q.Monic)
    (hcop : IsCoprime (p.map (standardPart Γ K)) (q.map (standardPart Γ K))) :
    IsCoprime p q :=
  FinitePolynomial.isCoprime_of_monic_reductions (standardPart Γ K)
    standardPart_reflects_units hp hq hcop

/-- Binary Hahn-factor uniqueness among all monic candidates with the
specified coprime reductions, independently of their support presentation. -/
theorem monic_factorization_unique_of_standardPart
    {p q p' q' : Polynomial (nonnegativeSubring Γ K)}
    (hp : p.Monic) (hq : q.Monic) (hp' : p'.Monic) (hq' : q'.Monic)
    (hcop : IsCoprime (p.map (standardPart Γ K)) (q.map (standardPart Γ K)))
    (hredp : p'.map (standardPart Γ K) = p.map (standardPart Γ K))
    (hredq : q'.map (standardPart Γ K) = q.map (standardPart Γ K))
    (hmul : p * q = p' * q') : p' = p ∧ q' = q :=
  FinitePolynomial.monic_factorization_unique_of_reductions (standardPart Γ K)
    standardPart_reflects_units hp hq hp' hq' hcop hredp hredq hmul

/-- Finite-family uniqueness with all positive-support candidates admitted. -/
theorem monic_finite_factorization_unique_of_standardPart {ι : Type*} [Fintype ι]
    (p p' : ι → Polynomial (nonnegativeSubring Γ K))
    (hp : ∀ i, (p i).Monic) (hp' : ∀ i, (p' i).Monic)
    (hcop : Pairwise fun i j =>
      IsCoprime ((p i).map (standardPart Γ K)) ((p j).map (standardPart Γ K)))
    (hred : ∀ i, (p' i).map (standardPart Γ K) = (p i).map (standardPart Γ K))
    (hmul : ∏ i, p i = ∏ i, p' i) : p' = p :=
  FinitePolynomial.monic_finite_factorization_unique_of_reductions (standardPart Γ K)
    standardPart_reflects_units p p' hp hp' hcop hred hmul

end

end Surreal.HahnSeries
