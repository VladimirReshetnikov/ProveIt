import Surreal.HahnSeries.StrongEvaluation
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Source summation of ordinary power series

Finite coefficient incidence is exactly native Hahn strong summability after
identifying ordinary power series with Hahn series over `ℕ`. In particular,
every formal series is the source sum of its monomials. These statements do
not invoke topological convergence or restrict the source index universe.
-/

universe u v w

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {R : Type u} {ι : Type v} {κ : Type w} [CommRing R]

/-- A source-summable formal-series family, regarded as a native Hahn family. -/
def powerSeriesSourceFamily (f : ι → PowerSeries R) (hf : PowerSeriesSummable f) :
    SummableFamily ℕ R ι where
  toFun i := toPowerSeries.symm (f i)
  isPWO_iUnion_support' := .of_linearOrder _
  finite_co_support' n := hf n

@[simp] theorem powerSeriesSourceFamily_apply (f : ι → PowerSeries R)
    (hf : PowerSeriesSummable f) (i : ι) :
    powerSeriesSourceFamily f hf i = toPowerSeries.symm (f i) := rfl

/-- The coefficient-finiteness predicate is exactly native Hahn summability. -/
theorem powerSeriesSummable_iff_exists_hahnFamily (f : ι → PowerSeries R) :
    PowerSeriesSummable f ↔
      ∃ s : SummableFamily ℕ R ι, ∀ i, s i = toPowerSeries.symm (f i) := by
  constructor
  · intro hf
    exact ⟨powerSeriesSourceFamily f hf, powerSeriesSourceFamily_apply f hf⟩
  · rintro ⟨s, hs⟩ n
    simpa only [hs, coeff_toPowerSeries_symm] using s.finite_co_support n

/-- The source sum agrees with the native Hahn strong sum. -/
theorem powerSeriesSum_eq_toPowerSeries_hsum (f : ι → PowerSeries R)
    (hf : PowerSeriesSummable f) :
    powerSeriesSum f = toPowerSeries (powerSeriesSourceFamily f hf).hsum := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_powerSeriesSum, coeff_toPowerSeries, SummableFamily.coeff_hsum,
    powerSeriesSourceFamily_apply, coeff_toPowerSeries_symm]

/-- Reindexing by an equivalence preserves finite coefficient incidence. -/
theorem PowerSeriesSummable.reindex {f : ι → PowerSeries R}
    (hf : PowerSeriesSummable f) (e : κ ≃ ι) :
    PowerSeriesSummable (fun k => f (e k)) := by
  intro n
  exact (hf n).preimage e.injective.injOn

/-- Source sums are invariant under equivalences of their index types. -/
theorem powerSeriesSum_reindex (f : ι → PowerSeries R) (e : κ ≃ ι) :
    powerSeriesSum (fun k => f (e k)) = powerSeriesSum f := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_powerSeriesSum]
  exact finsum_comp_equiv e (f := fun i => (f i).coeff n)

/-- The monomials of an ordinary formal power series form a source-summable family. -/
theorem powerSeriesSummable_monomials (f : PowerSeries R) :
    PowerSeriesSummable (fun n => PowerSeries.monomial n (f.coeff n)) := by
  intro n
  apply (Set.finite_singleton n).subset
  intro m hm
  by_contra hmn
  exact hm (by simp [PowerSeries.coeff_monomial, Ne.symm hmn])

/-- A formal power series is exactly the source sum of its monomials. -/
theorem powerSeriesSum_monomials (f : PowerSeries R) :
    powerSeriesSum (fun n => PowerSeries.monomial n (f.coeff n)) = f := by
  apply PowerSeries.ext
  intro n
  rw [coeff_powerSeriesSum, finsum_eq_single _ n]
  · exact PowerSeries.coeff_monomial_same _ _
  · intro m hmn
    simp [PowerSeries.coeff_monomial, Ne.symm hmn]

end

end Surreal.HahnSeries
