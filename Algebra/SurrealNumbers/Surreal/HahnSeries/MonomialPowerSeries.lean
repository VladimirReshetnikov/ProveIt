import Surreal.HahnSeries.Binomial
import Surreal.Algebra.FormalBinomialRoots

/-!
# Injective formal-series substitution at one Hahn monomial

The coefficient preservation and admissibility in `osq:nm:lem:binomial`.
Native Hahn exponents measure valuation, so a positive exponent here
corresponds to a negative growth exponent in the manuscript.
-/

namespace Surreal.HahnSeries
open _root_.HahnSeries
noncomputable section

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing R] [Nontrivial R]

/-- Substitution at a positive-order monomial is a native algebra homomorphism. -/
def monomialEvaluation (g : Γ) (hg : 0 < g) : PowerSeries R →ₐ[R] R⟦Γ⟧ :=
  evaluate (single g 1) (by simpa only [orderTop_single one_ne_zero, WithTop.coe_pos] using hg)

/-- Every ordinary coefficient is preserved at the corresponding monomial exponent. -/
theorem coeff_monomialEvaluation (g : Γ) (hg : 0 < g) (f : PowerSeries R) (n : ℕ) :
    (monomialEvaluation g hg f).coeff (n • g) = f.coeff n := by
  rw [monomialEvaluation, coeff_evaluate, finsum_eq_single _ n]
  · simp [single_pow, single_mul_single]
  · intro k hk
    have he : n • g ≠ k • g := fun h => hk ((nsmul_left_strictMono hg).injective h).symm
    simp [single_pow, single_mul_single, coeff_single_of_ne he]

/-- No coefficient can appear outside the nonnegative integral multiples of the argument exponent. -/
theorem coeff_monomialEvaluation_eq_zero (g : Γ) (hg : 0 < g) (f : PowerSeries R) (a : Γ)
    (ha : ∀ n : ℕ, a ≠ n • g) : (monomialEvaluation g hg f).coeff a = 0 := by
  rw [monomialEvaluation, coeff_evaluate]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  simp [single_pow, single_mul_single, coeff_single_of_ne (ha n)]

/-- Monomial substitution is injective, without a topological-convergence assertion. -/
theorem monomialEvaluation_injective (g : Γ) (hg : 0 < g) :
    Function.Injective (monomialEvaluation (R := R) g hg) := by
  intro f q h
  ext n
  simpa only [coeff_monomialEvaluation] using congrArg (fun z : R⟦Γ⟧ => z.coeff (n • g)) h

/-- The substituted Hahn support is countable, even when the exponent group is not. -/
theorem monomialEvaluation_support_countable (g : Γ) (hg : 0 < g) (f : PowerSeries R) :
    (monomialEvaluation g hg f).support.Countable := by
  apply (Set.countable_range (fun n : ℕ => n • g)).mono
  intro a ha
  by_contra h
  exact ha (coeff_monomialEvaluation_eq_zero g hg f a (fun n he => h ⟨n, he.symm⟩))

/-- The formal variable becomes the specified monomial. -/
@[simp] theorem monomialEvaluation_X (g : Γ) (hg : 0 < g) :
    monomialEvaluation (R := R) g hg PowerSeries.X = single g 1 := evaluate_X _ _

/-- The binomial identity holds after monomial substitution in every ordered-group Hahn ring. -/
theorem monomialEvaluation_binomial_root {K : Type*} [Field K] [CharZero K]
    (g : Γ) (hg : 0 < g) (m : ℕ) (hm : m ≠ 0) :
    monomialEvaluation g hg (PowerSeries.binomialSeries K (1 / (m : K))) ^ m =
      1 + single g 1 := by
  rw [← map_pow, FormalBinomialRoots.binomialSeries_root m hm, map_add, map_one,
    monomialEvaluation_X]

end
end Surreal.HahnSeries
