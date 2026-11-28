import GRHArticle.ProgressionFree.PolynomialMonicBallDensity

/-!
# Nonzero scalar invariance of valuation families
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid Filter Topology
open scoped Classical

variable {F : Type*} [Field F]

theorem polynomialPrimeExponent_C_mul {a : F} (ha : a ≠ 0) {g : F[X]} (hg : g ≠ 0)
    (p : F[X]) : polynomialPrimeExponent p (C a*g) = polynomialPrimeExponent p g := by
  rw [polynomialPrimeExponent_mul p (C_ne_zero.mpr ha) hg]
  have hu : IsUnit (C a : F[X]) := IsUnit.map C (isUnit_iff_ne_zero.mpr ha)
  simp [polynomialPrimeExponent, normalizedFactors_of_isUnit hu]

/-- A rule depending only on prime exponents accepts exactly the nonzero
scalar multiples of the monic polynomials satisfying the same predicate. -/
theorem polynomialScalarClosure_valuationPredicate (V : (F[X] → ℕ) → Prop) :
    polynomialScalarClosure {f : F[X] | V (fun p ↦ polynomialPrimeExponent p f)} =
      {f : F[X] | f ≠ 0 ∧ V (fun p ↦ polynomialPrimeExponent p f)} := by
  ext f
  constructor
  · rintro ⟨g,hg,hm,a,ha,rfl⟩
    exact ⟨mul_ne_zero (C_ne_zero.mpr ha) hm.ne_zero,
      by simpa only [Set.mem_setOf_eq, polynomialPrimeExponent_C_mul ha hm.ne_zero] using hg⟩
  · rintro ⟨hf,hV⟩
    let g := f*C f.leadingCoeff⁻¹
    have hm : g.Monic := monic_mul_leadingCoeff_inv hf
    have ha : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
    have he : f = C f.leadingCoeff*g := by
      dsimp [g]
      rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ ha, map_one, mul_one]
    refine ⟨g, ?_, hm, f.leadingCoeff, ha, he⟩
    have he' (p : F[X]) : polynomialPrimeExponent p g = polynomialPrimeExponent p f := by
      conv_rhs => rw [he, polynomialPrimeExponent_C_mul ha hm.ne_zero]
    simpa only [Set.mem_setOf_eq, he'] using hV

/-- The limit of a monic valuation predicate gives the natural density of the
same predicate on all nonzero polynomials. -/
theorem tendsto_polynomialBallProportion_valuationPredicate [Fintype F]
    (V : (F[X] → ℕ) → Prop) {c : ℝ}
    (h : Tendsto (monicFamilyProportion {f : F[X] | V (fun p ↦ polynomialPrimeExponent p f)})
      atTop (𝓝 c)) :
    Tendsto (polynomialBallProportion {f : F[X] | f ≠ 0 ∧ V (fun p ↦ polynomialPrimeExponent p f)})
      atTop (𝓝 c) := by
  rw [← polynomialScalarClosure_valuationPredicate V]
  exact tendsto_polynomialBallProportion_scalarClosure h

end GRHArticle.ProgressionFree
