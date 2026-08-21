import ExponentialIdentities.TwoBaseIntegerExponent.BlockWeyl

/-!
# Equidistribution consequences for exact solution blocks

The Fourier-mode estimate from `BlockWeyl` is extended by finite linearity to every
finitely supported trigonometric polynomial. The limiting block average is exactly its
zero Fourier coefficient.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The normalized `h`-th Fourier average on the exact ceiling-parametrized points in block `N`. -/
def primitiveUnitBlockFourierAverage (β : ℝ) (h : ℤ) (N : ℕ) : ℂ :=
  let K := primitiveRotationLength β N
  (∑ k ∈ range K,
    rotationFourierCharacter h
      (primitiveUnitBlockParameter β N (k + 1))) / (K : ℂ)

/-- The zero Fourier mode of the exact block average is eventually identically one. -/
theorem primitiveUnitBlockFourierAverage_zero_eventuallyEq_one
    {β : ℝ} (hβpos : 0 < β) :
    primitiveUnitBlockFourierAverage β 0 =ᶠ[atTop] fun _ : ℕ ↦ 1 := by
  have hlength := (tendsto_primitiveRotationLength_atTop hβpos).eventually
    (eventually_ge_atTop 1)
  filter_upwards [hlength] with N hN
  have hK0 : primitiveRotationLength β N ≠ 0 := by omega
  simp [primitiveUnitBlockFourierAverage, rotationFourierCharacter, hK0]

/-- Every Fourier mode has the expected limiting block average: one in mode zero and zero in
every nonzero mode. -/
theorem tendsto_primitiveUnitBlockFourierAverage
    {β : ℝ} (hβpos : 0 < β) (hβirr : Irrational β) (h : ℤ) :
    Tendsto (primitiveUnitBlockFourierAverage β h) atTop
      (nhds (if h = 0 then 1 else 0)) := by
  by_cases hh : h = 0
  · subst h
    exact Tendsto.congr'
      (primitiveUnitBlockFourierAverage_zero_eventuallyEq_one hβpos).symm
      tendsto_const_nhds
  · simp only [hh, ↓reduceIte]
    change Tendsto
      (fun N : ℕ =>
        let K := primitiveRotationLength β N
        (∑ k ∈ range K,
          rotationFourierCharacter h
            (primitiveUnitBlockParameter β N (k + 1))) / (K : ℂ))
      atTop (nhds 0)
    exact tendsto_primitiveUnitBlockParameter_fourierAverage hβpos hβirr hh

/-- A trigonometric polynomial represented by its finitely supported Fourier coefficients. -/
def blockTrigonometricPolynomial (c : ℤ →₀ ℂ) (x : ℝ) : ℂ :=
  c.sum fun h a ↦ a * rotationFourierCharacter h x

/-- The normalized average of a trigonometric polynomial over the exact points in block `N`. -/
def primitiveUnitBlockTrigonometricAverage
    (β : ℝ) (c : ℤ →₀ ℂ) (N : ℕ) : ℂ :=
  let K := primitiveRotationLength β N
  (∑ k ∈ range K,
    blockTrigonometricPolynomial c
      (primitiveUnitBlockParameter β N (k + 1))) / (K : ℂ)

/-- Finite linearity rewrites a trigonometric-polynomial block average as the corresponding
finite linear combination of Fourier-mode averages. -/
theorem primitiveUnitBlockTrigonometricAverage_eq_sum
    (β : ℝ) (c : ℤ →₀ ℂ) (N : ℕ) :
    primitiveUnitBlockTrigonometricAverage β c N =
      c.sum fun h a ↦ a * primitiveUnitBlockFourierAverage β h N := by
  classical
  simp only [primitiveUnitBlockTrigonometricAverage, blockTrigonometricPolynomial,
    primitiveUnitBlockFourierAverage, Finsupp.sum]
  rw [sum_comm]
  rw [sum_div]
  apply sum_congr rfl
  intro h hh
  rw [← mul_sum]
  ring

/-- **Finite trigonometric-polynomial equidistribution.** On the exact ceiling-parametrized
points in successive solution blocks, the normalized average of every finite Fourier sum
converges to its zero Fourier coefficient. -/
theorem tendsto_primitiveUnitBlockTrigonometricAverage
    {β : ℝ} (hβpos : 0 < β) (hβirr : Irrational β) (c : ℤ →₀ ℂ) :
    Tendsto (primitiveUnitBlockTrigonometricAverage β c) atTop (nhds (c 0)) := by
  classical
  have hmodes : ∀ h ∈ c.support,
      Tendsto
        (fun N : ℕ ↦ c h * primitiveUnitBlockFourierAverage β h N)
        atTop (nhds (c h * (if h = 0 then 1 else 0))) := by
    intro h hh
    exact tendsto_const_nhds.mul
      (tendsto_primitiveUnitBlockFourierAverage hβpos hβirr h)
  have hsum := tendsto_finsetSum c.support hmodes
  have hlimit :
      (∑ h ∈ c.support, c h * (if h = 0 then 1 else 0)) = c 0 := by
    by_cases hzero : 0 ∈ c.support
    · simp [hzero]
    · have hc0 : c 0 = 0 := Finsupp.notMem_support_iff.mp hzero
      simp [hzero, hc0]
  rw [hlimit] at hsum
  apply hsum.congr'
  filter_upwards with N
  exact (primitiveUnitBlockTrigonometricAverage_eq_sum β c N).symm

/-- Conditional package: failure of Alaoglu--Erdős supplies a canonical least generator for
which every finite trigonometric-polynomial block average converges to its constant term. -/
theorem exists_primitiveGenerator_with_block_trigonometric_equidistribution
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ,
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      ∀ c : ℤ →₀ ℂ,
        Tendsto (primitiveUnitBlockTrigonometricAverage β c)
          atTop (nhds (c 0)) := by
  obtain ⟨β, hβirr, hβleast, _⟩ :=
    exists_primitiveGenerator_with_vanishing_block_fourier_modes hfail
  exact ⟨β, hβirr, hβleast,
    tendsto_primitiveUnitBlockTrigonometricAverage hβleast.pos hβirr⟩

end

end LeanProofs.TwoBaseIntegerExponent
