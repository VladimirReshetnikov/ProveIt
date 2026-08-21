import ExponentialIdentities.TwoBaseIntegerExponent.ExactCounting
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Normed

namespace LeanProofs.TwoBaseIntegerExponent

open Filter Finset
open scoped Topology

noncomputable section

/-- The `h`-th Fourier character on the real circle. -/
def rotationFourierCharacter (h : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * (h : ℂ) * (x : ℂ)) * Complex.I)

/-- The unit-complex phase for the `h`-th Fourier mode of rotation by `β`. -/
def irrationalRotationPhase (β : ℝ) (h : ℤ) : ℂ :=
  rotationFourierCharacter h β

@[simp] theorem norm_irrationalRotationPhase (β : ℝ) (h : ℤ) :
    ‖irrationalRotationPhase β h‖ = 1 := by
  rw [irrationalRotationPhase, rotationFourierCharacter, Complex.norm_exp]
  simp

theorem irrationalRotationPhase_ne_one {β : ℝ} (hβ : Irrational β)
    {h : ℤ} (hh : h ≠ 0) : irrationalRotationPhase β h ≠ 1 := by
  intro hone
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone
  have hcancelI :
      (2 * (Real.pi : ℂ)) * ((h : ℂ) * (β : ℂ)) =
        (2 * (Real.pi : ℂ)) * (n : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    simpa only [irrationalRotationPhase] using
      (show
        ((2 * (Real.pi : ℂ)) * ((h : ℂ) * (β : ℂ))) * Complex.I =
          ((2 * (Real.pi : ℂ)) * (n : ℂ)) * Complex.I by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hn)
  have hcoef : (h : ℂ) * (β : ℂ) = (n : ℂ) := by
    have hcne : (2 * (Real.pi : ℂ)) ≠ 0 := by
      norm_num [Real.pi_ne_zero]
    apply mul_left_cancel₀ hcne
    exact hcancelI
  have hreal : (h : ℝ) * β = (n : ℝ) := by
    simpa using congrArg Complex.re hcoef
  exact (hβ.intCast_mul hh).ne_int n hreal

@[simp] theorem rotationFourierCharacter_nat_add (h : ℤ) (n : ℕ) (x : ℝ) :
    rotationFourierCharacter h ((n : ℝ) + x) = rotationFourierCharacter h x := by
  rw [rotationFourierCharacter]
  have harg :
      (2 * (Real.pi : ℂ) * (h : ℂ) * (((n : ℝ) + x : ℝ) : ℂ)) * Complex.I =
        ((h * (n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          (2 * (Real.pi : ℂ) * (h : ℂ) * (x : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp [rotationFourierCharacter]

theorem rotationFourierCharacter_nat_mul (β : ℝ) (h : ℤ) (k : ℕ) :
    rotationFourierCharacter h ((k : ℝ) * β) = irrationalRotationPhase β h ^ k := by
  rw [rotationFourierCharacter, irrationalRotationPhase, rotationFourierCharacter]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rotationFourierCharacter_primitiveUnitBlockParameter
    (β : ℝ) (h : ℤ) (N k : ℕ) :
    rotationFourierCharacter h (primitiveUnitBlockParameter β N k) =
      irrationalRotationPhase β h ^ k := by
  rw [primitiveUnitBlockParameter, rotationFourierCharacter_nat_add]
  exact rotationFourierCharacter_nat_mul β h k

/-- The normalized geometric Weyl sum for one Fourier mode. -/
def rotationWeylAverage (β : ℝ) (h : ℤ) (K : ℕ) : ℂ :=
  (∑ k ∈ range K, irrationalRotationPhase β h ^ k) / (K : ℂ)

/-- The same average indexed by the actual rotation points `β, 2β, ..., Kβ`. -/
def rotationWeylAverageFromOne (β : ℝ) (h : ℤ) (K : ℕ) : ℂ :=
  (∑ k ∈ range K, irrationalRotationPhase β h ^ (k + 1)) / (K : ℂ)

theorem rotationWeylAverageFromOne_eq (β : ℝ) (h : ℤ) (K : ℕ) :
    rotationWeylAverageFromOne β h K =
      irrationalRotationPhase β h * rotationWeylAverage β h K := by
  simp only [rotationWeylAverageFromOne, rotationWeylAverage, pow_succ]
  rw [← sum_mul]
  ring

theorem rotationWeylAverageFromOne_eq_unitBlockParameter_sum
    (β : ℝ) (h : ℤ) (N K : ℕ) :
    rotationWeylAverageFromOne β h K =
      (∑ k ∈ range K,
        rotationFourierCharacter h (primitiveUnitBlockParameter β N (k + 1))) /
          (K : ℂ) := by
  apply congrArg (fun s : ℂ => s / (K : ℂ))
  apply sum_congr rfl
  intro k hk
  rw [rotationFourierCharacter_primitiveUnitBlockParameter]

private theorem norm_geom_sum_le {z : ℂ} (hz : z ≠ 1) (hznorm : ‖z‖ = 1)
    (K : ℕ) :
    ‖∑ k ∈ range K, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ K - 1‖ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hznorm]; norm_num

/-- Every nonzero Fourier mode of an irrational rotation has vanishing Cesàro average. -/
theorem tendsto_rotationWeylAverage {β : ℝ} (hβ : Irrational β)
    {h : ℤ} (hh : h ≠ 0) :
    Tendsto (rotationWeylAverage β h) atTop (𝓝 0) := by
  let z := irrationalRotationPhase β h
  have hz : z ≠ 1 := irrationalRotationPhase_ne_one hβ hh
  have hznorm : ‖z‖ = 1 := norm_irrationalRotationPhase β h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (g := fun K : ℕ => (2 / ‖z - 1‖) / (K : ℝ))
      (fun K => norm_nonneg (rotationWeylAverage β h K))
      (fun K => ?_) ?_
  · change ‖(∑ k ∈ range K, irrationalRotationPhase β h ^ k) / (K : ℂ)‖ ≤ _
    rw [norm_div]
    simpa only [z, Complex.norm_natCast] using
      div_le_div_of_nonneg_right (norm_geom_sum_le hz hznorm K)
        (norm_nonneg ((K : ℂ)))
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem tendsto_rotationWeylAverageFromOne {β : ℝ} (hβ : Irrational β)
    {h : ℤ} (hh : h ≠ 0) :
    Tendsto (rotationWeylAverageFromOne β h) atTop (𝓝 0) := by
  rw [show rotationWeylAverageFromOne β h =
      fun K => irrationalRotationPhase β h * rotationWeylAverage β h K by
    funext K
    exact rotationWeylAverageFromOne_eq β h K]
  simpa using tendsto_const_nhds.mul (tendsto_rotationWeylAverage hβ hh)

/-- The number of rotation points occurring in the `N`-th unit block. -/
def primitiveRotationLength (β : ℝ) (N : ℕ) : ℕ :=
  ⌊((N : ℝ) + 1) / β⌋₊

theorem tendsto_primitiveRotationLength_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (primitiveRotationLength β) atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply Tendsto.atTop_div_const hβ
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- Consequently the Fourier average of the exact rotation segment in the `N`-th
solution block tends to zero. -/
theorem tendsto_primitiveBlock_rotationWeylAverage {β : ℝ}
    (hβpos : 0 < β) (hβirr : Irrational β) {h : ℤ} (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => rotationWeylAverage β h (primitiveRotationLength β N))
      atTop (𝓝 0) :=
  (tendsto_rotationWeylAverage hβirr hh).comp
    (tendsto_primitiveRotationLength_atTop hβpos)

/-- The Fourier averages of the actual initial orbit segments occurring in successive
solution blocks vanish in every nonzero mode. -/
theorem tendsto_primitiveBlock_rotationWeylAverageFromOne {β : ℝ}
    (hβpos : 0 < β) (hβirr : Irrational β) {h : ℤ} (hh : h ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        rotationWeylAverageFromOne β h (primitiveRotationLength β N))
      atTop (𝓝 0) :=
  (tendsto_rotationWeylAverageFromOne hβirr hh).comp
    (tendsto_primitiveRotationLength_atTop hβpos)

/-- In the exact ceiling parametrization of each solution block, every nonzero normalized
Fourier sum tends to zero.  This is the Weyl-sum input for blockwise equidistribution. -/
theorem tendsto_primitiveUnitBlockParameter_fourierAverage {β : ℝ}
    (hβpos : 0 < β) (hβirr : Irrational β) {h : ℤ} (hh : h ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        let K := primitiveRotationLength β N
        (∑ k ∈ range K,
          rotationFourierCharacter h
            (primitiveUnitBlockParameter β N (k + 1))) / (K : ℂ))
      atTop (𝓝 0) := by
  apply (tendsto_primitiveBlock_rotationWeylAverageFromOne hβpos hβirr hh).congr'
  filter_upwards with N
  exact rotationWeylAverageFromOne_eq_unitBlockParameter_sum β h N
    (primitiveRotationLength β N)

/-- Conditional on failure of Alaoglu--Erdős, the canonical primitive generator has
vanishing normalized Fourier sums in every nonzero mode on the exact point set in each
successive unit block. -/
theorem exists_primitiveGenerator_with_vanishing_block_fourier_modes
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ,
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      ∀ h : ℤ, h ≠ 0 →
        Tendsto
          (fun N : ℕ =>
            let K := primitiveRotationLength β N
            (∑ k ∈ range K,
              rotationFourierCharacter h
                (primitiveUnitBlockParameter β N (k + 1))) / (K : ℂ))
          atTop (𝓝 0) := by
  obtain ⟨β, hβirr, hβleast, _hunique, _hblocks, _hcounts, _hdyadic, _hcumulative⟩ :=
    exists_primitiveGenerator_with_exact_counting hfail
  exact ⟨β, hβirr, hβleast,
    fun h hh =>
      tendsto_primitiveUnitBlockParameter_fourierAverage hβleast.pos hβirr hh⟩

end

end LeanProofs.TwoBaseIntegerExponent
