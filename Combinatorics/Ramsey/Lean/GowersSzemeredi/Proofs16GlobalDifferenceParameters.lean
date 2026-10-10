import GowersSzemeredi.Proofs16GlobalPurificationParameters

/-! Uniform source accuracy and proper-progression mass for the eight-term
and difference-map stages, preserving an exponential of a polynomial scale. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalProgressionDifferenceError (alpha : Real) : Real :=
  (globalProgressionPurificationParentDensity alpha)^3/(1024*(65536 : Real)^globalProgressionPurificationRank alpha)

def globalDifferenceProgressionDensity (alpha : Real) : Real :=
  globalProgressionPurificationParentDensity alpha/(2048 : Real)^globalProgressionPurificationRank alpha

def globalDifferenceProgressionModulusBound (alpha : Real) : Nat :=
  globalProgressionSelectionModulusBound alpha (globalProgressionDifferenceError alpha)

theorem globalProgressionDifferenceError_pos (alpha : Real) : 0 < globalProgressionDifferenceError alpha := by
  have hp := globalProgressionPurificationParentDensity_pos alpha
  unfold globalProgressionDifferenceError
  positivity

theorem globalDifferenceProgressionDensity_pos (alpha : Real) : 0 < globalDifferenceProgressionDensity alpha := by
  have hp := globalProgressionPurificationParentDensity_pos alpha
  unfold globalDifferenceProgressionDensity
  positivity

theorem globalProgressionDifferenceError_le {alpha : Real} {r : Nat}
    (hr : r ≤ globalProgressionPurificationRank alpha) :
    globalProgressionDifferenceError alpha ≤
      (globalProgressionPurificationParentDensity alpha)^3/(1024*(65536 : Real)^r) := by
  have hp := globalProgressionPurificationParentDensity_pos alpha
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 65536) hr
  unfold globalProgressionDifferenceError
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hpow (by norm_num))

theorem globalDifferenceProgressionDensity_le {alpha : Real} {r : Nat}
    (hr : r ≤ globalProgressionPurificationRank alpha) :
    globalDifferenceProgressionDensity alpha ≤ globalProgressionPurificationParentDensity alpha/(2048 : Real)^r := by
  have hp := globalProgressionPurificationParentDensity_pos alpha
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2048) hr
  unfold globalDifferenceProgressionDensity
  exact div_le_div_of_nonneg_left hp.le (by positivity) hpow

def globalDifferenceProgressionDensityConstant : Real :=
  robustDifferenceProgressionConstant+33+11*robustDifferenceBohrConstant

/-- Use `2048=2^11` and `2<=exp(1)` to keep the logarithmic shrinking
cost at `11*rank`, instead of bounding it by the progression side factor. -/
theorem globalDifferenceProgressionDensity_lower (alpha : Real) :
    Real.exp (-(globalDifferenceProgressionDensityConstant*(globalColumnProgressionLogDensity alpha+1)^8)) ≤
      globalDifferenceProgressionDensity alpha := by
  let p := globalColumnProgressionLogDensity alpha
  let r := globalProgressionPurificationRank alpha
  let w := robustDifferenceProgressionConstant*(p+1)^8
  have hp : 0 ≤ p := (globalColumnProgressionLogDensity_pos alpha).le
  have hC := robustDifferenceBohrConstant_pos
  have hr : (r : Real) ≤ 3+robustDifferenceBohrConstant*(p+1)^4 := globalProgressionPurificationRank_le alpha
  have hu : 1 ≤ p+1 := by linarith
  have h48 : (p+1)^4 ≤ (p+1)^8 := pow_le_pow_right₀ hu (by decide)
  have h8 : 1 ≤ (p+1)^8 := one_le_pow₀ hu
  have hcost : w+11*r ≤ globalDifferenceProgressionDensityConstant*(p+1)^8 := by
    dsimp only [w, globalDifferenceProgressionDensityConstant]
    nlinarith only [hr,h48,h8,mul_nonneg hC.le (sub_nonneg.mpr h48)]
  have hbase : (2048 : Real) ≤ Real.exp 11 := by
    have h2 : (2 : Real) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : Real)]
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) h2 11
    rw [←Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have hden : (2048 : Real)^r ≤ Real.exp (11*r) := by
    calc (2048 : Real)^r ≤ (Real.exp 11)^r := pow_le_pow_left₀ (by norm_num) hbase r
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring
  have hlower : Real.exp (-(w+11*r)) ≤ Real.exp (-w)/(2048 : Real)^r := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc Real.exp (-(w+11*r))*(2048 : Real)^r ≤ Real.exp (-(w+11*r))*Real.exp (11*r) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
      _ = Real.exp (-w) := by rw [←Real.exp_add]; congr 1; ring
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hlower

end LeanProofs.GowersSzemeredi
