import GowersSzemeredi.Proofs16GlobalSelectedProgressionMaps
import GowersSzemeredi.Proofs16PurificationMassBudget

/-! Uniform error and mass parameters for purification from the original
bihomomorphism. They depend only on the original density, and preserve the
exponential of a polynomial scale of the robust progression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalProgressionPurificationRank (alpha : Real) : Nat :=
  ⌈2+robustDifferenceBohrConstant*(globalColumnProgressionLogDensity alpha+1)^4⌉₊

def globalProgressionPurificationParentDensity (alpha : Real) : Real :=
  Real.exp (-(robustDifferenceProgressionConstant*(globalColumnProgressionLogDensity alpha+1)^8))

def globalProgressionPurificationError (alpha : Real) : Real :=
  (globalProgressionPurificationParentDensity alpha)^3/(128*(2048 : Real)^globalProgressionPurificationRank alpha)

def globalProgressionPurificationCoreDensity (alpha : Real) : Real :=
  globalProgressionPurificationParentDensity alpha/(2*(32 : Real)^globalProgressionPurificationRank alpha)

def globalProgressionPurificationModulusBound (alpha : Real) : Nat :=
  globalProgressionSelectionModulusBound alpha (globalProgressionPurificationError alpha)

theorem globalProgressionPurificationParentDensity_pos (alpha : Real) :
    0 < globalProgressionPurificationParentDensity alpha := Real.exp_pos _

theorem globalProgressionPurificationError_pos (alpha : Real) :
    0 < globalProgressionPurificationError alpha := by
  have h := globalProgressionPurificationParentDensity_pos alpha
  unfold globalProgressionPurificationError
  positivity

theorem globalProgressionPurificationCoreDensity_pos (alpha : Real) :
    0 < globalProgressionPurificationCoreDensity alpha := by
  have h := globalProgressionPurificationParentDensity_pos alpha
  unfold globalProgressionPurificationCoreDensity
  positivity

/-- The integer rank ceiling costs at most one. -/
theorem globalProgressionPurificationRank_le (alpha : Real) :
    (globalProgressionPurificationRank alpha : Real) ≤
      3+robustDifferenceBohrConstant*(globalColumnProgressionLogDensity alpha+1)^4 := by
  have hC := robustDifferenceBohrConstant_pos
  have h := (Nat.ceil_lt_add_one (show (0 : Real) ≤
    2+robustDifferenceBohrConstant*(globalColumnProgressionLogDensity alpha+1)^4 by positivity)).le
  unfold globalProgressionPurificationRank
  linarith

/-- The uniform error is admissible at every actual progression rank. -/
theorem globalProgressionPurificationError_le {alpha : Real} {r : Nat}
    (hr : r ≤ globalProgressionPurificationRank alpha) :
    globalProgressionPurificationError alpha ≤
      (globalProgressionPurificationParentDensity alpha)^3/(128*(2048 : Real)^r) := by
  have hp := globalProgressionPurificationParentDensity_pos alpha
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2048) hr
  unfold globalProgressionPurificationError
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hpow (by norm_num))

/-- The uniform core density is valid at every actual progression rank. -/
theorem globalProgressionPurificationCoreDensity_le {alpha : Real} {r : Nat}
    (hr : r ≤ globalProgressionPurificationRank alpha) :
    globalProgressionPurificationCoreDensity alpha ≤
      globalProgressionPurificationParentDensity alpha/(2*(32 : Real)^r) := by
  have hp := globalProgressionPurificationParentDensity_pos alpha
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 32) hr
  unfold globalProgressionPurificationCoreDensity
  exact div_le_div_of_nonneg_left hp.le (by positivity)
    (mul_le_mul_of_nonneg_left hpow (by norm_num))

def globalProgressionPurificationDensityConstant : Real :=
  robustDifferenceProgressionConstant+94+31*robustDifferenceBohrConstant

/-- The retained core stays on the same degree-eight exponential density
scale as the robust parent, despite the rank-dependent shrinking loss. -/
theorem globalProgressionPurificationCoreDensity_lower (alpha : Real) :
    Real.exp (-(globalProgressionPurificationDensityConstant*(globalColumnProgressionLogDensity alpha+1)^8)) ≤
      globalProgressionPurificationCoreDensity alpha := by
  let p := globalColumnProgressionLogDensity alpha
  let r := globalProgressionPurificationRank alpha
  let w := robustDifferenceProgressionConstant*(p+1)^8
  have hp : 0 ≤ p := (globalColumnProgressionLogDensity_pos alpha).le
  have hC := robustDifferenceBohrConstant_pos
  have hr : (r : Real) ≤ 3+robustDifferenceBohrConstant*(p+1)^4 := globalProgressionPurificationRank_le alpha
  have hu : 1 ≤ p+1 := by linarith
  have h48 : (p+1)^4 ≤ (p+1)^8 := pow_le_pow_right₀ hu (by decide)
  have h8 : 1 ≤ (p+1)^8 := one_le_pow₀ hu
  have hcost : w+1+31*r ≤ globalProgressionPurificationDensityConstant*(p+1)^8 := by
    dsimp only [w, globalProgressionPurificationDensityConstant]
    nlinarith only [hr,h48,h8,mul_nonneg hC.le (sub_nonneg.mpr h48)]
  have hden : 2*(32 : Real)^r ≤ Real.exp (1+31*r) := by
    have h2 : (2 : Real) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : Real)]
    have h32 : (32 : Real) ≤ Real.exp 31 := by linarith [Real.add_one_le_exp (31 : Real)]
    calc 2*(32 : Real)^r ≤ Real.exp 1*(Real.exp 31)^r :=
        mul_le_mul h2 (pow_le_pow_left₀ (by norm_num) h32 r) (by positivity) (by positivity)
      _ = Real.exp (1+31*r) := by rw [←Real.exp_nat_mul, ←Real.exp_add]; congr 1; ring
  have hlower : Real.exp (-(w+1+31*r)) ≤ Real.exp (-w)/(2*(32 : Real)^r) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc Real.exp (-(w+1+31*r))*(2*(32 : Real)^r) ≤
        Real.exp (-(w+1+31*r))*Real.exp (1+31*r) :=
          mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
      _ = Real.exp (-w) := by rw [←Real.exp_add]; congr 1; ring
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hlower

end LeanProofs.GowersSzemeredi
