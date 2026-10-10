import GowersSzemeredi.Proofs16GlobalDifferenceParameters

/-! Uniform density of the original N^7 agreement family. Powers of two
keep the logarithmic rank cost explicit and preserve the parent's
degree-eight exponential density scale. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalOriginalEightAgreementDensity (alpha : Real) : Real :=
  globalProgressionPurificationParentDensity alpha*(globalProgressionRepresentationDensity alpha)^2/
    (8*(1024 : Real)^globalProgressionPurificationRank alpha)

theorem globalOriginalEightAgreementDensity_pos (alpha : Real) : 0 < globalOriginalEightAgreementDensity alpha := by
  have hd := globalProgressionPurificationParentDensity_pos alpha
  have hk := globalProgressionRepresentationDensity_pos alpha
  unfold globalOriginalEightAgreementDensity
  positivity

theorem globalOriginalEightAgreementDensity_le {alpha : Real} {r : Nat}
    (hr : r ≤ globalProgressionPurificationRank alpha) :
    globalOriginalEightAgreementDensity alpha ≤ globalProgressionPurificationParentDensity alpha*
      (globalProgressionRepresentationDensity alpha)^2/(8*(1024 : Real)^r) := by
  have hd := globalProgressionPurificationParentDensity_pos alpha
  have hk := globalProgressionRepresentationDensity_pos alpha
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 1024) hr
  unfold globalOriginalEightAgreementDensity
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hpow (by norm_num))

def globalOriginalEightAgreementDensityConstant : Real :=
  robustDifferenceProgressionConstant+47+10*robustDifferenceBohrConstant

theorem globalOriginalEightAgreementDensity_lower (alpha : Real) :
    Real.exp (-(globalOriginalEightAgreementDensityConstant*(globalColumnProgressionLogDensity alpha+1)^8)) ≤
      globalOriginalEightAgreementDensity alpha := by
  let p := globalColumnProgressionLogDensity alpha
  let r := globalProgressionPurificationRank alpha
  let w := robustDifferenceProgressionConstant*(p+1)^8
  have hp : 0 ≤ p := (globalColumnProgressionLogDensity_pos alpha).le
  have hC := robustDifferenceBohrConstant_pos
  have hr : (r : Real) ≤ 3+robustDifferenceBohrConstant*(p+1)^4 := globalProgressionPurificationRank_le alpha
  have hu : 1 ≤ p+1 := by linarith
  have h48 : (p+1)^4 ≤ (p+1)^8 := pow_le_pow_right₀ hu (by decide)
  have h8 : 1 ≤ (p+1)^8 := one_le_pow₀ hu
  have hp8 : p ≤ (p+1)^8 := by
    have h := pow_le_pow_right₀ hu (by decide : 1 ≤ (8 : Nat))
    simp only [pow_one] at h
    linarith
  have hcost : w+8*p+9+10*r ≤ globalOriginalEightAgreementDensityConstant*(p+1)^8 := by
    dsimp only [w,globalOriginalEightAgreementDensityConstant]
    nlinarith only [hr,h48,h8,hp8,mul_nonneg hC.le (sub_nonneg.mpr h48)]
  have h2 : (2 : Real) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : Real)]
  have h512 : (512 : Real) ≤ Real.exp 9 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) h2 9
    rw [←Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have h1024 : (1024 : Real) ≤ Real.exp 10 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) h2 10
    rw [←Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have hden : 512*(1024 : Real)^r ≤ Real.exp (9+10*r) := by
    calc 512*(1024 : Real)^r ≤ Real.exp 9*(Real.exp 10)^r :=
        mul_le_mul h512 (pow_le_pow_left₀ (by norm_num) h1024 r) (by positivity) (by positivity)
      _ = _ := by rw [←Real.exp_nat_mul,←Real.exp_add]; congr 1; ring
  have heq : globalOriginalEightAgreementDensity alpha = Real.exp (-(w+8*p))/(512*(1024 : Real)^r) := by
    unfold globalOriginalEightAgreementDensity globalProgressionPurificationParentDensity globalProgressionRepresentationDensity
    rw [div_pow,←pow_mul,←Real.exp_nat_mul]
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    have hexp : (8 : Real)*(-p) = -8*p := by ring
    rw [hexp,←mul_div_assoc,←Real.exp_add]
    dsimp only [w,p,r]
    have harg : -(robustDifferenceProgressionConstant*(globalColumnProgressionLogDensity alpha+1)^8)+
        -8*globalColumnProgressionLogDensity alpha =
      -(robustDifferenceProgressionConstant*(globalColumnProgressionLogDensity alpha+1)^8+8*globalColumnProgressionLogDensity alpha) := by ring
    rw [harg]
    ring
  have hlower : Real.exp (-(w+8*p+9+10*r)) ≤ globalOriginalEightAgreementDensity alpha := by
    rw [heq]
    apply (le_div_iff₀ (by positivity)).mpr
    calc Real.exp (-(w+8*p+9+10*r))*(512*(1024 : Real)^r) ≤
        Real.exp (-(w+8*p+9+10*r))*Real.exp (9+10*r) := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
      _ = Real.exp (-(w+8*p)) := by rw [←Real.exp_add]; congr 1; ring
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hlower

end LeanProofs.GowersSzemeredi
