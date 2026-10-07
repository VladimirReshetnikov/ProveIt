import Mathlib

namespace OAI

section

namespace Erdos3

variable {ι : Type*}

noncomputable def integerPeriodicTorusLift (F : (ι → ℝ) → ℂ) (x : UnitAddTorus ι) : ℂ :=
  F (fun i => (AddCircle.equivIoc 1 0 (x i)).val)

theorem integerPeriodicTorusLift_coe (F : (ι → ℝ) → ℂ)
    (hF : ∀ (x : ι → ℝ) (n : ι → ℤ), F (fun i => x i + (n i : ℝ)) = F x)
    (x : ι → ℝ) : integerPeriodicTorusLift F (fun i => (x i : UnitAddCircle)) = F x := by
  classical
  let y : ι → ℝ := fun i => (AddCircle.equivIoc 1 0 (x i : UnitAddCircle)).val
  have hzero (i : ι) : (((y i - x i : ℝ) : UnitAddCircle)) = 0 := by
    simp [y]
  choose n hn using fun i => (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp (hzero i)
  have hy : y = fun i => x i + (n i : ℝ) := by
    funext i
    have hi : (n i : ℝ) = y i - x i := by simpa only [zsmul_eq_mul, mul_one] using hn i
    linarith
  change F y = F x
  rw [hy, hF]

theorem continuous_integerPeriodicTorusLift (F : (ι → ℝ) → ℂ) (hc : Continuous F)
    (hF : ∀ (x : ι → ℝ) (n : ι → ℤ), F (fun i => x i + (n i : ℝ)) = F x) :
    Continuous (integerPeriodicTorusLift F) := by
  have hq : IsOpenQuotientMap (fun x : ι → ℝ => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hq.isQuotientMap.continuous_iff.mpr
  convert hc using 1
  funext x
  exact integerPeriodicTorusLift_coe F hF x

end Erdos3

end

end OAI
