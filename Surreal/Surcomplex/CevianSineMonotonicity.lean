import Surreal.Surcomplex.TrigonometricOrder

/-!
# Strict order of the cevian sine ratio

For an actual finite angle strictly between zero and pi, the function
`sin(x) / sin(alpha-x)` strictly increases between zero and that angle.
This is the uniqueness argument in the proof of
`trigonometry:thm:cevian`; all inequalities retain infinitesimal parts.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- Subtraction identities give the numerator controlling the order of cevian sine ratios. -/
theorem cevian_sine_cross_difference (α x y : SignSequence.FiniteElement.{u}) :
    finiteSin y * finiteSin (α - x) - finiteSin x * finiteSin (α - y) =
      finiteSin α * finiteSin (y - x) := by
  rw [finiteSin_sub, finiteSin_sub, finiteSin_sub]
  ring

/-- A larger split angle has a strictly larger ratio of the two positive sines. -/
theorem cevian_sine_ratio_lt (α x y : SignSequence.FiniteElement.{u})
    (hα : α.val < SignSequence.ofReal Real.pi) (hx : 0 < x.val)
    (hxy : x.val < y.val) (hy : y.val < α.val) :
    finiteSin x / finiteSin (α - x) < finiteSin y / finiteSin (α - y) := by
  have hsα : 0 < finiteSin α := finiteSin_pos_of_mem_Ioo _ ⟨by linarith, hα⟩
  have hsx : 0 < finiteSin (α - x) := by
    apply finiteSin_pos_of_mem_Ioo
    change 0 < α.val - x.val ∧ α.val - x.val < SignSequence.ofReal Real.pi
    constructor <;> linarith
  have hsy : 0 < finiteSin (α - y) := by
    apply finiteSin_pos_of_mem_Ioo
    change 0 < α.val - y.val ∧ α.val - y.val < SignSequence.ofReal Real.pi
    constructor <;> linarith
  have hsd : 0 < finiteSin (y - x) := by
    apply finiteSin_pos_of_mem_Ioo
    change 0 < y.val - x.val ∧ y.val - x.val < SignSequence.ofReal Real.pi
    constructor <;> linarith
  apply (div_lt_div_iff₀ hsx hsy).mpr
  have he := cevian_sine_cross_difference α x y
  have hp := mul_pos hsα hsd
  linarith only [he, hp]

/-- The cevian sine ratio is strictly increasing on the actual open interval of split angles. -/
theorem cevian_sine_ratio_strictMonoOn (α : SignSequence.FiniteElement.{u})
    (hα : α.val < SignSequence.ofReal Real.pi) :
    StrictMonoOn (fun x : SignSequence.FiniteElement.{u} =>
      finiteSin x / finiteSin (α - x)) {x | x.val ∈ Set.Ioo 0 α.val} := by
  intro x hx y hy hxy
  exact cevian_sine_ratio_lt α x y hα hx.1 hxy hy.2

end Surreal.Surcomplex
