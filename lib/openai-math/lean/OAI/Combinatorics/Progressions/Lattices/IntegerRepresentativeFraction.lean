import OAI.Combinatorics.Progressions.Fourier.CRTConfigurationTorus

namespace OAI

section

namespace Erdos3

theorem integer_fraction_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    Int.fract ((a : ℝ) / N) = (((a : ZMod N).val : ℝ) / N) := by
  rw [Int.fract_div_intCast_eq_div_intCast_mod]
  exact congrArg (fun z : ℤ => (z : ℝ) / N) (ZMod.val_intCast a).symm

theorem integer_sub_floor_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    a - (N : ℤ) * ⌊(a : ℝ) / N⌋ = ((a : ZMod N).val : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast, ZMod.val_intCast]
  have h := Int.emod_add_mul_ediv a (N : ℤ)
  omega

end Erdos3

end

end OAI
