import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def complexMaskComponent (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

def complexMaskSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def complexPositiveMask (t : Bool × Bool) (z : ℂ) : ℝ :=
  (1 + complexMaskSign t.2 * complexMaskComponent t.1 z) / 2

def complexMaskCoefficient (t : Bool × Bool) : ℂ :=
  (complexMaskSign t.2 : ℂ) * (if t.1 then 1 else Complex.I)

theorem complexMaskComponent_abs_le (b : Bool) (z : ℂ) :
    |complexMaskComponent b z| ≤ ‖z‖ := by
  cases b
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

theorem complexPositiveMask_bounds (t : Bool × Bool) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ complexPositiveMask t z ∧ complexPositiveMask t z ≤ 1 := by
  have hs : |complexMaskSign t.2| = 1 := by cases t.2 <;> norm_num [complexMaskSign]
  have h : |complexMaskSign t.2 * complexMaskComponent t.1 z| ≤ 1 := by
    rw [abs_mul, hs, one_mul]
    exact (complexMaskComponent_abs_le t.1 z).trans hz
  obtain ⟨hl, hu⟩ := abs_le.mp h
  dsimp [complexPositiveMask]
  constructor <;> linarith

theorem complexPositiveMask_lipschitz (t : Bool × Bool) :
    LipschitzWith 1 (complexPositiveMask t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hs : |complexMaskSign t.2| = 1 := by cases t.2 <;> norm_num [complexMaskSign]
  have hc : complexMaskComponent t.1 (z - w) =
      complexMaskComponent t.1 z - complexMaskComponent t.1 w := by
    cases t.1 <;> rfl
  have he : complexPositiveMask t z - complexPositiveMask t w =
      complexMaskSign t.2 * complexMaskComponent t.1 (z - w) / 2 := by
    rw [hc]
    dsimp [complexPositiveMask]
    ring
  rw [NNReal.coe_one, one_mul, Real.dist_eq, he, abs_div, abs_mul, hs, one_mul]
  norm_num only [show |(2 : ℝ)| = 2 by norm_num]
  rw [dist_eq_norm]
  linarith [complexMaskComponent_abs_le t.1 (z - w), norm_nonneg (z - w)]

theorem complexMaskCoefficient_norm (t : Bool × Bool) : ‖complexMaskCoefficient t‖ = 1 := by
  rcases t with ⟨b, c⟩
  cases b <;> cases c <;> norm_num [complexMaskCoefficient, complexMaskSign]

theorem complexPositiveMask_expansion (z : ℂ) :
    z = ∑ t : Bool × Bool, complexMaskCoefficient t * (complexPositiveMask t z : ℂ) := by
  apply Complex.ext <;>
    simp [Fintype.sum_prod_type, complexMaskCoefficient,
      complexPositiveMask, complexMaskSign, complexMaskComponent] <;> ring

end Erdos3

end

end OAI
