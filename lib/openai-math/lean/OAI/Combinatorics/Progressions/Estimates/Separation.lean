import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

theorem eq_zero_of_integer_mul_of_abs_lt {x D : ℝ} (hD : 0 < D)
    (hgrid : ∃ z : ℤ, D * x = z) (hsmall : |x| < 1 / D) : x = 0 := by
  obtain ⟨z, hz⟩ := hgrid
  have hzsmall : |(z : ℝ)| < 1 := by
    rw [← hz, abs_mul, abs_of_pos hD]
    have h := (lt_div_iff₀ hD).mp hsmall
    nlinarith
  have hz0 : z = 0 := by
    have h : |z| < (1 : ℤ) := by exact_mod_cast hzsmall
    have hnonneg := abs_nonneg z
    have habs : |z| = 0 := by omega
    exact abs_eq_zero.mp habs
  rw [hz0, Int.cast_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hD.ne'

theorem separate_kernel {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V →ₗ[ℝ] (ι → ℝ)) (a b : V) {D : ℝ} (hD : 0 < D)
    (hsum : Q (a + b) = 0)
    (hgrid : ∀ i, ∃ z : ℤ, D * Q b i = z)
    (hsmall : ∀ i, |Q a i| < 1 / D) : Q a = 0 ∧ Q b = 0 := by
  have hcoords : ∀ i, Q a i + Q b i = 0 := by
    intro i
    have h := congrFun hsum i
    simpa only [map_add, Pi.add_apply, Pi.zero_apply] using h
  have hb : Q b = 0 := by
    funext i
    apply eq_zero_of_integer_mul_of_abs_lt hD (hgrid i)
    have hneg : Q b i = -(Q a i) := by linarith [hcoords i]
    simpa only [hneg, abs_neg] using hsmall i
  refine ⟨?_, hb⟩
  funext i
  change Q a i = 0
  have hbi : Q b i = 0 := congrFun hb i
  linarith [hcoords i]

end Erdos3

end

end OAI
