import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import Mathlib.Tactic.Ring

/-! Triangle-only extraction from BusyBeaver.ZFC.ArithmeticCantor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CompactControllerTriangle
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

def triangle (s : V) : V := s * (s + 1) / 2

lemma triangle_double (s : V) : 2 * triangle s = s * (s + 1) := by
  apply (mul_div_self_of_dvd).2
  rcases even_or_odd s with ⟨r, h | h⟩
  · refine ⟨r * (s + 1), ?_⟩
    rw [h]
    ring
  · refine ⟨s * (r + 1), ?_⟩
    rw [h]
    ring

lemma triangle_succ (s : V) : triangle (s + 1) = triangle s + s + 1 := by
  apply mul_left_cancel₀ (show (2 : V) ≠ 0 by simp)
  rw [mul_add, mul_add, triangle_double, triangle_double]
  ring

lemma le_triangle (s : V) : s ≤ triangle s := by
  rcases Arithmetic.zero_le s with (rfl | hs)
  · simp [triangle]
  · have h1 : 1 ≤ s := by simpa using (lt_iff_succ_le.mp hs)
    have hm : 2 * s ≤ s * (s + 1) := by
      have := mul_le_mul_of_nonneg_left (add_le_add_right h1 1) (Arithmetic.zero_le s)
      simpa [one_add_one_eq_two, mul_comm, add_comm] using this
    apply (mul_le_mul_iff_right₀ (show (0 : V) < 2 by simp)).mp
    rwa [triangle_double]

#print axioms triangle_succ
#print axioms le_triangle
end DiophantineConsistency.CompactControllerTriangle
