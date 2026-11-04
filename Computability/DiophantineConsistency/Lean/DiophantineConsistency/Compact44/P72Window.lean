import DiophantineConsistency.Compact44.P72Mu

/-! # P13, section 4: the rank window

`q = F + (C + α)` has three positive summands. The masks satisfy `MC < β` and
`MF < 2β`, and `βJ = q − 1`. Hence

  `R = ((q−1)(q−F) + α)(q²−1) + (MC + MF·q)·J < q⁴ − 1`

without any transport sign, and `R ≥ q² − 1`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P72Window
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing P72Root
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem window_ring {q F α C β J MC MF : DiffRing V} (hq : q = F + (C + α))
    (hF : 1 ≤ F) (hα : 1 ≤ α) (hC : 1 ≤ C) (hJ : 1 ≤ J) (hβJ : β * J = q - 1)
    (hMC' : MC + 1 ≤ β) (hMF' : MF + 1 ≤ 2 * β) :
    ((q - 1) * (q - F) + α) * (q * q - 1) + (MC + MF * q) * J + 1 < q * (q * (q * q)) := by
  have hq3 : 3 ≤ q := by rw [hq]; linarith
  have hG : (q - 1) * (q - F) + α ≤ q * q - q - 1 := by
    have h1 : q - F ≤ q - 1 := by linarith
    have h2 : (q - 1) * (q - F) ≤ (q - 1) * (q - 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : α ≤ q - 2 := by rw [hq]; linarith
    nlinarith
  have hqq : 0 ≤ q * q - 1 := by nlinarith
  have hGq : ((q - 1) * (q - F) + α) * (q * q - 1) ≤ (q * q - q - 1) * (q * q - 1) :=
    mul_le_mul_of_nonneg_right hG hqq
  have hW : (MC + MF * q) * J ≤ ((β - 1) + (2 * β - 1) * q) * J := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : MF * q ≤ (2 * β - 1) * q := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hW2 : ((β - 1) + (2 * β - 1) * q) * J = (1 + 2 * q) * (q - 1) - (1 + q) * J := by
    rw [← hβJ]; ring
  have hJq : (1 + q) * 1 ≤ (1 + q) * J := mul_le_mul_of_nonneg_left hJ (by linarith)
  nlinarith

end P72Window

#print axioms P72Window.window_ring
