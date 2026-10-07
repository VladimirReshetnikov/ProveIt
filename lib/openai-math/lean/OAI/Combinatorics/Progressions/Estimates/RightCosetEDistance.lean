import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

section

namespace Erdos3

open scoped ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

noncomputable def rightCosetEDist (Γ : Subgroup G) (x y : G) : ℝ≥0∞ :=
  ⨅ γ : Γ, edist x (y * γ)

theorem rightCosetEDist_le (Γ : Subgroup G) (x y : G) :
    rightCosetEDist Γ x y ≤ edist x y := by
  unfold rightCosetEDist
  exact iInf_le_of_le (1 : Γ) (by simp)

@[simp] theorem rightCosetEDist_self (Γ : Subgroup G) (x : G) : rightCosetEDist Γ x x = 0 :=
  le_antisymm ((rightCosetEDist_le Γ x x).trans_eq (edist_self x)) bot_le

variable [IsIsometricSMul Gᵐᵒᵖ G]

theorem rightCosetEDist_comm (Γ : Subgroup G) (x y : G) :
    rightCosetEDist Γ x y = rightCosetEDist Γ y x := by
  have h : ∀ a b : G, rightCosetEDist Γ a b ≤ rightCosetEDist Γ b a := by
    intro a b
    apply le_iInf
    intro γ
    apply (iInf_le (fun δ : Γ => edist a (b * δ)) γ⁻¹).trans_eq
    rw [← edist_mul_right a (b * (γ⁻¹ : Γ)) (γ : G)]
    simp only [Subgroup.coe_inv, inv_mul_cancel_right, edist_comm]
  exact le_antisymm (h x y) (h y x)

omit [IsIsometricSMul Gᵐᵒᵖ G] in
theorem rightCosetEDist_mul_right (Γ : Subgroup G) (x y : G) (δ : Γ) :
    rightCosetEDist Γ x (y * δ) = rightCosetEDist Γ x y := by
  apply le_antisymm
  · apply le_iInf
    intro γ
    apply (iInf_le (fun a : Γ => edist x (y * δ * a)) (δ⁻¹ * γ)).trans_eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]
  · apply le_iInf
    intro γ
    apply (iInf_le (fun a : Γ => edist x (y * a)) (δ * γ)).trans_eq
    simp only [Subgroup.coe_mul, mul_assoc]

theorem rightCosetEDist_mul_left (Γ : Subgroup G) (x y : G) (δ : Γ) :
    rightCosetEDist Γ (x * δ) y = rightCosetEDist Γ x y := by
  rw [rightCosetEDist_comm, rightCosetEDist_mul_right, rightCosetEDist_comm]

theorem rightCosetEDist_triangle (Γ : Subgroup G) (x y z : G) :
    rightCosetEDist Γ x z ≤ rightCosetEDist Γ x y + rightCosetEDist Γ y z := by
  apply ENNReal.le_iInf_add_iInf
  intro a b
  apply (iInf_le (fun γ : Γ => edist x (z * γ)) (b * a)).trans
  calc
    edist x (z * ↑(b * a)) ≤ edist x (y * a) + edist (y * a) (z * ↑(b * a)) :=
      edist_triangle _ _ _
    _ = edist x (y * a) + edist y (z * b) := by
      simp only [Subgroup.coe_mul, ← mul_assoc, edist_mul_right]

theorem rightCosetEDist_rel (Γ : Subgroup G) {x x' y y' : G}
    (hx : QuotientGroup.leftRel Γ x x') (hy : QuotientGroup.leftRel Γ y y') :
    rightCosetEDist Γ x y = rightCosetEDist Γ x' y' := by
  let a : Γ := ⟨x⁻¹ * x', QuotientGroup.leftRel_apply.mp hx⟩
  let b : Γ := ⟨y⁻¹ * y', QuotientGroup.leftRel_apply.mp hy⟩
  have ha : x * a = x' := by simp only [a, mul_inv_cancel_left]
  have hb : y * b = y' := by simp only [b, mul_inv_cancel_left]
  rw [← ha, ← hb, rightCosetEDist_mul_left, rightCosetEDist_mul_right]

noncomputable def quotientRightEDist (Γ : Subgroup G) : (G ⧸ Γ) → (G ⧸ Γ) → ℝ≥0∞ :=
  Quotient.lift₂ (rightCosetEDist Γ) (fun _ _ _ _ hx hy => rightCosetEDist_rel Γ hx hy)

@[simp] theorem quotientRightEDist_mk (Γ : Subgroup G) (x y : G) :
    quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) = rightCosetEDist Γ x y := rfl

@[simp] theorem quotientRightEDist_self (Γ : Subgroup G) (x : G ⧸ Γ) :
    quotientRightEDist Γ x x = 0 :=
  Quotient.inductionOn x (rightCosetEDist_self Γ)

theorem quotientRightEDist_comm (Γ : Subgroup G) (x y : G ⧸ Γ) :
    quotientRightEDist Γ x y = quotientRightEDist Γ y x :=
  Quotient.inductionOn₂ x y (rightCosetEDist_comm Γ)

theorem quotientRightEDist_triangle (Γ : Subgroup G) (x y z : G ⧸ Γ) :
    quotientRightEDist Γ x z ≤ quotientRightEDist Γ x y + quotientRightEDist Γ y z :=
  Quotient.inductionOn₃ x y z (rightCosetEDist_triangle Γ)

theorem quotientRightEDist_mk_le (Γ : Subgroup G) (x y : G) :
    quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) ≤ edist x y :=
  rightCosetEDist_le Γ x y

omit [PseudoEMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] in
theorem quotient_mk_mul_mem (Γ : Subgroup G) (x : G) (γ : Γ) :
    (QuotientGroup.mk (x * γ) : G ⧸ Γ) = QuotientGroup.mk x := by
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  simpa only [inv_mul_cancel_left] using γ.property

end Erdos3

end

end OAI
