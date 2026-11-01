import DiophantineConsistency.ArithmeticPellRecurrence

/-! Outer-seed lower bounds needed for the 85 shift threshold. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThresholdOuter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive outer coordinates give q³≤c and Y≤c for Y=s*q³. -/
theorem outer_seed_lower_bounds (q s eta zeta : V)
    (hs : 0<s) (heta : 0<eta) (hzeta : 0<zeta) :
    let Y := s*q^3
    let c := eta+Y*(eta+zeta)
    q^3≤c ∧ Y≤c := by
  let Y := s*q^3
  let c := eta+Y*(eta+zeta)
  have hs1 : 1≤s := pos_iff_one_le.mp hs
  have hk : 0<eta+zeta := add_pos heta hzeta
  have hk1 : 1≤eta+zeta := pos_iff_one_le.mp hk
  have hY : Y≤c := calc
    Y≤Y*(eta+zeta) := le_mul_of_one_le_right (by simp) hk1
    _≤eta+Y*(eta+zeta) := by simp
  have hq3 : q^3≤Y := by
    dsimp [Y]
    exact le_mul_of_one_le_left (by simp) hs1
  exact ⟨le_trans hq3 hY,hY⟩
end DiophantineConsistency.AdaptiveGap85ThresholdOuter
