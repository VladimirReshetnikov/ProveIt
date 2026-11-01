import DiophantineConsistency.AdaptiveGap85ActualFourthRoot
import DiophantineConsistency.AdaptiveGap85FourthLargeY
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ActualFourthLargeQ
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence AdaptiveGap85Literal
open AdaptiveGap85FirstDivisibility AdaptiveGap85ActualFourthRoot AdaptiveGap85FourthLargeY
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For an actual positive 85-zero at main index four, q≥5 forces X=16. -/
theorem actual_fourth_main_X16_of_large_q (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (h4 : v 9+v 7*(v 9+v 10) = ycoord 4 (v 6*v 7+v 7))
    (hq : 5≤1+v 0*(p 0:V)) : v 6=16 := by
  let q : V := 1+v 0*(p 0:V)
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient85 p v hb hv hz
  have hq3 : q*q*q∣v 7 := by
    refine ⟨s,?_⟩
    change v 7=(q*(q*q))*s at hs
    calc
      _ = (q*(q*q))*s := hs
      _ = (q*q*q)*s := by ring
  have h125 : (125:V)≤q*q*q := by
    have h25 : (25:V)≤q*q := by
      have hh := mul_le_mul hq hq (by simp) (by simp)
      calc
        _ = 5*5 := by ring
        _ ≤ _ := hh
    have hh := mul_le_mul h25 hq (by simp) (by simp)
    calc
      _ = 25*5 := by ring
      _ ≤ _ := hh
  have hY125 : 125≤v 7 := le_trans h125 (Arithmetic.le_of_dvd (hv 7) hq3)
  have hY109 : 109≤v 7 := le_trans (by norm_num : (109:V)≤125) hY125
  exact fourth_congruence_large_Y (v 6) (v 7) hY109 (actual_fourth_main_congruences p v hb hv hz h4)
end DiophantineConsistency.AdaptiveGap85ActualFourthLargeQ
