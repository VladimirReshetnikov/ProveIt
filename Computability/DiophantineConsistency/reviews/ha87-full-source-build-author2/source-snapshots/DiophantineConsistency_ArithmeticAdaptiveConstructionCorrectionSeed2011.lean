import DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionPositive2011
import DiophantineConsistency.ArithmeticOuterSeed

/-! Apply the positive correction to the actual outer-seed relation. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionSeed2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticOuterSeed ArithmeticAdaptiveConstructionCorrectionPositive2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual outer seed and phase supply the adaptive main correction. The
relation between its radix and the deleted multiplier is still a hypothesis. -/
theorem positive_correction_of_seed (u R s n eta zeta gammaOld w : V)
    (hs : 0<s) (hg : 0<gammaOld) (hphase : R%4=3)
    (hXq : Exp.exp R=Exp.exp u*w)
    (hseed : SeedRelations u R s n eta zeta gammaOld) :
    ∃ t gamma : V, 0<gamma ∧
      eta+zeta=R+1+((s*(Exp.exp u)^3)*(Exp.exp u)^2)*t ∧
      gamma+w=gammaOld+t := by
  have hq : (0:V)<Exp.exp u := lt_of_lt_of_le (by norm_num) (one_le_exp u)
  have hX : (0:V)<Exp.exp R := lt_of_lt_of_le (by norm_num) (one_le_exp R)
  have hY : (0:V)<s*(Exp.exp u)^3 := mul_pos hs (pow_pos hq _)
  dsimp only [SeedRelations] at hseed
  obtain ⟨_,_,_,_,r,hr,_,hk⟩ := hseed
  have ht : (2:V)≤r+1 := by
    rcases zero_or_succ r with hz | ⟨z,hz⟩
    · rw [hz] at hr
      simp at hr
      rw [hr] at hphase
      norm_num at hphase
    · rw [hz]
      have hz0 := Arithmetic.zero_le z
      calc (2:V) = 0+1+1 := by norm_num
           _ ≤ z+1+1 := by simpa only [add_assoc, add_comm, add_left_comm] using add_le_add_right (add_le_add_right hz0 1) 1
  have hR : R+1=2*(r+1) := by rw [hr]; ring
  exact positive_main_correction (Exp.exp u) (Exp.exp R) (s*(Exp.exp u)^3) s R
    (eta+zeta) (r+1) w gammaOld hq hX hY hs hg rfl hXq ht hR hk
end DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionSeed2011
