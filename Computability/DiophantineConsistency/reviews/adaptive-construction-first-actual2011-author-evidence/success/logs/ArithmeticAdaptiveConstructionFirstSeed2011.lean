import DiophantineConsistency.ArithmeticAdaptiveConstructionSeedSize2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstPositive2011
import DiophantineConsistency.ArithmeticOuterSeed

/-! Bind the first-carrier positivity proof to the actual outer-seed relation. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstSeed2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticOuterSeed ArithmeticAdaptiveConstructionSeedSize2011
  ArithmeticAdaptiveConstructionFirstPositive2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual seed supplies the size and norm premises. The lower radix bound
and nonzero transport quotient remain explicit construction obligations. -/
theorem positive_first_of_seed (u R s n eta zeta gammaOld b : V)
    (hs : 0<s) (hphase : R%4=3) (hq : 2≤Exp.exp u-1) (hb : 1≤b)
    (hseed : SeedRelations u R s n eta zeta gammaOld) :
    let q := Exp.exp u
    let X := Exp.exp R
    let Y := s*q^3
    let Q := X*Y*Y
    let k := eta+zeta
    let ell := Q*k
    let tau := X*Y*n+k-R
    ∃ r : V, 0<r ∧ ell+k+r+s=(1+(q-1)*k)*b+tau ∧
      (q^3*(q-1))*(ell+k+r)+(q^3*s)*(q-1) =
        (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*b) := by
  dsimp only
  have hqpos : (0:V)<Exp.exp u := lt_of_lt_of_le (by norm_num) (one_le_exp u)
  have hXpos : (0:V)<Exp.exp R := lt_of_lt_of_le (by norm_num) (one_le_exp R)
  have hYpos : (0:V)<s*(Exp.exp u)^3 := mul_pos hs (pow_pos hqpos _)
  dsimp only [SeedRelations] at hseed
  obtain ⟨hnorm,_,_,_,r,hr,_,hk⟩ := hseed
  have ht : (2:V)≤r+1 := by
    rcases zero_or_succ r with hz | ⟨z,hz⟩
    · rw [hz] at hr
      simp at hr
      rw [hr] at hphase
      norm_num at hphase
    · rw [hz]
      have hz0 := Arithmetic.zero_le z
      calc (2:V) = 0+1+1 := by norm_num
           _ ≤ z+1+1 := by simpa only [add_assoc, add_comm, add_left_comm] using
             add_le_add_right (add_le_add_right hz0 1) 1
  have hsize := seed_ordinate_le_k (Exp.exp u) (Exp.exp R) (s*(Exp.exp u)^3)
    s (eta+zeta) (r+1) hqpos hXpos hYpos rfl ht hk
  exact positive_first_carrier (Exp.exp u) (Exp.exp R*(s*(Exp.exp u)^3)*(s*(Exp.exp u)^3))
    (eta+zeta) s b (Exp.exp R*(s*(Exp.exp u)^3)*n+(eta+zeta)-R) hq hb hsize hnorm
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstSeed2011
