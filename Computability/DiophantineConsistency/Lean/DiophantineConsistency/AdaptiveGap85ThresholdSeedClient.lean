import DiophantineConsistency.AdaptiveGap85ThresholdArithmetic
import DiophantineConsistency.AdaptiveGap85ThresholdSeed

/-! The actual auxiliary seed relations force the shift T threshold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThresholdSeedClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence AdaptiveGap85ThresholdArithmetic AdaptiveGap85ThresholdSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact seed equations and outer-coordinate bounds imply the shift threshold. -/
theorem seed_relations_exceed_shift (a R b q Y c f i T u : V)
    (hR : 5≤R) (hc : c=ycoord R a) (hi : 0<i) (hf : 0<f)
    (hq : 1≤q) (hb : b≤q) (hY : Y≤c) (hq3 : q^3≤c)
    (hn : f*f=1+delta a*(i*c*c)*(i*c*c))
    (hux : let I:=delta a*i*c*c; xcoord R (I-2)=I*u)
    (he : f*f*c*T=u+c+f*f*R) :
    b*(Y*(q*q))*(q*q-1)<T := by
  let I : V := delta a*i*c*c
  have hc0 : 0<c := by
    rw [hc]
    exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0:V)<5) hR) (time_le_y R a)
  have hnorm : I*I+delta a=delta a*(f*f) := by
    calc
      I*I+delta a=delta a*(1+delta a*(i*c*c)*(i*c*c)) := by dsimp [I]; ring
      _=delta a*(f*f) := by rw [←hn]
  obtain ⟨hI,hfbound⟩ := strong_seed_estimates a c i f I hc0 hi hf rfl hnorm
  have hc1 : 1≤c := pos_iff_one_le.mp hc0
  have hc2 : (1:V)≤c*c := one_le_mul hc1 hc1
  have hI2 : 2≤I := calc
    (2:V)=2*1 := by ring
    _≤2*(c*c) := mul_le_mul_of_nonneg_left hc2 (by simp)
    _=2*c*c := by ring
    _≤I := hI
  have hu : I^4≤u := odd_quotient_growth I R u hI2 hR hux
  exact auxiliary_T_exceeds_shift b q Y c I f T u R hc0 hq hb hY hq3 hI hfbound hu he
end DiophantineConsistency.AdaptiveGap85ThresholdSeedClient
