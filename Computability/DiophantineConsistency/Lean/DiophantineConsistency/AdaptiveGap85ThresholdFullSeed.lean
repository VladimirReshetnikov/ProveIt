import DiophantineConsistency.AdaptiveGap85ThresholdSeedClient
import DiophantineConsistency.AdaptiveGap85ThresholdOuter

/-! The precise auxiliary seed equations and the outer seed force the shift threshold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThresholdFullSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence AdaptiveGap85ThresholdSeedClient AdaptiveGap85ThresholdOuter
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For positive outer-seed coordinates, the actual auxiliary-seed equations imply
    the T threshold required by the full-factor gap-violating shift. -/
theorem full_seed_exceeds_shift (a R b s eta zeta f i T u : V)
    (hR : 5 ≤ R) (hs : 0 < s) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hi : 0 < i) (hf : 0 < f)
    (hc : let q := 1+b; let Y := s*q^3; eta+Y*(eta+zeta)=ycoord R a)
    (hn : let q := 1+b; let Y := s*q^3; let c := eta+Y*(eta+zeta);
      f*f=1+delta a*(i*c*c)*(i*c*c))
    (hux : let q := 1+b; let Y := s*q^3; let c := eta+Y*(eta+zeta);
      let I := delta a*i*c*c; xcoord R (I-2)=I*u)
    (he : let q := 1+b; let Y := s*q^3; let c := eta+Y*(eta+zeta);
      f*f*c*T=u+c+f*f*R) :
    let q := 1+b; let Y := s*q^3; b*(Y*(q*q))*(q*q-1)<T := by
  let q := 1+b
  let Y := s*q^3
  let c := eta+Y*(eta+zeta)
  have hq : (1:V)≤q := by dsimp [q]; exact le_add_of_nonneg_right (by simp)
  have hb : b≤q := by dsimp [q]; exact le_add_of_nonneg_left (by simp)
  have ⟨hq3,hY⟩ := outer_seed_lower_bounds q s eta zeta hs heta hzeta
  exact seed_relations_exceed_shift a R b q Y c f i T u hR hc hi hf hq hb hY hq3 hn hux he
end DiophantineConsistency.AdaptiveGap85ThresholdFullSeed
