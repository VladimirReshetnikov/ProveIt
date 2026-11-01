import DiophantineConsistency.AdaptiveGap85ThresholdFullSeed
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! The auxiliary seed can be chosen with the gap-shift T threshold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThresholdAuxiliarySeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence AdaptiveGap85ThresholdFullSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual auxiliary-seed constructor produces the phase, norm, quotient,
    and literal equations together with the explicit gap-shift threshold. -/
theorem auxiliary_seed_with_shift_threshold (a R b s eta zeta : V)
    (hR : 5≤R) (hphase : R%4=3) (hs : 0<s) (heta : 0<eta) (hzeta : 0<zeta)
    (hc : let q := 1+b; let Y := s*q^3; eta+Y*(eta+zeta)=ycoord R a) :
    ∃ f i T u y : V, 0<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y ∧
      (let c := ycoord R a; f*f=1+delta a*(i*c*c)*(i*c*c)) ∧
      (let c := ycoord R a; let I := delta a*i*c*c; y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u) ∧
      f*f*(ycoord R a)*T=u+(ycoord R a)+f*f*R ∧
      (let q := 1+b; let Y := s*q^3; b*(Y*(q*q))*(q*q-1)<T) := by
  obtain ⟨f,i,T,u,y,hf,hi,hT,hu,hy,_,_,hn,hye,hux,_,_,_,he,_,_⟩ :=
    ArithmeticPellAuxiliarySeed.auxiliary_seed a R hphase
  have hthreshold := full_seed_exceeds_shift a R b s eta zeta f i T u hR hs heta hzeta hi hf hc
    (by simpa only [hc] using hn) (by simpa only [hc] using hux) (by simpa only [hc] using he)
  exact ⟨f,i,T,u,y,hf,hi,hT,hu,hy,hn,⟨hye,hux⟩,he,hthreshold⟩
end DiophantineConsistency.AdaptiveGap85ThresholdAuxiliarySeed
