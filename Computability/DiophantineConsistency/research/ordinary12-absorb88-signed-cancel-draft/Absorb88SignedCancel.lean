import DiophantineConsistency.ArithmeticAdaptiveFactorThree2011
import DiophantineConsistency.ModelDifferenceRing

/-! Draft: lift natural divisibility and cancel the factor-three carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88SignedCancel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticAdaptiveFactorThree2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem natural_of_embedded_dvd (a t : V)
    (h : (ι a : DiffRing V) ∣ ι t) : a ∣ t := by
  obtain ⟨z,hz⟩ := h
  rcases nonneg_or_nonpos z with ⟨u,hu⟩ | ⟨u,hu⟩
  · refine ⟨u,?_⟩
    apply ι_injective
    rw [map_mul,←hu]
    exact hz
  · have ht0 : (ι t : DiffRing V)=0 := by
      have ht := ι_nonneg t
      have hp := mul_nonneg (ι_nonneg a) (ι_nonneg u)
      rw [hu] at hz
      nlinarith
    have ht0' : t=0 := ι_injective (by simpa using ht0)
    rw [ht0']
    exact dvd_zero _

theorem cancel_signed (q Y X : V) (x : DiffRing V)
    (hq : 0<q) (hy : q^3∣Y)
    (h : (ι (q^5) : DiffRing V) ∣ ι (3+4*Y*(X+1))*x) :
    (ι (q^4) : DiffRing V) ∣ x := by
  rcases nonneg_or_nonpos x with ⟨t,ht⟩ | ⟨t,ht⟩
  · have hd : q^5∣(3+4*Y*(X+1))*t := by
      apply natural_of_embedded_dvd
      rw [ht] at h
      simpa only [map_mul] using h
    obtain ⟨u,hu⟩ := cancel_factor_three q Y X t hq hy hd
    refine ⟨ι u,?_⟩
    rw [ht,hu,map_mul]
  · have hd : q^5∣(3+4*Y*(X+1))*t := by
      apply natural_of_embedded_dvd
      rw [ht] at h
      have hn : (ι (q^5) : DiffRing V) ∣ -(ι ((3+4*Y*(X+1))*t)) := by
        simpa only [map_mul,mul_neg] using h
      exact dvd_neg.mp hn
    obtain ⟨u,hu⟩ := cancel_factor_three q Y X t hq hy hd
    refine ⟨-ι u,?_⟩
    rw [ht,hu,map_mul,mul_neg]

#print axioms Absorb88SignedCancel.natural_of_embedded_dvd
#print axioms Absorb88SignedCancel.cancel_signed
end Absorb88SignedCancel
