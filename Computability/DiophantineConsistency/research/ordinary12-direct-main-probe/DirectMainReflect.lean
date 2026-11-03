import DirectMainPlusBranch

/-! Conditional reflection of the negative first-root sign. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainReflect
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency DirectMainPlusBranch
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A negative signed root can be reflected by adding `2*first` to r.
The new r is above s and realizes the positive root. -/
theorem negative_reflection (b ell k Bt r first s : V)
    (hs : s≤ell) (hk : k≤ell) (hn : first*first=1+ell*(ell+k))
    (hneg : b*(ell+k+r)+b*first=(1+k*b)*Bt) :
    ∃ rnew : V, s<rnew ∧ b*(ell+k+rnew)=(1+k*b)*Bt+b*first := by
  have hthird := root_thirds ell k first hk hn
  have hscale : 3*ell<3*first := lt_of_le_of_lt (by simp) hthird
  have hroot : ell<first := lt_of_mul_lt_mul_left hscale (by simp)
  have hsfirst : s<first := lt_of_le_of_lt hs hroot
  refine ⟨r+2*first,?_,?_⟩
  · apply lt_of_lt_of_le hsfirst
    calc
      first≤first+first := by simp
      _≤r+(first+first) := by simp
      _=r+2*first := by ring
  · calc
      b*(ell+k+(r+2*first))=(b*(ell+k+r)+b*first)+b*first := by ring
      _=(1+k*b)*Bt+b*first := by rw [hneg]

/-- Reflection preserves the first squared residual in any commutative ring. -/
theorem reflect_square {R : Type*} [CommRing R] (b E A r first : R)
    (hneg : b*(E+r)-A= -(b*first)) :
    (b*(E+(r+2*first))-A)^2=(b*(E+r)-A)^2 := by
  have hnew : b*(E+(r+2*first))-A = (b*(E+r)-A)+2*(b*first) := by ring
  rw [hnew,hneg]
  ring

#print axioms DirectMainReflect.negative_reflection
#print axioms DirectMainReflect.reflect_square
end DirectMainReflect
