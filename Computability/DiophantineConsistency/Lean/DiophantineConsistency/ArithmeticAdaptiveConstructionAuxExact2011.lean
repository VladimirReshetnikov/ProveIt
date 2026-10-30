import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxClient2011

/-! The chosen auxiliary seed has a nonnegative signed adaptive V. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionAuxExact2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The seed's exact linear identity makes both truncated differences exact;
this is the missing orientation needed to use the adaptive auxiliary root. -/
theorem auxiliary_cut_exact (f c T R a u y Q : V)
    (hf : 0<f) (hlit : f*f*c*T=a+c+f*f*R)
    (hu : u+a=y)
    (hnorm : Q*a*a+y*y=1+Q*y*y) :
    let v := f*f*(c*T-R)-c
    R≤c*T ∧ v=a ∧ (v+u)*(v+u)+Q*v*v=1+Q*(v+u)*(v+u) := by
  have hf2 : 0<f*f := mul_pos hf hf
  have hle : f*f*R≤f*f*(c*T) := by
    rw [show f*f*(c*T)=f*f*c*T by ring, hlit]
    exact le_add_of_nonneg_left (by simp)
  have hcT : R≤c*T := le_of_mul_le_mul_left hle hf2
  have hv : f*f*(c*T-R)-c=a := by
    rw [mul_tsub, show f*f*(c*T)=a+c+f*f*R by rw [← hlit]; ring]
    simp
  dsimp only
  refine ⟨hcT,hv,?_⟩
  rw [hv,show a+u=y by rw [add_comm,hu]]
  calc y*y+Q*a*a=Q*a*a+y*y := by ring
       _=1+Q*y*y := hnorm
end DiophantineConsistency.ArithmeticAdaptiveConstructionAuxExact2011
