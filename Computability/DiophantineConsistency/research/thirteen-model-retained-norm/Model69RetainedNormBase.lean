import Model69ViewMap

/-! Experimental transfer of the two retained natural norms into the
model difference ring. The actual-zero caller is not yet provided. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69RetainedNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open Model69ViewMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_norm (E N k Y R : V) (hR : R≤E*N+k)
    (hn : (E*N+k-R)*(E*N+k-R)=1+(E*Y)*(E*Y+1)*k*k) :
    ((ι E * ι N + ι k - ι R : DiffRing V)^2 -
      (ι E * ι k * ι Y) * (ι E * ι k * ι Y + ι k)) = 1 := by
  have h := congrArg (ι : V → DiffRing V) hn
  simp only [map_add, map_mul, map_one, map_sub_of_le _ _ hR] at h
  linear_combination h

theorem main_norm (a c d : V)
    (hn : d*d=1+(a+1)*(a+3)*c*c) :
    (ι d : DiffRing V)^2 - ((ι a)^2+(4*ι a+3))*(ι c)^2 = 1 := by
  have h := congrArg (ι : V → DiffRing V) hn
  simp only [map_add, map_mul, map_one, map_ofNat] at h
  linear_combination h

end Model69RetainedNorm
#print axioms Model69RetainedNorm.first_norm
#print axioms Model69RetainedNorm.main_norm
