import DiophantineConsistency.BFS943.Direct80ProjectionProduct

/-! Once X is the projected power, the projection divisor is unweighted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80UnweightedProjection
variable {R : Type*} [CommRing R]

theorem unweighted (a c d X z : R)
    (hd : d=X+a*c+(4*a+3)*z)
    (hnorm : d*d=1+(a*a+(4*a+3))*c*c) :
    (4*a+3) ∣ (4*a+3)*X*c-2*(X*X+2*a*X*c-1) := by
  let H : R := 4*a+3
  have hnormdiv : H ∣ X*X+2*X*a*c-1 := by
    refine ⟨c*c-2*z*(X+a*c)-H*z*z,?_⟩
    change d*d=1+(a*a+H)*c*c at hnorm
    change d=X+a*c+H*z at hd
    calc
      X*X+2*X*a*c-1=(d*d-1-a*a*c*c)-H*(2*z*(X+a*c)+H*z*z) := by rw [hd]; ring
      _=H*(c*c)-H*(2*z*(X+a*c)+H*z*z) := by rw [hnorm]; ring
      _=H*(c*c-2*z*(X+a*c)-H*z*z) := by ring
  obtain ⟨s,hs⟩ := hnormdiv
  change H∣H*X*c-2*(X*X+2*a*X*c-1)
  refine ⟨X*c-2*s,?_⟩
  calc
    H*X*c-2*(X*X+2*a*X*c-1)=H*X*c-2*(X*X+2*X*a*c-1) := by ring
    _=H*X*c-2*(H*s) := by rw [hs]
    _=H*(X*c-2*s) := by ring

#print axioms Direct80UnweightedProjection.unweighted
end Direct80UnweightedProjection
