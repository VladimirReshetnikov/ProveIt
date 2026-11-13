import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Whole-product projection without cancelling an arbitrary factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80ProjectionProduct
variable {R : Type*} [CommRing R]

theorem entire_product (a c d t X b z : R)
    (hd : d=t+a*c+(4*a+3)*z)
    (hnorm : d*d=1+(a*a+(4*a+3))*c*c)
    (hdiv : (4*a+3) ∣ b*((4*a+3)*X*c-2*(X*X+2*a*X*c-1))) :
    (4*a+3) ∣ b*(X-t)*(t*X+1) := by
  let H : R := 4*a+3
  let K : R := X*X+2*a*X*c-1
  change H ∣ b*(H*X*c-2*K) at hdiv
  obtain ⟨u,hu⟩ := hdiv
  have htwo : 2*(b*K)=H*(b*X*c-u) := by linear_combination -hu
  have hK : H ∣ b*K := by
    refine ⟨b*K-(2*a+1)*(b*X*c-u),?_⟩
    calc
      b*K=H*(b*K)-(2*a+1)*(2*(b*K)) := by dsimp [H]; ring
      _=H*(b*K)-(2*a+1)*(H*(b*X*c-u)) := by rw [htwo]
      _=H*(b*K-(2*a+1)*(b*X*c-u)) := by ring
  have hnormdiv : H ∣ t*t+2*t*a*c-1 := by
    refine ⟨c*c-2*z*(t+a*c)-H*z*z,?_⟩
    change d*d=1+(a*a+H)*c*c at hnorm
    change d=t+a*c+H*z at hd
    rw [hd] at hnorm
    linear_combination hnorm
  obtain ⟨k,hk⟩ := hK
  obtain ⟨s,hs⟩ := hnormdiv
  refine ⟨t*k-b*X*s,?_⟩
  calc
    b*(X-t)*(t*X+1)=t*(b*K)-b*X*(t*t+2*t*a*c-1) := by dsimp [K]; ring
    _=t*(H*k)-b*X*(H*s) := by rw [hk,hs]
    _=H*(t*k-b*X*s) := by ring

#print axioms Direct80ProjectionProduct.entire_product
end Direct80ProjectionProduct
