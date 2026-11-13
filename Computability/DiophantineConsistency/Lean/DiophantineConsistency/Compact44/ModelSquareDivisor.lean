import DiophantineConsistency.ArithmeticGcdNormalization

/-! Model-level square-divisor witness from a reduced norm. This result does
not establish an object-theory derivation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ModelSquareDivisor

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A four-natural Bézout certificate for `(a,b)` yields one for
`(a,b²)`, by squaring its signed interpretation. -/
theorem unit_certificate_square_right {a b : V} (h : Bez a b 1) :
    Bez a (b*b) 1 := by
  obtain ⟨u,v,w,z,he⟩ := h
  let L := a*u+b*v
  let R := a*w+b*z
  let U := a*(2*w*u)+2*b*(w*v+u*z)
  let W := a*(w*w+u*u)+2*b*(w*z+u*v)
  let Bneg := 2*z*v
  let Bpos := z*z+v*v
  have hR : (1:V)+L=R := by
    simpa only [L,R,add_assoc] using he
  have hsq : (1:V)+2*L*R=R*R+L*L := by
    rw [←hR]
    ring
  refine ⟨U,Bneg,W,Bpos,?_⟩
  calc
    (1:V)+a*U+(b*b)*Bneg = 1+2*L*R := by dsimp [U,Bneg,L,R]; ring
    _ = R*R+L*L := hsq
    _ = a*W+(b*b)*Bpos := by dsimp [W,Bpos,L,R]; ring

/-- The additive reduced norm and a supplied four-natural Bézout certificate
produce a natural square-divisor witness. No factor is assumed nonzero. -/
theorem square_divisor_of_reduced_norm {a b r t : V}
    (hu : Bez a b 1) (hnorm : t*(b*b)=r*(a*a)+(b*b)) :
    ∃ s : V, r=(b*b)*s := by
  have hu2 : Bez a (b*b) 1 := unit_certificate_square_right hu
  have hc : Bez (t*(b*b)) (b*b) (r*(a*a)) := by
    refine ⟨0,1,1,0,?_⟩
    simpa only [mul_zero,mul_one,zero_add,add_zero] using hnorm.symm
  have hdiv : (b*b) ∣ r*(a*a) :=
    bez_divisor hc ⟨t,by ring⟩ (dvd_refl (b*b))
  have hdiv' : (b*b) ∣ a*(a*r) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hdiv
  have hdiv'' : (b*b) ∣ a*r := unit_certificate_cancel hu2 hdiv'
  have hdiv''' : (b*b) ∣ r := unit_certificate_cancel hu2 hdiv''
  obtain ⟨s,hs⟩ := hdiv'''
  exact ⟨s,hs⟩

/-- The zero-denominator edge is included: the two hypotheses force `r=0`.
This is an application of the generic result, not an extra premise. -/
theorem zero_right_edge {a r t : V} (hu : Bez a (0:V) 1)
    (hnorm : t*((0:V)*0)=r*(a*a)+((0:V)*0)) : r=0 := by
  obtain ⟨s,hs⟩ := square_divisor_of_reduced_norm hu hnorm
  simpa using hs

end ModelSquareDivisor
#print axioms ModelSquareDivisor.unit_certificate_square_right
#print axioms ModelSquareDivisor.square_divisor_of_reduced_norm
#print axioms ModelSquareDivisor.zero_right_edge
