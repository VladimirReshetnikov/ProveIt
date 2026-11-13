import DiophantineConsistency.Compact44.DirectMainProjection

/-! Conditional orientation of a positive direct main root in every IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectMainNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticAdaptiveQuotients2011 ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticSignedPairs DirectMainProjection
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An oriented signed pair whose square has the stated positive-scale norm
has a positive natural quotient and an exact oriented balance. -/
theorem oriented_scaled_norm (U P N C : V) (hU : 0<U) (hPN : N<P)
    (hnorm : magnitude (P,N)*magnitude (P,N)=U*U*(1+C)) :
    ∃ m : V, 0<m ∧ P=N+U*m ∧ m*m=1+C := by
  obtain ⟨m,hm,hn⟩ := scaled_quotient U (magnitude (P,N)) (1+C) hU hnorm
  have hmpos : 0<m := pos_of_mul_pos_left (by rw [hn]; simp) (by simp)
  have he : P=N+(P-N) := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hPN)]
  have hmag : magnitude (P,N)=P-N := magnitude_of_add he
  refine ⟨m,hmpos,?_,hn⟩
  rw [he, ←hmag, hm]

/-- The same oriented quotient for the direct U*G positive part. The norm
hypothesis is explicit; the lemma does not prove it for a polynomial graph. -/
theorem direct_main_orientation (U X Y k eta G R : V)
    (hU : 0<U) (hY : 8≤Y) (hk : 0<k)
    (hnorm :
      let a := X*Y+Y
      let c := eta+Y*k
      let H := 3+4*a
      let P := U*(X+a*c)+H*(U*G+R+1)
      let N := H*k
      magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))) :
    let a := X*Y+Y
    let c := eta+Y*k
    let H := 3+4*a
    let P := U*(X+a*c)+H*(U*G+R+1)
    let N := H*k
    ∃ m : V, 0<m ∧ P=N+U*m ∧ m*m=1+(H+a*a)*(c*c) := by
  exact oriented_scaled_norm _ _ _ _ hU (direct_parts_positive U X Y k eta G R hU hY hk) hnorm

#print axioms DirectMainNorm.oriented_scaled_norm
#print axioms DirectMainNorm.direct_main_orientation
end DirectMainNorm
