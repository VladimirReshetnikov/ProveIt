import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstFactor2011

/-! Small scalar identities for the concrete first-carrier binding. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstScalar2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Reassociate the old first norm to the literal graph's linear coefficient. -/
theorem first_norm_scalar (X Y k tau : V)
    (hn : tau*tau=1+(X*Y*Y)*((X*Y*Y)+1)*k*k) :
    tau*tau=1+((X*Y)*(Y*k))*(((X*Y)*(Y*k))+k) := by
  rw [hn]
  ring

/-- Reassociate the first-carrier identity without unfolding any rank or
radix definitions. -/
theorem first_carrier_scalar (q X Y k s r tau b : V) (hY : Y=s*q^3)
    (hc : (q^3*(q-1))*((X*Y*Y)*k+k+r)+(q^3*s)*(q-1) =
      (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*b)) :
    let ell := (X*Y)*(Y*k)
    let M := q*(q*q)*(q-1)
    let W := 1+k*(q-1)
    M*(ell+k+r)+Y*(q-1)=M*tau+W*(q*(q*q))*((q-1)*b) := by
  dsimp only
  rw [hY] at hc ⊢
  convert hc using 1 <;> ring
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstScalar2011
