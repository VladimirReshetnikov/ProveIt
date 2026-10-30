import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstData2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionWitnessProjection2011

/-! Project the actual first-carrier data onto the concrete 13-vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstInputProjected2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierRadix2011 ArithmeticAdaptiveScaledNorms2011
  ArithmeticAdaptiveConstructionWitness2011 ArithmeticAdaptiveConstructionFirstData2011
  ArithmeticAdaptiveConstructionWitnessProjection2011 ArithmeticAdaptivePortValues2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two literal first-factor input equalities follow from the already
extracted actual-vector data, for any other witness coordinates. -/
theorem first_input_of_data (v : Fin 14 → V) (r aux gamma : V) (hdata : FirstData v r) :
    let x := witness v r aux gamma
    let qv := ArithmeticCarrierRadix2011.q v
    let tau := qv*v 8*(v 7*qv^3)*v 9+(v 10+v 11)-rank v
    (let b : V := x 0*(currentPorts 0:V)
     let q := 1+b
     let Q := q*(q*q)
     let k := x 9+x 10
     let ell := (x 6*x 7)*(x 7*k)
     let M := Q*b
     let W := 1+k*b
     let A := x 6+(currentPorts 1:V)*q
     let Bp := q*A
     let Bn := (x 1+x 2)*A+x 1*q
     M*(ell+k+x 8)+x 7*b+Bn*(W*Q)=Bp*(W*Q)+M*tau) ∧
    (let k := x 9+x 10
     let ell := (x 6*x 7)*(x 7*k)
     tau*tau=1+ell*(ell+k)) := by
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let k := v 10+v 11
  let ell := (X*Y)*(Y*k)
  let tau := X*Y*v 9+k-rank v
  let A := X+(CurrentKernel2011.K:V)*q
  let Bp := q*A
  let Bn := (v 1+v 2)*A+v 1*q
  let M := q*(q*q)*(q-1)
  let W := 1+k*(q-1)
  obtain ⟨hcut,hnorm⟩ := hdata
  change M*(ell+k+r)+Y*(q-1)+Bn*(W*(q*(q*q))) = Bp*(W*(q*(q*q)))+M*tau at hcut
  change tau*tau=1+ell*(ell+k) at hnorm
  have hq1 : 1+v 0*(CurrentMasks2011.beta:V)=q := by
    change 1+v 0*(CurrentMasks2011.beta:V)=(CurrentMasks2011.beta:V)*v 0+1
    ring
  have hqm : q-1=v 0*(CurrentMasks2011.beta:V) := by rw [←hq1]; simp
  simp only [witness_zero,witness_one,witness_two,witness_six,witness_seven,
    witness_eight,witness_nine,witness_ten,port0_cast,port1_cast]
  rw [hq1,←hqm]
  exact ⟨hcut,hnorm⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstInputProjected2011
