import DiophantineConsistency.ArithmeticAdaptiveConstructionWitness2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstData2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstActual2011

/-! Bind the actual first factor to the concrete witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstWitness2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticOuterSeed
  ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFactorMagnitude2011
  ArithmeticAdaptiveConstructionWitness2011 ArithmeticAdaptiveConstructionFirstFactor2011
  ArithmeticAdaptiveConstructionFirstData2011
  ArithmeticAdaptiveConstructionFirstActual2011 ArithmeticAdaptiveConstructionTransport2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The common old vector and outer seed yield a positive r making the
concrete witness's actual literal first factor a positive unit. -/
theorem witness_first_unit (v : Fin 14 → V) (u aux gamma : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hphase : rank v%4=3)
    (hq : ArithmeticCarrierRadix2011.q v=Exp.exp u)
    (hX : Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8)
    (hR : 2*u≤rank v)
    (hseed : SeedRelations u (rank v) (v 7) (v 9) (v 10) (v 11) (v 13)) :
    ∃ r : V, 0<r ∧
      (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).1 (witness v r aux gamma)).1 =
        (ArithmeticAdaptiveFactorMagnitude2011.pairEval (factors CurrentWindowCarry2011.ports).1 (witness v r aux gamma)).2+1 := by
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let k := v 10+v 11
  let ell := (X*Y)*(Y*k)
  let R := rank v
  let tau := X*Y*v 9+k-R
  let A := X+(CurrentKernel2011.K:V)*q
  let Bp := q*A
  let Bn := (v 1+v 2)*A+v 1*q
  let M := q*(q*q)*(q-1)
  let W := 1+k*(q-1)
  obtain ⟨r,hr,hcut,hnorm⟩ := actual_first_data v u hv he hphase hq hX hR hseed
  change M*(ell+k+r)+Y*(q-1)+Bn*(W*(q*(q*q))) = Bp*(W*(q*(q*q)))+M*tau at hcut
  change tau*tau=1+ell*(ell+k) at hnorm
  have hq1 : 1+v 0*(CurrentMasks2011.beta:V)=q := by
    change 1+v 0*(CurrentMasks2011.beta:V)=(CurrentMasks2011.beta:V)*v 0+1
    ring
  have hqm : q-1=v 0*(CurrentMasks2011.beta:V) := by rw [←hq1]; simp
  refine ⟨r,hr,?_⟩
  rw [←currentPorts_cast]
  apply first_factor_of_additive currentPorts (witness v r aux gamma) tau
  · change let q' := 1+v 0*(CurrentMasks2011.beta:V)
      (q'*(q'*q')*(v 0*(CurrentMasks2011.beta:V)))*(ell+k+r)+Y*(v 0*(CurrentMasks2011.beta:V))+
      ((v 1+v 2)*(X+(CurrentKernel2011.K:V)*q')+v 1*q')*
        ((1+k*(v 0*(CurrentMasks2011.beta:V)))*(q'*(q'*q'))) =
      (q'*(X+(CurrentKernel2011.K:V)*q'))*((1+k*(v 0*(CurrentMasks2011.beta:V)))*(q'*(q'*q')))+
        (q'*(q'*q')*(v 0*(CurrentMasks2011.beta:V)))*tau
    dsimp only
    rw [hq1,←hqm]
    exact hcut
  · change tau*tau=1+((X*Y)*(Y*k))*(((X*Y)*(Y*k))+k)
    exact hnorm
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstWitness2011
