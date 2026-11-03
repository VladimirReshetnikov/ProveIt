import FreeJCarrierWitness

/-! Assemble the exact free-J literal from explicit Pell-type witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJWitnessAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ
open FreeJOrdinaryTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Explicit sufficient conditions for an actual free-J graph zero. The four
auxiliary elements are in the model difference ring; no existence or
coordinate-positivity is asserted. -/
theorem zero_of_witnesses (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (τ χ i u : DiffRing V)
    (hZ : let qm := (core p).qm.evalRing (fun j => ι (v j))
      let q := 1+qm
      (core p).z.evalRing (fun j => ι (v j)) = q*(q*q)*qm*τ)
    (hτ : τ*τ = (core p).n.evalRing (fun j => ι (v j)))
    (hD : (core p).d.evalRing (fun j => ι (v j)) =
      (core p).u.evalRing (fun j => ι (v j))*χ)
    (hχ : let a := (core p).a.evalRing (fun j => ι (v j))
      let c := (core p).c.evalRing (fun j => ι (v j))
      χ*χ = 1+(3+4*a+a*a)*(c*c))
    (hq : (parts p).q.evalRing (fun j => ι (v j)) =
      (parts p).d.evalRing (fun j => ι (v j))*i*i)
    (hn : (parts p).n.evalRing (fun j => ι (v j)) = i+u)
    (hu : let q := (parts p).q.evalRing (fun j => ι (v j))
      let z := (parts p).z.evalRing (fun j => ι (v j))
      (1-q)*(z+u)*(z+u)+q*z*z-1 = 0) :
    InternalZero (literal p) v := by
  obtain ⟨hfirst, hmain⟩ := FreeJCarrierWitness.carrier_units p v τ χ hZ hτ hD hχ
  have htail := FreeJOrdinaryTailWitness.ordinary_unit_of_witnesses p v i u hq hn hu
  exact FreeJCompletenessFactorBridge.zero_of_factor_units p v hfirst hmain htail

#print axioms FreeJWitnessAssembly.zero_of_witnesses
end FreeJWitnessAssembly
