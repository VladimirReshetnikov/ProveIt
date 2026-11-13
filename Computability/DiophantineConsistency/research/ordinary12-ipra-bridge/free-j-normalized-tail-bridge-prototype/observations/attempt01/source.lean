import FreeJOrdinaryTailWitness

/-! Bridge normalized strong/auxiliary seed equations to the exact ordinary tail. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJNormalizedTailBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ
open FreeJOrdinaryTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A normalized strong Pell seed and its auxiliary seed suffice for the
actual ordinary graph factor, with ordinary multiplier `Δ*i`. All graph
bindings are explicit; the seed and the graph valuation are not constructed. -/
theorem ordinary_unit_of_normalized_seed (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (Δ c f i y : DiffRing V)
    (hq : (parts p).q.evalRing (fun j => ι (v j)) = Δ*(f*f-1))
    (hd : (parts p).d.evalRing (fun j => ι (v j)) = (c*c)*(c*c))
    (hn : (parts p).n.evalRing (fun j => ι (v j)) =
      Δ*i+(y-(parts p).z.evalRing (fun j => ι (v j))))
    (hstrong : f*f=1+Δ*(i*c*c)*(i*c*c))
    (haux : let z := (parts p).z.evalRing (fun j => ι (v j))
      (Δ*i*c*c)*(Δ*i*c*c)*z*z+y*y =
        1+(Δ*i*c*c)*(Δ*i*c*c)*y*y) :
    (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2+1 := by
  apply FreeJOrdinaryTailWitness.ordinary_unit_of_witnesses p v (Δ*i)
    (y-(parts p).z.evalRing (fun j => ι (v j)))
  · rw [hq,hd,hstrong]
    ring
  · exact hn
  · dsimp only at haux ⊢
    rw [hq,hstrong]
    linear_combination haux

#print axioms FreeJNormalizedTailBridge.ordinary_unit_of_normalized_seed
end FreeJNormalizedTailBridge
