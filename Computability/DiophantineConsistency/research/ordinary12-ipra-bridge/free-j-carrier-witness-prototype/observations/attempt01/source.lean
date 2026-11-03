import FreeJOrdinaryTailWitness
import FreeJCompletenessFactorBridge

/-! Assemble the actual free-J zero from its Pell-type carrier witnesses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJCarrierWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ Ordinary12Patterns
open FreeJOrdinaryTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem factor_unit {σ : Type*} (e : Expr σ) (v : σ → V)
    (h : e.evalRing (fun j => ι (v j)) = 1) :
    (pairEval e v).1 = (pairEval e v).2+1 := by
  have hz : InternalZero (e-1) v := by
    apply (internalZero_iff (e-1) v).mpr
    simp only [Expr.evalRing_sub, Expr.evalRing_ofNat, h, sub_self]
  simpa [pairEval, Expr.splitNatural, NatExpr.evalSemiring, InternalZero] using hz

/-- The first and main carriers hold for their exact graph expressions when
suitable first- and main-Pell witnesses satisfy these ring equations. -/
theorem carrier_units (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (τ χ : DiffRing V)
    (hZ : let qm := (core p).qm.evalRing (fun j => ι (v j))
      let q := 1+qm
      (core p).z.evalRing (fun j => ι (v j)) = q*(q*q)*qm*τ)
    (hτ : τ*τ = (core p).n.evalRing (fun j => ι (v j)))
    (hD : (core p).d.evalRing (fun j => ι (v j)) =
      (core p).u.evalRing (fun j => ι (v j))*χ)
    (hχ : let a := (core p).a.evalRing (fun j => ι (v j))
      let c := (core p).c.evalRing (fun j => ι (v j))
      χ*χ = 1+(3+4*a+a*a)*(c*c)) :
    (pairEval (core p).first v).1 = (pairEval (core p).first v).2+1 ∧
    (pairEval (core p).main v).1 = (pairEval (core p).main v).2+1 := by
  constructor
  · apply factor_unit
    rw [first_eq]
    simp only [firstPattern, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
      Expr.evalRing_ofNat]
    dsimp only at hZ
    rw [hZ]
    calc
      _ = 1 + ((1+(core p).qm.evalRing (fun j => ι (v j))) *
        ((1+(core p).qm.evalRing (fun j => ι (v j)))*
        (1+(core p).qm.evalRing (fun j => ι (v j)))) *
        (core p).qm.evalRing (fun j => ι (v j)))^2 *
        (τ*τ-(core p).n.evalRing (fun j => ι (v j))) := by ring
      _ = 1 := by rw [hτ]; ring
  · apply factor_unit
    rw [main_eq]
    simp only [mainPattern, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
      Expr.evalRing_ofNat]
    dsimp only at hχ
    rw [hD]
    calc
      _ = 1 + ((core p).u.evalRing (fun j => ι (v j)))^2 *
        (χ*χ-(1+(3+4*(core p).a.evalRing (fun j => ι (v j))+
          (core p).a.evalRing (fun j => ι (v j))*(core p).a.evalRing (fun j => ι (v j)))*
          ((core p).c.evalRing (fun j => ι (v j))*(core p).c.evalRing (fun j => ι (v j))))) := by ring
      _ = 1 := by rw [hχ]; ring

#print axioms FreeJCarrierWitness.carrier_units
end FreeJCarrierWitness
