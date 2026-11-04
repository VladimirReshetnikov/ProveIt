import DiophantineConsistency.Compact44.FreeJCarrierWitness

/-! Bridge the outer seed's norm squares to exact free-J graph carriers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJSeedSquareBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem first_norm_shape (p : Fin 4 → ℤ) :
    (core p).n =
      let X : Expr (Fin 12) := .var 5
      let Y : Expr (Fin 12) := .var 6
      let k : Expr (Fin 12) := .var 8 + .var 9
      let ell := (X*Y)*(Y*k)
      1+ell*(ell+k) := by rfl

/-- Outer seed square identities, together with graph transport and adaptive
lift, suffice for both exact free-J carrier factors. -/
theorem carrier_units_of_seed_squares (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (τ χ : DiffRing V)
    (hZ : let qm := (core p).qm.evalRing (fun j => ι (v j))
      let q := 1+qm
      (core p).z.evalRing (fun j => ι (v j)) = q*(q*q)*qm*τ)
    (hD : (core p).d.evalRing (fun j => ι (v j)) =
      (core p).u.evalRing (fun j => ι (v j))*χ)
    (hfirst : let X := ι (v 5)
      let Y := ι (v 6)
      let k := ι (v 8)+ι (v 9)
      τ*τ = 1+(X*Y*Y)*(X*Y*Y+1)*k*k)
    (hmain : let a := (core p).a.evalRing (fun j => ι (v j))
      let c := (core p).c.evalRing (fun j => ι (v j))
      χ*χ = 1+(a+1)*(a+3)*c*c) :
    (pairEval (core p).first v).1 = (pairEval (core p).first v).2+1 ∧
    (pairEval (core p).main v).1 = (pairEval (core p).main v).2+1 := by
  apply FreeJCarrierWitness.carrier_units p v τ χ hZ ?_ hD ?_
  · rw [hfirst,first_norm_shape]
    simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_ofNat]
    ring
  · dsimp only at hmain ⊢
    rw [hmain]
    ring

#print axioms FreeJSeedSquareBridge.carrier_units_of_seed_squares
end FreeJSeedSquareBridge
