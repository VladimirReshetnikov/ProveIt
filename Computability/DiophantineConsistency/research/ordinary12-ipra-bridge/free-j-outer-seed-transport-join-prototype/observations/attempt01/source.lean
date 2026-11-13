import FreeJFirstTransportIdentity

/-! Join the model outer seed to both exact carrier transport identities. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJOuterSeedTransportJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ ArithmeticOuterSeed
open FreeJOuterSeedClient FreeJAdaptiveLift FreeJFirstTransportIdentity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem a_shape (p : Fin 4 → ℤ) : (core p).a =
    ((.var 5)*(.var 6))+(.var 6) := by rfl
private theorem c_shape (p : Fin 4 → ℤ) : (core p).c =
    (.var 8)+(.var 6)*((.var 8)+(.var 9)) := by rfl

/-- The outer seed and the two explicit transport/lift equations imply that
both exact graph carrier factors represent +1. -/
theorem carrier_units (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (u R s n eta zeta gamma : V) (w : DiffRing V)
    (hseed : SeedRelations u R s n eta zeta gamma)
    (hX : v 5 = Exp.exp R) (hY : v 6 = s*Exp.exp u^3)
    (heta : v 8 = eta) (hzeta : v 9 = zeta)
    (hw : ι (v 5) = (1+(core p).qm.evalRing (fun j => ι (v j)))*w)
    (hlift : (core p).u.evalRing (fun j => ι (v j))*ι (v 11) +
      (core p).u.evalRing (fun j => ι (v j))*w =
      (core p).u.evalRing (fun j => ι (v j))*ι gamma +
        (shiftExpr p).evalRing (fun j => ι (v j)))
    (htransport : let ev := fun e : Expr (Fin 12) => e.evalRing (fun j => ι (v j))
      let q := 1+ev (core p).qm
      let k := ι (v 8)+ι (v 9)
      ev (mExpr p)*(ev ellExpr+k+ι (v 7)) + ι (v 6)*ev (core p).qm =
        ev (mExpr p)*ι (seedTau u R s n eta zeta) +
          (1+ev (core p).qm*k)*(q*(q*q))*ev (btExpr p)) :
    (pairEval (core p).first v).1 = (pairEval (core p).first v).2+1 ∧
    (pairEval (core p).main v).1 = (pairEval (core p).main v).2+1 := by
  apply carrier_units_of_outer_seed p v u R s n eta zeta gamma hseed hX hY heta hzeta
  · have hz := graph_z_of_additive_transport p v (ι (seedTau u R s n eta zeta)) htransport
    dsimp only at hz ⊢
    simp only [mExpr, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_ofNat] at hz
    convert hz using 1 <;> ring
  · have h := main_lift_identity p v w (ι gamma) hw hlift
    have hc : ι (seedChi u R s eta zeta gamma) =
        ι (v 5)+(core p).a.evalRing (fun j => ι (v j))*
          (core p).c.evalRing (fun j => ι (v j))+
          ι gamma*(4*(core p).a.evalRing (fun j => ι (v j))+3) := by
      rw [a_shape,c_shape]
      simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_var]
      rw [hX,hY,heta,hzeta]
      simp only [seedChi,map_add,map_mul,map_ofNat,map_pow]
      ring
    rw [hc]
    exact h

#print axioms FreeJOuterSeedTransportJoin.carrier_units
end FreeJOuterSeedTransportJoin
