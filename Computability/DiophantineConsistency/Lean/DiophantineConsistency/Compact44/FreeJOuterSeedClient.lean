import DiophantineConsistency.ArithmeticOuterSeed
import DiophantineConsistency.Compact44.FreeJSeedSquareBridge

/-! Connect the model outer Pell seed to the exact free-J carrier factors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJOuterSeedClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ ArithmeticOuterSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def seedTau (u R s n eta zeta : V) : V :=
  let X := Exp.exp R
  let Y := s*Exp.exp u^3
  X*Y*n+(eta+zeta)-R

def seedChi (u R s eta zeta gamma : V) : V :=
  let X := Exp.exp R
  let Y := s*Exp.exp u^3
  let a := X*Y+Y
  let c := (eta+zeta)*Y+eta
  X+a*c+gamma*(4*a+3)

private theorem a_shape (p : Fin 4 → ℤ) : (core p).a =
    ((.var 5)*(.var 6))+(.var 6) := by rfl
private theorem c_shape (p : Fin 4 → ℤ) : (core p).c =
    (.var 8)+(.var 6)*((.var 8)+(.var 9)) := by rfl

/-- The actual outer seed supplies the exact free-J carrier squares. The
coordinate, transport and adaptive-lift equations remain explicit. -/
theorem carrier_units_of_outer_seed (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (u R s n eta zeta gamma : V)
    (hseed : SeedRelations u R s n eta zeta gamma)
    (hX : v 5 = Exp.exp R) (hY : v 6 = s*Exp.exp u^3)
    (heta : v 8 = eta) (hzeta : v 9 = zeta)
    (hZ : let qm := (core p).qm.evalRing (fun j => ι (v j))
      let q := 1+qm
      (core p).z.evalRing (fun j => ι (v j)) =
        q*(q*q)*qm*ι (seedTau u R s n eta zeta))
    (hD : (core p).d.evalRing (fun j => ι (v j)) =
      (core p).u.evalRing (fun j => ι (v j))*ι (seedChi u R s eta zeta gamma)) :
    (pairEval (core p).first v).1 = (pairEval (core p).first v).2+1 ∧
    (pairEval (core p).main v).1 = (pairEval (core p).main v).2+1 := by
  apply FreeJSeedSquareBridge.carrier_units_of_seed_squares p v
    (ι (seedTau u R s n eta zeta)) (ι (seedChi u R s eta zeta gamma)) hZ hD
  · have ht := hseed.1
    dsimp only at ht ⊢
    have hm := congrArg (fun x : V => ι x) ht
    simp only [map_add, map_mul, map_one, map_pow] at hm
    rw [hX,hY,heta,hzeta]
    simpa only [seedTau, map_add, map_mul, map_one, map_pow] using hm
  · have ht := hseed.2.1
    dsimp only at ht ⊢
    have hm := congrArg (fun x : V => ι x) ht
    simp only [map_add, map_mul, map_one, map_ofNat, map_pow] at hm
    rw [a_shape,c_shape]
    simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var]
    rw [hX,hY,heta,hzeta]
    simp only [seedChi, map_add, map_mul, map_ofNat, map_pow]
    convert hm using 1; ring

#print axioms FreeJOuterSeedClient.carrier_units_of_outer_seed
end FreeJOuterSeedClient
