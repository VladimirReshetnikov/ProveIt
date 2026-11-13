import FreeJSignedTransport

/-! Construct the ordinary factor from its two exact Pell-type equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJOrdinaryTailWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ
open FreeJNormZero FreeJOrdinaryTransport

/-- Exact polynomial factorization used in the ordinary-tail construction. -/
theorem factor_identity {R : Type*} [CommRing R] (d i z u : R) :
    let q := d*i*i
    let r := 1-q
    let h := fun x => r*(z+x)*(z+x)+q*z*z-1
    let a := d*h (i+u)-q*r
    a*a+4*d*q*r*(q*z*z-1) = d*d*h u*h (u+2*i) := by
  dsimp only
  ring

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- If graph-evaluated q and n admit the specified ordinary strong and
auxiliary witnesses in the model difference ring, the actual ordinary factor
represents +1. No positivity or existence of those witnesses is asserted. -/
theorem ordinary_unit_of_witnesses (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (i u : DiffRing V)
    (hq : (parts p).q.evalRing (fun j => ι (v j)) =
      (parts p).d.evalRing (fun j => ι (v j))*i*i)
    (hn : (parts p).n.evalRing (fun j => ι (v j)) = i+u)
    (hu : let q := (parts p).q.evalRing (fun j => ι (v j))
      let z := (parts p).z.evalRing (fun j => ι (v j))
      (1-q)*(z+u)*(z+u)+q*z*z-1 = 0) :
    (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2+1 := by
  have hzero : InternalZero (ordinaryResidual p) v := by
    apply (internalZero_iff (ordinaryResidual p) v).mpr
    rw [graph_residual_shape, polarized_eval]
    dsimp only at *
    rw [hq] at hu ⊢
    rw [hn]
    have hf := factor_identity ((parts p).d.evalRing (fun j => ι (v j))) i
      ((parts p).z.evalRing (fun j => ι (v j))) u
    dsimp only at hf
    rw [hu, mul_zero, zero_mul] at hf
    convert hf using 1 <;> ring
  rw [ordinary_shape]
  change (pairEval (Expr.add (Expr.constant 1) (ordinaryResidual p)) v).1 =
    (pairEval (Expr.add (Expr.constant 1) (ordinaryResidual p)) v).2+1
  simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,InternalZero,add_comm,add_left_comm,add_assoc] using hzero

#print axioms FreeJOrdinaryTailWitness.factor_identity
#print axioms FreeJOrdinaryTailWitness.ordinary_unit_of_witnesses
end FreeJOrdinaryTailWitness
