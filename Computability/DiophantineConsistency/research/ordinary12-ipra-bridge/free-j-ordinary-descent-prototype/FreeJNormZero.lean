import DiophantineConsistency.Ordinary12FreeJ
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJNormZero
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.Ordinary12FreeJ
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ordinaryResidual (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let d := core p
  d.pa*d.pa + (4*(d.pd*d.pt))*d.pc

theorem ordinary_shape (p : Fin 4 → ℤ) : (core p).ordinary = 1 + ordinaryResidual p := by rfl

theorem ordinary_residual_zero (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (hz : InternalZero (literal p) v) : InternalZero (ordinaryResidual p) v := by
  have hu := (literal_factor_units p v hz).2.2
  rw [ordinary_shape] at hu
  change (pairEval (Expr.add (Expr.constant 1) (ordinaryResidual p)) v).1 =
    (pairEval (Expr.add (Expr.constant 1) (ordinaryResidual p)) v).2+1 at hu
  simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,InternalZero,add_comm,add_left_comm,add_assoc] using hu

/-- Universal tail polarization and cleared auxiliary identity. These are
ring identities; no division or integrality is asserted. -/
theorem cleared_auxiliary_identity {R : Type*} [CommRing R] (q d V0 n : R) :
    let w := n+V0
    let p := 1-q
    let h := p*w*w+q*V0*V0-1
    let b := 2*p*w
    let A := d*h+q*p
    let N := A*A-d*q*b*b
    let D := d*b
    let Y := w*D-A
    q*V0*V0*D*D-(q-1)*Y*Y-D*D = -(q-1)*N := by
  dsimp only
  ring

theorem polarization_identity {R : Type*} [CommRing R] (q d V0 n : R) :
    let w := n+V0
    let p := 1-q
    let cy := q*V0*V0-1
    let h := p*w*w+cy
    (d*h+q*p)*(d*h+q*p)-d*q*(2*p*w)*(2*p*w) =
      (d*h-q*p)*(d*h-q*p)+4*d*q*p*cy := by
  dsimp only
  ring


/-- Cleared auxiliary identity in signed-pair semantics for every arithmetic
model. This does not divide by D or assert integrality. -/
theorem cleared_auxiliary_pairs (v : Fin 4 → V) :
    let q : Expr (Fin 4) := .var 0
    let d : Expr (Fin 4) := .var 1
    let z : Expr (Fin 4) := .var 2
    let n : Expr (Fin 4) := .var 3
    let w := Expr.add n z
    let p := Expr.sub (.constant 1) q
    let h := Expr.sub (.add (.mul (.mul p w) w) (.mul (.mul q z) z)) (.constant 1)
    let b := Expr.mul (.mul (.constant 2) p) w
    let A := Expr.add (.mul d h) (.mul q p)
    let N := Expr.sub (.mul A A) (.mul (.mul (.mul d q) b) b)
    let D := Expr.mul d b
    let Y := Expr.sub (.mul w D) A
    Equivalent (pairEval (.add (.mul (.mul (.mul (.mul q z) z) D) D)
      (.mul (.sub q (.constant 1)) N)) v)
      (pairEval (.add (.mul (.mul (.sub q (.constant 1)) Y) Y) (.mul D D)) v) := by
  simp [pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent]
  all_goals ring


end FreeJNormZero
#print axioms FreeJNormZero.ordinary_shape
#print axioms FreeJNormZero.ordinary_residual_zero
#print axioms FreeJNormZero.cleared_auxiliary_identity
#print axioms FreeJNormZero.polarization_identity
#print axioms FreeJNormZero.cleared_auxiliary_pairs
