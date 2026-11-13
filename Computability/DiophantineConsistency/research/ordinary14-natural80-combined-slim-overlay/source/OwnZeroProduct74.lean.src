import FirstFactor74

/-! Source-only extraction of the literal 74 signed product from its own
zero. The other three negative-unit residue exclusions remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OwnZeroProduct74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
open FirstFactor74Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem pairEval_mul {σ : Type*} (e f : Expr σ) (v : σ → V) :
    pairEval (e*f) v=multiply (pairEval e v) (pairEval f v) := rfl

private theorem one_of_zero {σ : Type*} (e : Expr σ) (v : σ → V)
    (hz : InternalZero (e-1) v) : Equivalent (pairEval e v) (natural (1:V)) := by
  apply equivalent_one.mpr
  change (Expr.sub e (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub e (Expr.constant 1)).splitNatural.2.evalSemiring v at hz
  simpa [Expr.splitNatural,NatExpr.evalSemiring,pairEval] using hz

private theorem swap_last (p q r s t : Pair V) :
    product5 p q r s t=product5 p q r t s := by
  apply Prod.ext <;> simp only [product5,multiply] <;> ring

/-- A 74 own zero gives the required product in the order first, main,
auxiliary, guard, strong. The literal output orders the last two oppositely. -/
theorem product_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P74PositiveGuard.graph p).output v) :
    Equivalent (product5 (pairEval (P74PositiveGuard.graph p).first v)
      (pairEval (P74PositiveGuard.graph p).main v)
      (pairEval (P74PositiveGuard.graph p).aux v)
      (pairEval (P74PositiveGuard.graph p).guardFactor v)
      (pairEval (P74PositiveGuard.graph p).strong v)) (natural (1:V)) := by
  rw [P74PositiveGuard.output_shape] at hz
  have h := one_of_zero _ v hz
  rw [pairEval_mul,pairEval_mul,pairEval_mul,pairEval_mul] at h
  change Equivalent (product5 (pairEval (P74PositiveGuard.graph p).first v)
    (pairEval (P74PositiveGuard.graph p).main v)
    (pairEval (P74PositiveGuard.graph p).aux v)
    (pairEval (P74PositiveGuard.graph p).strong v)
    (pairEval (P74PositiveGuard.graph p).guardFactor v)) (natural (1:V)) at h
  rw [swap_last] at h
  exact h

/-- Own-zero unit extraction, conditional only on the three other factors'
mod-four exclusions and the explicit beta/positive-slot assumptions. -/
theorem factor_units_of_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta)
    (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)
    (hz : InternalZero (P74PositiveGuard.graph p).output v)
    (hmain : pairResidue (pairEval (P74PositiveGuard.graph p).main v) ≠ -1)
    (haux : pairResidue (pairEval (P74PositiveGuard.graph p).aux v) ≠ -1)
    (hstrong : pairResidue (pairEval (P74PositiveGuard.graph p).strong v) ≠ -1) :
    v 8*v 8=(m beta v*k v)*(m beta v*k v+k v)+1 ∧
    (pairEval (P74PositiveGuard.graph p).main v).1=
      (pairEval (P74PositiveGuard.graph p).main v).2+1 ∧
    (pairEval (P74PositiveGuard.graph p).aux v).1=
      (pairEval (P74PositiveGuard.graph p).aux v).2+1 ∧
    (pairEval (P74PositiveGuard.graph p).guardFactor v).1=
      (pairEval (P74PositiveGuard.graph p).guardFactor v).2+1 ∧
    (pairEval (P74PositiveGuard.graph p).strong v).1=
      (pairEval (P74PositiveGuard.graph p).strong v).2+1 := by
  exact first_factor_units p beta v hbeta hb hJ hw hs _ _ _ _
    (product_of_zero p v hz) hmain haux hstrong

end DiophantineConsistency.OwnZeroProduct74Draft

#print axioms DiophantineConsistency.OwnZeroProduct74Draft.product_of_zero
#print axioms DiophantineConsistency.OwnZeroProduct74Draft.factor_units_of_zero
