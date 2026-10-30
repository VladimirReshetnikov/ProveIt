import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Converse from all four actual signed factor units to the literal zero. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFactorZero2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
  ArithmeticAdaptiveFactorUnits2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The four actual syntax factors representing +1 imply the actual
unshifted adaptive expression is zero, for arbitrary integer ports. -/
theorem zero_of_factor_units (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (h : FactorUnits p v) : InternalZero (expressionAt p) v := by
  obtain ⟨h0,h1,ha,hs⟩ := h
  have e0 := equivalent_one.mpr h0
  have e1 := equivalent_one.mpr h1
  have ea := equivalent_one.mpr ha
  have es := equivalent_one.mpr hs
  have hp : Equivalent (pairEval ((factors p).2.2.2 * ((factors p).2.2.1 *
      ((factors p).1 * (factors p).2.1))) v) (natural (1:V)) := by
    change Equivalent (multiply (pairEval (factors p).2.2.2 v)
      (multiply (pairEval (factors p).2.2.1 v)
        (multiply (pairEval (factors p).1 v) (pairEval (factors p).2.1 v)))) (natural (1:V))
    simpa using equivalent_multiply es (equivalent_multiply ea (equivalent_multiply e0 e1))
  have he := equivalent_one.mp hp
  rw [expression_factors]
  change (Expr.sub ((factors p).2.2.2 * ((factors p).2.2.1 *
      ((factors p).1 * (factors p).2.1))) (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub ((factors p).2.2.2 * ((factors p).2.2.1 *
      ((factors p).1 * (factors p).2.1))) (Expr.constant 1)).splitNatural.2.evalSemiring v
  simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,add_comm] using he

/-- A positive unshifted witness yields a witness of the displayed shifted
natural equation without postulating subtraction cancellation. -/
theorem shifted_zero_of_factor_units (v : Fin 13 → V)
    (hv : ∀ j, 0<v j) (h : FactorUnits CurrentWindowCarry2011.ports v) :
    InternalZero naturalExpression (fun j => v j-1) := by
  have hplus : (fun j => (v j-1)+1)=v := by
    funext j
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hv j))
  change InternalZero (positiveShift expression) (fun j => v j-1)
  rw [internalZero_positiveShift,hplus]
  exact zero_of_factor_units CurrentWindowCarry2011.ports v h
end DiophantineConsistency.ArithmeticAdaptiveConstructionFactorZero2011
