import DiophantineConsistency.Ordinary12FreeJ

/-! Assemble the free-J literal zero from its three exact unit factors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJCompletenessFactorBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticAdaptiveFactorMagnitude2011

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The three signed factors being positive units is sufficient for the
exact free-J literal to vanish. No positivity of coordinates is assumed. -/
theorem zero_of_factor_units (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (hfirst : (pairEval (core p).first v).1 = (pairEval (core p).first v).2 + 1)
    (hmain : (pairEval (core p).main v).1 = (pairEval (core p).main v).2 + 1)
    (hordinary : (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2 + 1) :
    InternalZero (literal p) v := by
  have hproduct : Equivalent (multiply (multiply (pairEval (core p).first v)
      (pairEval (core p).main v)) (pairEval (core p).ordinary v)) (natural (1:V)) := by
    have h := equivalent_multiply
      (equivalent_multiply (equivalent_one.mpr hfirst) (equivalent_one.mpr hmain))
      (equivalent_one.mpr hordinary)
    simpa only [one_multiply] using h
  have hu := equivalent_one.mp hproduct
  rw [literal_eq_factors]
  change (Expr.sub _ (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub _ (Expr.constant 1)).splitNatural.2.evalSemiring v
  simpa [Expr.splitNatural, NatExpr.evalSemiring, pairEval, multiply] using hu

/-- Exact equivalence for this graph in each model; constructing a positive
valuation satisfying the factor equations remains a separate obligation. -/
theorem zero_iff_factor_units (p : Fin 4 → ℤ) (v : Fin 12 → V) :
    InternalZero (literal p) v ↔
      (pairEval (core p).first v).1 = (pairEval (core p).first v).2 + 1 ∧
      (pairEval (core p).main v).1 = (pairEval (core p).main v).2 + 1 ∧
      (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2 + 1 := by
  constructor
  · exact literal_factor_units p v
  · rintro ⟨h1, h2, h3⟩
    exact zero_of_factor_units p v h1 h2 h3

#print axioms FreeJCompletenessFactorBridge.zero_of_factor_units
#print axioms FreeJCompletenessFactorBridge.zero_iff_factor_units
end FreeJCompletenessFactorBridge
