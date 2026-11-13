import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Model-level negative-unit exclusion for an arbitrary signed ordinary
norm whose second coordinate has an explicit factor 2. This is not yet a
literal 12-variable graph theorem or an object-language proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Ordinary12Residual
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private def x (i : Fin 8) : Expr (Fin 8) := .var i

/-- Slots encode signed AN, b, d and Q by pairs of natural coordinates;
actual b_n is twice the signed b. -/
def ordinaryFactor : Expr (Fin 8) :=
  1 + (x 0 - x 1) * (x 0 - x 1) -
    (x 4 - x 5) * (2 * (x 2 - x 3)) * (2 * (x 2 - x 3)) * (x 6 - x 7)

private theorem ordinary_mod : ∀ a b d q : ZMod 4,
    1 + a*a - d*(2*b)*(2*b)*q ≠ -1 := by decide

/-- The signed ordinary factor cannot be the negative unit, in every IΣ₁
model, provided its displayed second coordinate is explicitly even. -/
theorem ordinary_factor_ne_negative_one (v : Fin 8 → V) :
    (pairEval ordinaryFactor v).1 + 1 ≠ (pairEval ordinaryFactor v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  have hm := ordinary_mod (residue (v 0) - residue (v 1))
    (residue (v 2) - residue (v 3))
    (residue (v 4) - residue (v 5))
    (residue (v 6) - residue (v 7))
  apply hm
  simpa only [ordinaryFactor, x, syntax_add, syntax_sub, syntax_mul, syntax_var, syntax_ofNat] using hn

end DiophantineConsistency.Ordinary12Residual
#print axioms DiophantineConsistency.Ordinary12Residual.ordinary_factor_ne_negative_one
