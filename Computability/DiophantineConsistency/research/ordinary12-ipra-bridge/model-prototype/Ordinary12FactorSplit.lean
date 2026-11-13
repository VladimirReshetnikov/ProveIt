import DiophantineConsistency.Ordinary12Residual

/-! Abstract three-factor split for signed pairs. The two carrier exclusions
and the actual 12-variable literal-to-factor identity remain hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Ordinary12FactorSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.Ordinary12Residual

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Three signed factors multiplying to one are each positive units when
all three negative units are excluded. -/
theorem three_factor_units {p q r : Pair V}
    (h : Equivalent (multiply (multiply p q) r) (natural (1:V)))
    (hp : p.1 + 1 ≠ p.2) (hq : q.1 + 1 ≠ q.2) (hr : r.1 + 1 ≠ r.2) :
    p.1 = p.2 + 1 ∧ q.1 = q.2 + 1 ∧ r.1 = r.2 + 1 := by
  have h5 : Equivalent (product5 p q r (natural (1:V)) (natural (1:V))) (natural (1:V)) := by
    simpa only [product5, multiply_one] using h
  obtain ⟨mp,mq,mr,_,_⟩ := product5_magnitudes h5
  exact ⟨equivalent_one.mp (positive_of_magnitude_one mp hp),
    equivalent_one.mp (positive_of_magnitude_one mq hq),
    equivalent_one.mp (positive_of_magnitude_one mr hr)⟩

/-- In the abstract ordinary merger, only the two carrier exclusions remain
as assumptions: the ordinary factor's exclusion is proved separately. -/
theorem ordinary_three_factor_units {p q : Pair V} (v : Fin 8 → V)
    (h : Equivalent (multiply (multiply p q) (pairEval ordinaryFactor v)) (natural (1:V)))
    (hp : p.1 + 1 ≠ p.2) (hq : q.1 + 1 ≠ q.2) :
    p.1 = p.2 + 1 ∧ q.1 = q.2 + 1 ∧
      (pairEval ordinaryFactor v).1 = (pairEval ordinaryFactor v).2 + 1 := by
  exact three_factor_units h hp hq (ordinary_factor_ne_negative_one v)

end DiophantineConsistency.Ordinary12FactorSplit
#print axioms DiophantineConsistency.Ordinary12FactorSplit.three_factor_units
#print axioms DiophantineConsistency.Ordinary12FactorSplit.ordinary_three_factor_units
