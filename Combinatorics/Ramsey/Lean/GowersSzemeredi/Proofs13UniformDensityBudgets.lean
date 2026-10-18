import GowersSzemeredi.Proofs13UniformRoundedBudgets

/-! Bohr-model integer budgets: the radius `section10Zeta` is positive
(`section10Zeta_pos`), and the threshold `section13IntegerBudgetThreshold` has
the finite maximum `section13DensityIntegerThreshold` over the admissible
spectrum sizes.

The budgets uniform over the actual density (`lemma_13_6_uniform_density`) are
in `Proofs13UniformDensityBudgetsSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- The radius in the corrected Section 10 model is positive. -/
theorem section10Zeta_pos {a : Real} (ha : 0 < a) : 0 < section10Zeta a := by
  have hk : 0 < section10SpectrumParameter a := by
    apply Nat.ceil_pos.mpr
    unfold section10SpectrumBound
    positivity
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos ha _))
    (by exact_mod_cast hk)

def section13IntegerBudgetThreshold (delta : Real) (q : Nat) : Real :=
  let theta := section10Lambda (delta ^ 32 / 16)
  let d₀ := section13ThetaOne theta / (64 * Real.pi)
  max (uniformRoundedPowerThreshold (section13Zeta delta / 2) (min 1 (d₀ / 2))
    (section10Zeta (delta ^ 32 / 16)) ((1 : Real) / (2 : Real) ^ (13 * section13Q delta)))
    (positivePowerThreshold 4 d₀ (section13ThetaOne theta ^ 2 / (16 * (q : Real))))

/-- A finite maximum handles every admissible spectrum size. -/
def section13DensityIntegerThreshold (delta : Real) : Nat :=
  (Finset.range (Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) + 1)).sup
    (fun q => Nat.ceil (section13IntegerBudgetThreshold delta q))

end LeanProofs.GowersSzemeredi
