import GowersSzemeredi.Proofs16GlobalBilinearBohrTheorem

/-! Uniform positive size of the bilinear Bohr variety in the seven-operator
set, using a density-dependent integer denominator. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

namespace CompletionParameters

def varietyCells (p : CompletionParameters) : Nat := ⌈1 / p.varietyRadius⌉₊
def varietySizeDenominator (p : CompletionParameters) : Nat :=
  p.varietyCells ^ (p.spectrumCap + (p.fixedCap + p.mapCap * p.mapCap + p.mapCap))

theorem varietyCells_pos (p : CompletionParameters) (h : 0 < p.varietyRadius) :
    0 < p.varietyCells := Nat.ceil_pos.mpr (by positivity)

theorem varietyCells_bound (p : CompletionParameters) (h : 0 < p.varietyRadius) :
    1 ≤ p.varietyRadius * p.varietyCells := by
  have hb : 1 / p.varietyRadius ≤ (p.varietyCells : Real) := Nat.le_ceil _
  have := (div_le_iff₀ h).mp hb
  nlinarith only [this]

theorem varietySizeDenominator_pos (p : CompletionParameters) (h : 0 < p.varietyRadius) :
    0 < p.varietySizeDenominator := pow_pos (p.varietyCells_pos h) _

/-- Every variety within the uniform frequency caps has the same size lower bound. -/
theorem variety_size_lower {N : Nat} [NeZero N] (p : CompletionParameters)
    {k : Nat} (F U : Finset (ZMod N)) (L : Fin k → ZMod N → ZMod N)
    (hrho : 0 < p.varietyRadius) (hk : k ≤ p.mapCap)
    (hF : F.card ≤ p.fixedCap + p.mapCap * p.mapCap) (hU : U.card ≤ p.spectrumCap) :
    N * N ≤ p.varietySizeDenominator * (bilinearBohrVariety F U L p.varietyRadius).card := by
  letI : NeZero p.varietyCells := ⟨ne_of_gt (p.varietyCells_pos hrho)⟩
  apply (variety_card_lower F U L p.varietyCells (p.varietyCells_bound hrho)).trans
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_right (p.varietyCells_pos hrho)
  omega

end CompletionParameters

/-- Density alone controls both the geometric caps and the variety's positive size. -/
theorem density_seven_operator_bilinear_bohr_size {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) {alpha : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hN : densitySevenModulusBound alpha ≤ N) :
    let p := densitySevenParameters alpha
    ∃ (k : Nat) (F U : Finset (ZMod N)) (L : Fin k → ZMod N → ZMod N),
      k ≤ p.mapCap ∧ F.card ≤ p.fixedCap + p.mapCap * p.mapCap ∧
      U.card ≤ p.spectrumCap ∧ 0 < p.varietyRadius ∧ 0 < p.varietySizeDenominator ∧
      (∀ j, IsFreimanLinearOn (bohr U p.varietyRadius) (L j) ∧ L j 0 = 0) ∧
      N * N ≤ p.varietySizeDenominator * (bilinearBohrVariety F U L p.varietyRadius).card ∧
      bilinearBohrVariety F U L p.varietyRadius ⊆
        horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))) := by
  obtain ⟨k, F, U, L, hk, hF, hU, hrho, hL, hsub⟩ :=
    density_seven_operator_bilinear_bohr A ha ha1 hA hN
  exact ⟨k, F, U, L, hk, hF, hU, hrho, (densitySevenParameters alpha).varietySizeDenominator_pos hrho,
    hL, (densitySevenParameters alpha).variety_size_lower F U L hrho hk hF hU, hsub⟩

end LeanProofs.GowersSzemeredi
