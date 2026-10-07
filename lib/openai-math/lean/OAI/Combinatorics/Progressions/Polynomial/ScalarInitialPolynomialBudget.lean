import OAI.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData

namespace OAI

section

namespace Erdos3

noncomputable def scalarInitialReferencePolynomial (d A : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let P := Polynomial.C A * (X + 1)
  let M := Polynomial.C (d + 1) * X
  let D := Polynomial.C d
  let input := M * (P + 3) + X * P + 2 * (X + 1) + P + 1
  let Z := 4 * (6 * input + P + 3 * D + 10) + 2 * P + 10
  let row := (16 + 4 * D) * Z + 16 * D + 48
  let error := Z + row + X * (row + 6 * Z + 12)
  let G := 2 * (30 + 2 * X * Z + 2 * X + error + X * (5 * Z + 11) + 10 * Z + 4 * (2 + D)) + 2
  G + Z + P + M + X + D + 2 * (3 * X + 10) + X + 20

theorem scalarInitialReferenceInput_le_polynomial (m n d A : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ (d + 1 : ℝ) * p) (hn : (n : ℝ) ≤ p) :
    scalarInitialReferenceInput m n d p ((A : ℝ) * (p + 1)) ≤
      (scalarInitialReferencePolynomial d A).eval₂ (Nat.castRingHom ℝ) p := by
  simp [scalarInitialReferenceInput, scalarInitialReferencePolynomial,
    replacementCommonInputLog, replacementCutoffInputLog, physicalReplacementInputLog,
    physicalPairCoefficientLog, smoothPairErrorLog, smoothPairRowErrorLog, scalarTransferTail]
  gcongr

theorem exists_scalarInitialReferenceInput_power_bound (d A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m n : ℕ) (p : ℝ), 0 ≤ p →
      (m : ℝ) ≤ (d + 1 : ℝ) * p → (n : ℝ) ≤ p →
      scalarInitialReferenceInput m n d p ((A : ℝ) * (p + 1)) ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (scalarInitialReferencePolynomial d A)
  refine ⟨C, hC, ?_⟩
  intro m n p hp hm hn
  exact (scalarInitialReferenceInput_le_polynomial m n d A hp hm hn).trans (hbound p hp)

end Erdos3

end

end OAI
