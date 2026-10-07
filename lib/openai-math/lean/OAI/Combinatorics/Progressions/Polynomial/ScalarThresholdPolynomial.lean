import OAI.Combinatorics.Progressions.Dynamics.ScalarMeshCoefficientBudget

namespace OAI

section

namespace Erdos3

noncomputable def scalarThresholdPolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  let b := 1024 * (X + 3) ^ 3
  let row := (16 + 4 * X) * X + 16 * X + 48
  let error := X + row + X * (row + 6 * X + 12)
  let coeff := 30 + 2 * X * X + 2 * X + error + X * (5 * X + 11) + 10 * X + 4 * (2 + X)
  let mean := 2 * (b * (X + 2) + 2) + 4 + 2 * X * X + X * (5 * X + 11) + X
  let replacement := 2 * coeff + 2 * mean + (2 * b + 2) * X + 20
  let accuracy := 3 * X + (b * (X + 2) + 1) + 10
  let cell := 65536 * (X + 3) ^ 4 + X * b + accuracy + X + 1
  let mesh := X + 3 * (X + 1) + accuracy + 50
  X + X + 2 * (3 * X + 10) + 2 * replacement + X + X + 4 * mesh + 2 * cell + 2 * X + 100

theorem scalarCombinedLogThreshold_le_polynomial (n d b : ℕ)
    {p P0 Z G U common refCost : ℝ} (hcommon : 0 ≤ common) (hZ : 0 ≤ Z)
    (hp : p ≤ common) (hP0 : P0 ≤ common) (hZC : Z ≤ common) (hG : G ≤ common) (hU : U ≤ common)
    (hn : (n : ℝ) ≤ common) (hd : (d : ℝ) ≤ common) (href : refCost ≤ common)
    (hb : (b : ℝ) ≤ 1024 * (common + 3) ^ 3) :
    scalarCombinedLogThreshold n d b p P0 Z G refCost
      (scalarTransferCellLog common b p Z U)
      (scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)) ≤
      scalarThresholdPolynomial.eval₂ (Nat.castRingHom ℝ) common := by
  simp [scalarThresholdPolynomial, scalarCombinedLogThreshold, scalarTransferCellLog,
    scalarMeshLog, scalarTransferAccuracyLog, scalarTransferCapLog, scalarTransferTail,
    physicalReplacementThresholdLog, physicalPairCoefficientLog, physicalPairMeanLog,
    smoothPairErrorLog, smoothPairRowErrorLog, Polynomial.eval₂_pow]
  gcongr

theorem exists_scalarCombinedLogThreshold_common_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n d b : ℕ) (p P0 Z G U common refCost : ℝ),
    0 ≤ common → 0 ≤ Z → p ≤ common → P0 ≤ common → Z ≤ common → G ≤ common → U ≤ common →
    (n : ℝ) ≤ common → (d : ℝ) ≤ common → refCost ≤ common →
    (b : ℝ) ≤ 1024 * (common + 3) ^ 3 →
    scalarCombinedLogThreshold n d b p P0 Z G refCost
      (scalarTransferCellLog common b p Z U)
      (scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)) ≤ (common + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget scalarThresholdPolynomial
  refine ⟨C, hC, ?_⟩
  intro n d b p P0 Z G U common refCost hcommon hZ hp hP0 hZC hG hU hn hd href hb
  exact (scalarCombinedLogThreshold_le_polynomial n d b hcommon hZ hp hP0 hZC hG hU hn hd href hb).trans
    (hbound common hcommon)

end Erdos3

end

end OAI
