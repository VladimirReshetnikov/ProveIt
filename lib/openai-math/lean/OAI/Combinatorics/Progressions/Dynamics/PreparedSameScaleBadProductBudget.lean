import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds
import OAI.Combinatorics.Progressions.Geometry.PreparedBadProductSpatialBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedModularCanonicalDetectorAllocationBudget (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P : ℝ} {M nX : ℕ},
      0 ≤ P → (M : ℝ) ≤ P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let budget := (P + A) ^ A
      P ≤ budget ∧ (Jalloc : ℝ) ∈ Set.Icc 0 budget ∧ pnum ∈ Set.Icc 0 budget ∧
        pnum + Jalloc + nX + M + 1 ≤ budget := by
  let c := 2 ^ m * (2 ^ (2 * m) * m.factorial + 1) + 1
  let blocks := ∑ j : Fin m, preparedCommonBlockCount m j
  let X : Polynomial ℕ := Polynomial.X
  let allocation : Polynomial ℕ := Polynomial.C c * (Polynomial.C (m + 1) * X + 11)
  let base : Polynomial ℕ := Polynomial.C ((m + 1) * (m + 3)) +
    X * Polynomial.C m * Polynomial.C blocks + X + Polynomial.C m + 2
  let dimension := base + (Polynomial.C (m + 2) + X * Polynomial.C m * Polynomial.C m) * allocation
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget (dimension + allocation + 3 * X + 1)
  refine ⟨A, hA, ?_⟩
  intro P M nX hP hM hnX Jalloc pnum budget
  let allocBound : ℝ := c * (((m : ℝ) + 1) * P + 11)
  let baseBound : ℝ := ((m : ℝ) + 1) * (m + 3) + P * m * blocks + P + m + 2
  let dimBound : ℝ := baseBound + ((m : ℝ) + 2 + P * m * m) * allocBound
  have halloc0 : 0 ≤ allocBound := by dsimp only [allocBound]; positivity
  have hbase0 : 0 ≤ baseBound := by dsimp only [baseBound]; positivity
  have hdim0 : 0 ≤ dimBound := by dsimp only [dimBound]; positivity
  have halloc : (Jalloc : ℝ) ≤ allocBound := by
    have hlinear := Nat.cast_le (α := ℝ).mpr (modularInitialBlockCount_linear_bound m (nX + m * M))
    change (Jalloc : ℝ) ≤ (c * (nX + m * M + 11) : ℕ) at hlinear
    push_cast at hlinear
    apply hlinear.trans
    dsimp only [allocBound]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
    have hmM := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m)
    nlinarith
  have hbase : (preparedCommonSamplerDimension m M : ℝ) ≤ baseBound := by
    simp only [preparedCommonSamplerDimension, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    dsimp only [baseBound, blocks]
    gcongr
  have hdim : pnum ≤ dimBound := by
    dsimp only [pnum]
    rw [enlargedPreparedCommonSamplerDimension_polynomial]
    push_cast
    dsimp only [dimBound]
    apply add_le_add hbase
    exact mul_le_mul (by gcongr) halloc (Nat.cast_nonneg _) (by positivity)
  have hsum : dimBound + allocBound + 3 * P + 1 ≤ budget := by
    simpa [dimension, allocation, base, X, dimBound, allocBound, baseBound,
      Nat.cast_add, Nat.cast_mul] using hbound P hP
  have hallocNonneg : (0 : ℝ) ≤ Jalloc := Nat.cast_nonneg _
  have hnumNonneg : 0 ≤ pnum := Nat.cast_nonneg _
  refine ⟨?_, ⟨hallocNonneg, ?_⟩, ⟨hnumNonneg, ?_⟩, ?_⟩
  all_goals linarith

theorem exists_shiftedPower_triple_composition_budget (A C B : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {P : ℝ}, 0 ≤ P →
      (((P + A) ^ A + C) ^ C + B) ^ B ≤ (P + D) ^ D := by
  let poly : Polynomial ℕ :=
    (((Polynomial.X + Polynomial.C A) ^ A + Polynomial.C C) ^ C + Polynomial.C B) ^ B
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨D, hD, ?_⟩
  intro P hP
  simpa [poly, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedBadProductSourceBudget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B P0 E V : ℝ} {M nX : ℕ},
      0 ≤ B → (M : ℝ) ≤ B → (nX : ℝ) ≤ B →
      P0 ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → V ∈ Set.Icc 0 B →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
      let ncoeff := (m + 1) * (pnum + 1) ^ m
      let P := (B + C) ^ C
      B ≤ P ∧ P0 ≤ P ∧ (ncoeff : ℝ) + pnum ≤ P ∧
        allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ P ∧
        V + 3 * E + 16 ≤ P ∧ ((pnum + 1) * nX : ℕ) ≤ P := by
  obtain ⟨A, _, halloc⟩ := exists_preparedModularCanonicalDetectorAllocationBudget m
  let X : Polynomial ℕ := Polynomial.X
  let dim : Polynomial ℕ := (X + Polynomial.C A) ^ A
  let coeff : Polynomial ℕ := Polynomial.C (m + 1) * (dim + 1) ^ m
  let scale : Polynomial ℕ := (1 + X ^ 2) * (5 * X + 49) + X ^ 2 * (9 * X + 24)
  let total := X + coeff + dim + scale + (4 * X + 16) + (dim + 1) * X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro B P0 E V M nX hB hM hnX hP0 hE hV Jalloc pnum ncoeff P
  have hP0lo := hP0.1
  have hP0hi := hP0.2
  have hElo := hE.1
  have hEhi := hE.2
  have hVlo := hV.1
  have hVhi := hV.2
  let dimBound : ℝ := (B + A) ^ A
  let coeffBound : ℝ := (m + 1 : ℕ) * (dimBound + 1) ^ m
  let scaleBound : ℝ := (1 + B ^ 2) * (5 * B + 49) + B ^ 2 * (9 * B + 24)
  have hdim0 : 0 ≤ dimBound := by dsimp only [dimBound]; positivity
  have hcoeff0 : 0 ≤ coeffBound := by dsimp only [coeffBound]; positivity
  have hscale0 : 0 ≤ scaleBound := by dsimp only [scaleBound]; positivity
  have hframe0 : 0 ≤ (dimBound + 1) * B := by positivity
  obtain ⟨_, _, hnum, _⟩ := halloc hB hM hnX
  have hnumBound : (pnum : ℝ) ≤ dimBound := hnum.2
  have hcoeff : (ncoeff : ℝ) ≤ coeffBound := by
    dsimp only [ncoeff, coeffBound]
    push_cast
    gcongr
  have hframe : (((pnum + 1) * nX : ℕ) : ℝ) ≤ (dimBound + 1) * B := by
    push_cast
    gcongr
  have hscale : allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ scaleBound := by
    unfold allocatedWitnessScaleLog allocatedScaleLog
    dsimp only [scaleBound]
    gcongr; linarith
  have htotal : B + coeffBound + dimBound + scaleBound + (4 * B + 16) +
      (dimBound + 1) * B ≤ P := by
    simpa [total, X, coeff, dim, scale, coeffBound, dimBound, scaleBound, P,
      Nat.cast_add, Polynomial.eval₂_pow] using hbound B hB
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_preparedBadProductFinalBudget (m : ℕ) :
    ∃ C1 C2 : ℕ, 2 ≤ C1 ∧ 2 ≤ C2 ∧ ∀ {B P0 E V : ℝ} {M nX : ℕ},
      1 ≤ B → (M : ℝ) ≤ B → (nX : ℝ) ≤ B →
      P0 ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → V ∈ Set.Icc 0 B →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
      let ncoeff := (m + 1) * (pnum + 1) ^ m
      let P := (B + C1) ^ C1
      let Ps := (B + C2) ^ C2
      let Qf := allocatedFourierLogBudget m P
      1 ≤ P ∧ 1 ≤ Ps ∧ B ≤ P ∧ P0 ≤ P ∧
        (ncoeff : ℝ) + pnum ≤ P ∧
        allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ P ∧
        V + 3 * E + 16 ≤ P ∧ ((pnum + 1) * nX : ℕ) ≤ Ps ∧
        P ≤ Ps ∧ 2 * P + 2 * V + 5 * E + 24 ≤ Ps ∧
        (4 * Qf + 2) ^ 4 ≤ Ps ∧ 4 * Qf * (4 * Qf + 2) ^ 4 + Qf ≤ Ps := by
  obtain ⟨C1, hC1, hsource⟩ := exists_preparedBadProductSourceBudget m
  obtain ⟨C2, hC2, hspatial⟩ := exists_preparedBadProductSpatialBudget m C1
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro B P0 E V M nX hB hM hnX hP0 hE hV Jalloc pnum ncoeff P Ps Qf
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨hBP, hP0P, hprimitive, hscale, haccuracy, hframe⟩ := hsource hB0 hM hnX hP0 hE hV
  obtain ⟨hPPS, hwidth, _, hfreq, hmass⟩ := hspatial B hB0
  refine ⟨hB.trans hBP, hB.trans (hBP.trans hPPS), hBP, hP0P, hprimitive, hscale,
    haccuracy, hframe.trans hPPS, hPPS, ?_, hfreq, hmass⟩
  have hEhi := hE.2
  have hVhi := hV.2
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedWitnessScaleLog_mono {P P' Q Q' : ℝ}
    (hP : 0 ≤ P) (hPP' : P ≤ P') (hQ : 0 ≤ Q) (hQQ' : Q ≤ Q') :
    allocatedWitnessScaleLog P Q ≤ allocatedWitnessScaleLog P' Q' := by
  unfold allocatedWitnessScaleLog allocatedScaleLog
  gcongr

theorem allocatedWitnessScaleLog_le_prepared_envelope {B P0 Qw E V : ℝ}
    (hB : 0 ≤ B) (hP0 : P0 ∈ Set.Icc 0 B) (hQw : Qw ∈ Set.Icc 0 B)
    (hE : 0 ≤ E) (hV : 0 ≤ V) :
    allocatedWitnessScaleLog P0 Qw ≤
      allocatedWitnessScaleLog B (2 * B + 2 * V + 5 * E + 24) := by
  apply allocatedWitnessScaleLog_mono hP0.1 hP0.2 hQw.1
  exact hQw.2.trans (by linarith)

theorem exists_preparedSameScaleBadProductBudget (m : ℕ) :
    ∃ C1 C2 : ℕ, 2 ≤ C1 ∧ 2 ≤ C2 ∧ ∀ {B P0 Qw E V : ℝ} {M nX : ℕ},
      1 ≤ B → (M : ℝ) ≤ B → (nX : ℝ) ≤ B →
      P0 ∈ Set.Icc 0 B → Qw ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → V ∈ Set.Icc 0 B →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
      let ncoeff := (m + 1) * (pnum + 1) ^ m
      let P := (B + C1) ^ C1
      let Ps := (B + C2) ^ C2
      let Qf := allocatedFourierLogBudget m P
      1 ≤ P ∧ 1 ≤ Ps ∧ B ≤ P ∧ P0 ≤ P ∧ Qw ≤ P ∧
        (ncoeff : ℝ) + pnum ≤ P ∧ allocatedWitnessScaleLog P0 Qw ≤ P ∧
        V + 3 * E + 16 ≤ P ∧ ((pnum + 1) * nX : ℕ) ≤ Ps ∧
        P ≤ Ps ∧ 2 * P + 2 * V + 5 * E + 24 ≤ Ps ∧
        (4 * Qf + 2) ^ 4 ≤ Ps ∧ 4 * Qf * (4 * Qf + 2) ^ 4 + Qf ≤ Ps := by
  obtain ⟨C1, C2, hC1, hC2, hbudget⟩ := exists_preparedBadProductFinalBudget m
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro B P0 Qw E V M nX hB hM hnX hP0 hQw hE hV Jalloc pnum ncoeff P Ps Qf
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨hP1, hPs1, hBP, _, hprimitive, hscale, haccuracy, hframe, hPPS, hwidth, hfreq, hmass⟩ :=
    hbudget hB hM hnX (show B ∈ Set.Icc 0 B from ⟨hB0, le_rfl⟩) hE hV
  have hscale' : allocatedWitnessScaleLog P0 Qw ≤ P :=
    (allocatedWitnessScaleLog_le_prepared_envelope hB0 hP0 hQw hE.1 hV.1).trans hscale
  exact ⟨hP1, hPs1, hBP, hP0.2.trans hBP, hQw.2.trans hBP, hprimitive, hscale',
    haccuracy, hframe, hPPS, hwidth, hfreq, hmass⟩

end Erdos3.VectorPolynomial

end

end OAI
