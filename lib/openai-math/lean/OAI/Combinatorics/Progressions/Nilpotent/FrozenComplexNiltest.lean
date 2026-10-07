import OAI.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
  {w : σ → ℕ} (T : E.Niltest w) (g : D.filtration.realification.PolynomialOrbit w)
  (K : ℝ≥0)
  (hK : letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith K (frozenCosetMap D.realLattice E.realLattice
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h))

noncomputable def frozenComplexNiltest : D.Niltest w where
  orbit := g
  observable := T.observable ∘ frozenCosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h
  normBound := T.normBound
  lipBound := T.lipBound * K
  norm_le x := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact T.lipschitz.comp hK

theorem frozenComplexNiltest_eval (x : σ → ℤ) :
    (D.frozenComplexNiltest E φ a r h T g K hK).eval x =
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          (D.filtration.realification.polynomialOrbitEval w x g) * r)) := rfl

theorem frozenComplexNiltest_complexity {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hD : D.GeometryComplexityLE q) (hT : T.ComplexityLE p)
    (hbound : (K : ℝ) ≤ Real.exp q) :
    (D.frozenComplexNiltest E φ a r h T g K hK).ComplexityLE (p + q + 4) := by
  have hb := T.observable_budget hT
  have hnorm : (T.normBound : ℝ) ≤ Real.exp (p + q) :=
    (by linarith [T.lipBound.coe_nonneg] : (T.normBound : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hlip : (T.lipBound : ℝ) * K ≤ Real.exp (p + q) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [T.normBound.coe_nonneg]) hbound K.coe_nonneg (Real.exp_pos _).le
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) + ((T.lipBound * K : ℝ≥0) : ℝ)) ≤ p + q + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp (p + q) := by
      simp only [NNReal.coe_mul]
      linarith [Real.one_le_exp (show 0 ≤ p + q by linarith)]
    _ ≤ Real.exp 4 * Real.exp (p + q) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem frozenComplexNiltest_top_invariant
    (hinv : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x : D.RealGroup,
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)))
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s) (x : D.Space) :
    (D.frozenComplexNiltest E φ a r h T g K hK).observable (z • x) =
      (D.frozenComplexNiltest E φ a r h T g K hK).observable x := by
  induction x using Quotient.inductionOn with
  | h x => exact hinv z hz x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
