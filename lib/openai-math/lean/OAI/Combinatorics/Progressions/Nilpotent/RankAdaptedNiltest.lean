import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.AdaptedModelData

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (F : D.AdaptedModelData) (H : ℕ)
  (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) {w : σ → ℕ}

noncomputable def rebaseNiltest (T : D.Niltest w) : F.model.Niltest w where
  orbit := T.orbit
  observable := T.observable
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d (finrank ℚ L) H
  norm_le := T.norm_le
  lipschitz := by
    let := F.model.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hT : dist (T.observable x) (T.observable y) ≤
        (T.lipBound : ℝ) * @dist D.Space D.metricSpace.toDist x y := by
      let := D.metricSpace
      exact T.lipschitz.dist_le_mul x y
    calc
      dist (T.observable x) (T.observable y) ≤
          (T.lipBound : ℝ) * @dist D.Space D.metricSpace.toDist x y := hT
      _ ≤ (T.lipBound : ℝ) *
          (coordinateLipschitzBound d (finrank ℚ L) H * dist x y) :=
        mul_le_mul_of_nonneg_left (F.original_dist_le H hH x y) T.lipBound.coe_nonneg
      _ = ↑(T.lipBound * coordinateLipschitzBound d (finrank ℚ L) H) * dist x y := by
        rw [NNReal.coe_mul]
        ring

theorem rebaseNiltest_orbit (T : D.Niltest w) : (F.rebaseNiltest H hH T).orbit = T.orbit := rfl

theorem rebaseNiltest_normBound (T : D.Niltest w) : (F.rebaseNiltest H hH T).normBound = T.normBound := rfl

theorem rebaseNiltest_eval (T : D.Niltest w) (x : σ → ℤ) : (F.rebaseNiltest H hH T).eval x = T.eval x := rfl

theorem rebaseNiltest_evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (F.rebaseNiltest H hH T).evalCyclic N x = T.evalCyclic N x := rfl

theorem rebaseNiltest_unit_interval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    (F.rebaseNiltest H hH T).UnitIntervalValued := hT

theorem rebaseNiltest_vertical (T : D.Niltest w) (eta : L →ₗ[ℚ] ℚ)
    (hT : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) :
    ∀ z, z ∈ F.model.filtration.realification.subgroup s → ∀ x,
      (F.rebaseNiltest H hH T).observable (z • x) =
        character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) *
          (F.rebaseNiltest H hH T).observable x := hT

theorem rebaseNiltest_kernel_invariant (T : D.Niltest w) {J : Type*} (eta : J → L →ₗ[ℚ] ℚ)
    (hT : ∀ z, z ∈ D.filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x, T.observable (z • x) = T.observable x) :
    ∀ z, z ∈ F.model.filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x,
        (F.rebaseNiltest H hH T).observable (z • x) = (F.rebaseNiltest H hH T).observable x := hT

theorem rebaseNiltest_complexity (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hT : T.ComplexityLE p) (hF : F.model.GeometryComplexityLE p) (hHp : (H : ℝ) ≤ Real.exp p) :
    (F.rebaseNiltest H hH T).ComplexityLE (p + (p + 2) ^ 2) := by
  have hK : (coordinateLipschitzBound d (finrank ℚ L) H : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    coordinateLipschitzBound_le_exp d (finrank ℚ L) H hp hT.1.1 hF.1 hHp
  have h1 : 1 ≤ Real.exp ((p + 2) ^ 2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  refine ⟨hF.mono F.model (le_add_of_nonneg_right (sq_nonneg _)), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * coordinateLipschitzBound d (finrank ℚ L) H) ≤ p + (p + 2) ^ 2
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * coordinateLipschitzBound d (finrank ℚ L) H ≤
        (2 + (T.normBound : ℝ)) * Real.exp ((p + 2) ^ 2) +
          (T.lipBound : ℝ) * Real.exp ((p + 2) ^ 2) :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hK T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp ((p + 2) ^ 2) := by ring
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) :=
      mul_le_mul_of_nonneg_right (Niltest.observable_budget hT) (Real.exp_pos _).le
    _ = Real.exp (p + (p + 2) ^ 2) := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.AdaptedModelData

end

section

namespace Erdos3

def rankAdaptedNiltestBase (p : ℝ) : ℝ := (p + 3) ^ 11 + p + 2

def rankAdaptedNiltestBudget (p : ℝ) : ℝ :=
  rankAdaptedNiltestBase p + (rankAdaptedNiltestBase p + 2) ^ 2

theorem le_rankAdaptedNiltestBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ rankAdaptedNiltestBudget p := by
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  unfold rankAdaptedNiltestBudget rankAdaptedNiltestBase
  nlinarith [sq_nonneg ((p + 3) ^ 11 + p + 2 + 2)]

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

theorem exists_adapted_niltest {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)
    {w : σ → ℕ} (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hR : R.ComplexityLE p) (hT : T.ComplexityLE p) :
    ∃ F : R.AdaptedData,
      F.rank.ComplexityLE (rankAdaptedNiltestBudget p) ∧
      (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1) ∧
      (∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + 3) ^ 5) ∧
      ∃ S : F.model.Niltest w, S.orbit = T.orbit ∧ S.observable = T.observable ∧
        S.ComplexityLE (rankAdaptedNiltestBudget p) := by
  obtain ⟨F, hF, hb, hinv⟩ := R.exists_rank_adapted_data hp hR
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let q := rankAdaptedNiltestBase p
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpq : p ≤ q := by dsimp [q, rankAdaptedNiltestBase]; linarith
  have hfq : (p + 3) ^ 11 ≤ q := by dsimp [q, rankAdaptedNiltestBase]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [q, rankAdaptedNiltestBase]; linarith))
  have hqb : q ≤ rankAdaptedNiltestBudget p := by
    exact le_add_of_nonneg_right (sq_nonneg _)
  refine ⟨F, hF.mono F.rank (hfq.trans hqb), hb, hinv,
    F.toAdaptedModelData.rebaseNiltest H hH T, rfl, rfl, ?_⟩
  exact F.toAdaptedModelData.rebaseNiltest_complexity H hH T hq
    (hT.mono hpq) (hF.1.mono F.model hfq) hHq

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

end OAI
