import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]

theorem exists_rankInvariant_niltest
    (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientLie
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal)
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z ∈ R.realSubgroup s (r + 1), ∀ x, T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr
      (lieQuotientMap (R.filtration.layerIdeal s (r + 1)) (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = R.rankQuotientOrbit Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound ∧
      (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
        T.observable (QuotientGroup.mk x)) ∧
      ∀ x, S.eval x = T.eval x := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap (R.filtration.layerIdeal s (r + 1)))
    (lieQuotientMap_surjective _) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff
        (R.filtration.layerIdeal s (r + 1)).toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := R.rankQuotientOrbit Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  }
  refine ⟨S, rfl, rfl, rfl, hf, ?_⟩
  intro x
  exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
    (R.rankQuotientOrbit_eval Q hQF T.orbit x)).trans (hf _)

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open scoped TensorProduct NNReal

theorem exists_rankInvariant_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d n : ℕ} {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      [T2Space (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))]
      (Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n)
      (hQF : Q.filtration = D.filtration.quotientLie
        (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal)
      (_hQL : Q.lattice = D.lattice.map
        (D.filtration.quotientStepHom (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1)) (D.basis j)) i) ≤ p) →
      (∀ z ∈ R.realSubgroup s (r + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = R.rankQuotientOrbit Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
        (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
          (NilpotentLieBCHGroup.realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
          T.observable (QuotientGroup.mk x)) ∧
        ∀ x, S.eval x = T.eval x := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 1 + Polynomial.C a) ^ a + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ r d n D R _ _ _ _ Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hSp, hSe⟩ := R.exists_rankInvariant_niltest Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + C) ^ C := by
    simpa [r, P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩, hSp, hSe⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
