import OAI.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem NilpotentLieFiltration.adapted_basis_weight_bounds
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ w i})) (i : Fin d) :
    1 ≤ w i ∧ w i ≤ s := by
  constructor
  · have h : b i ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    rw [hlayers] at h
    exact b.self_mem_span_image.mp h
  · by_contra h
    have hi : s + 1 ≤ w i := by omega
    have hmem : b i ∈ F.layer (s + 1) := by
      rw [hlayers]
      exact b.self_mem_span_image.mpr hi
    rw [F.terminal, Submodule.mem_bot] at hmem
    exact b.ne_zero i hmem

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

theorem exists_central_adapted_model_data (D : RationalFilteredNilmanifold L s d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ F : D.AdaptedModelData, Monotone F.weight ∧ IsCentralLieBasis F.basis ∧
      (∀ i, 1 ≤ F.weight i ∧ F.weight i ≤ s) ∧
      F.model.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1 := by
  obtain ⟨b, w, N, hw, hc, hlayers, hb, _, hbracket, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let F : D.AdaptedModelData := ⟨b, w, hlayers, N, hN, hin, hout⟩
  have hbase : 1 ≤ p + 3 := by linarith
  have hpq : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ ≤ (p + 3) ^ 11 := by
        simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hD.1.trans hpq
  refine ⟨F, hw, hc, D.filtration.adapted_basis_weight_bounds b w hlayers, ?_, hb⟩
  exact D.filtration.ofAdaptedBasis_geometry b w hlayers D.lattice N hN hin hout
    (by positivity) hdim
    (hNp.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 9 ≤ 11)))) hbracket

theorem exists_controlled_central_rebase :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (F : D.AdaptedModelData) (H : ℕ)
        (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H),
        Monotone F.weight ∧ IsCentralLieBasis F.basis ∧
        (∀ i, 1 ≤ F.weight i ∧ F.weight i ≤ s) ∧
        p ≤ (p + 2) ^ C ∧ F.model.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ {σ : Type*} {w : σ → ℕ} (T : D.Niltest w), T.ComplexityLE p →
          (F.rebaseNiltest H hH T).ComplexityLE ((p + 2) ^ C) := by
  let R : Polynomial ℕ := (Polynomial.X + 3) ^ 11 + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (R + (R + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D p hp hD
  obtain ⟨F, hw, hc, hweights, hF, hb⟩ := D.exists_central_adapted_model_data hp hD
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let r := (p + 3) ^ 11 + p + 2
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hfr : (p + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hHbound : (H : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [r]; linarith))
  have hbud : r + (r + 2) ^ 2 ≤ (p + 2) ^ C := by
    simpa [R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + 2) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hbud
  have hgeom : F.model.GeometryComplexityLE r := hF.mono F.model hfr
  refine ⟨F, H, hH, hw, hc, hweights, hpr.trans hrC, hgeom.mono F.model hrC, ?_⟩
  intro σ w T hT
  exact (F.rebaseNiltest_complexity H hH T hr (hT.mono hpr) hgeom hHbound).mono hbud

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
