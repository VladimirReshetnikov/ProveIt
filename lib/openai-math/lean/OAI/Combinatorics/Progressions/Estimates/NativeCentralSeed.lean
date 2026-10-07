import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight
import OAI.Combinatorics.Progressions.Geometry.CentralOrbitMetric

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_central_character_extension (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (hint : ∀ γ ∈ Γ, ∃ n : ℤ, η γ.coord = n) :
    letI := quotientMetricSpace e Γ hΓ
    ∃ f : NilpotentLieBCHGroup L s hnil ⧸ Γ → ℂ,
      LipschitzWith (2 * logCharacterMetricConstant s (Fintype.card ι) H A) f ∧
      (∀ z ∈ T, f (QuotientGroup.mk z) = logCharacter η z) ∧ ∀ x, ‖f x‖ ≤ 2 := by
  let := quotientMetricSpace e Γ hΓ
  obtain ⟨f, hf, heq, hbound⟩ := exists_complex_extension_along_map
    (fun z : T => (QuotientGroup.mk z.val : _ ⧸ Γ)) (fun z : T => logCharacter η z.val)
    (logCharacterMetricConstant s (Fintype.card ι) H A) 1
    (central_logCharacter_coset_dist_le e c hstructure hc Γ T hΓ hT η A hη hint)
    (fun z => (logCharacter_norm η z.val).le)
  exact ⟨f, hf, fun z hz => heq ⟨z, hz⟩, by simpa only [NNReal.coe_one, mul_one] using hbound⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def realifyFunctional (η : L →ₗ[ℚ] ℚ) : (ℝ ⊗[ℚ] L) →ₗ[ℝ] ℝ :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
    ((Algebra.linearMap ℚ ℝ).comp η))

@[simp]
theorem realifyFunctional_tmul (η : L →ₗ[ℚ] ℚ) (r : ℝ) (v : L) :
    realifyFunctional η (r ⊗ₜ[ℚ] v) = r * (η v : ℝ) := by
  simp [realifyFunctional]

noncomputable def basisFrequency {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) : L →ₗ[ℚ] ℚ :=
  ∑ j : S, ((n j : ℚ) / (N : ℚ)) • b.coord j

theorem basisFrequency_apply {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) (v : L) :
    basisFrequency b S N n v = ∑ j : S, ((n j : ℚ) / (N : ℚ)) * b.repr v j := by
  simp [basisFrequency, Basis.coord_apply]

theorem basisFrequency_basis {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) (j : S) :
    basisFrequency b S N n (b j) = (n j : ℚ) / (N : ℚ) := by
  classical
  rw [basisFrequency_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hval : (j : ι) ≠ i := fun h => hij (Subtype.ext h.symm)
    simp [Basis.repr_self, hval]
  · simp

theorem realify_basisFrequency_direction {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (hN : 0 < N) (n : S → ℤ) (j : S) :
    realifyFunctional (basisFrequency b S N n) ((N : ℝ) • b.baseChange ℝ j) = n j := by
  simp only [map_smul, Basis.baseChange_apply, realifyFunctional_tmul,
    basisFrequency_basis, one_mul, smul_eq_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  exact mul_div_cancel₀ _ (by exact_mod_cast hN.ne')

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_central_seed (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ f : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K f) ∧
        (∀ x, ‖f x‖ ≤ 2) ∧ ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
          f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨a, _, hcost⟩ := exists_logCharacterMetricConstant_exp_bound s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((2 * X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  let H := ⌈Real.exp p⌉₊
  let A : ℝ≥0 := d * H
  have hlinear (x : ℝ ⊗[ℚ] L) : |realifyFunctional η x| ≤
      A * ‖(D.basis.baseChange ℝ).equivFun x‖ := by
    have h := abs_linearMap_le_basis_bound (D.basis.baseChange ℝ) (realifyFunctional η)
      (H : ℝ≥0) (fun i => by
        simpa only [Basis.baseChange_apply, realifyFunctional_tmul, one_mul, NNReal.coe_natCast] using
          (rationalHeightLE_ceil_exp (hη i)).abs_real_le) x
    simpa only [Fintype.card_fin, A, NNReal.coe_mul, NNReal.coe_natCast] using h
  obtain ⟨f, hf, hseed, hnorm⟩ := exists_central_character_extension (D.basis.baseChange ℝ)
    (lieStructureConstants D.basis) (fun i j k => (realLieBasis_structure D.basis i j k).symm)
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    D.realLattice (D.filtration.realification.subgroup s) D.realLattice_closed_discrete.1
    (fun z hz v => D.filtration.realification.top_layer_central hz v)
    (realifyFunctional η) A hlinear hint
  let K := 2 * logCharacterMetricConstant s d H A
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hA : (A : ℝ) ≤ Real.exp (2 * p + 1) := by
    have hd : (d : ℝ) ≤ Real.exp p := hD.1.trans (by linarith [Real.add_one_le_exp p])
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) := mul_le_mul hd hH (Nat.cast_nonneg H) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hK : (K : ℝ) ≤ Real.exp ((2 * p + 1 + a) ^ a) :=
    hcost d H A (2 * p + 1) (by positivity) (hD.1.trans (by linarith))
      (hH.trans (Real.exp_le_exp.mpr (by linarith))) hA
  have hpc : (2 * p + 1 + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hpoly p hp
  refine ⟨K, hK.trans (Real.exp_le_exp.mpr hpc), f, ?_, hnorm, hseed⟩
  simp only [Fintype.card_fin] at hf
  convert hf using 1
  rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
