/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.NativeReplacedRankFamily

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)

theorem lipschitz_native_frozenCosetMap {A C : ℝ≥0}
    (hφ : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha : letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x)) :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith (A * C) (frozenCosetMap D.realLattice E.realLattice
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (E.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  exact lipschitz_frozenCosetMap D.realLattice E.realLattice D.realLattice_closed_discrete.1
    E.realLattice_closed_discrete.1 _ a r h hφ ha

include h in
theorem exists_positive_frozen_observable {A C ℓ : ℝ≥0}
    (hφ : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha : letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x))
    (u : E.Space → ℂ) (hu : letI := E.metricSpace; LipschitzWith ℓ u)
    (hunit : ∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) :
    ∃ v : D.Space → ℂ,
      (letI := D.metricSpace; LipschitzWith (ℓ * (A * C)) v) ∧
      (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
      ∀ x : D.RealGroup, v (QuotientGroup.mk x) = u (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  let := D.metricSpace
  let := E.metricSpace
  let f := frozenCosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h
  have hf : LipschitzWith (A * C) f := D.lipschitz_native_frozenCosetMap E φ a r h hφ ha
  refine ⟨u ∘ f, hu.comp hf, fun x => hunit (f x), ?_, fun _ => rfl⟩
  intro x
  change ‖u (f x)‖ ≤ 1
  rw [← positiveClip_eq_self (u (f x)) (hunit (f x))]
  exact norm_positiveClip_le_one _

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem native_frozenCosetMap_dist_le {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (r a b : E.RealGroup)
    (h : ∀ γ ∈ D.realLattice, r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
    {A C : ℝ≥0}
    (hφ :
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha :
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x)) (x y : D.RealGroup) :
    letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
      (E.basis.baseChange ℝ)
    letI := D.metricSpace
    letI := E.metricSpace
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    dist (QuotientGroup.mk (a * ψ x * r) : E.Space) (QuotientGroup.mk (b * ψ y * r)) ≤
      (A * C : ℝ≥0) * dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk y) + dist a b := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (E.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
    (E.basis.baseChange ℝ)
  exact frozenCosetMap_dist_le D.realLattice E.realLattice D.realLattice_closed_discrete.1
    E.realLattice_closed_discrete.1 _ r h a b hφ ha (QuotientGroup.mk x) (QuotientGroup.mk y)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

noncomputable def conjugationPullback {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) : Subgroup D.filtration.Group :=
  ⨅ z : {z : E.filtration.Group // E.basis.equivFun z.coord ∈ denominatorGrid q},
    (E.lattice.map (MulAut.conj z.val).toMonoidHom).comap
      (NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ)

theorem exists_uniform_conjugated_source_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.conjugationPullback E φ q ∧ Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) := by
  obtain ⟨a, _, hconj⟩ := exists_uniform_conjugated_inner_grid s
  let X : Polynomial ℕ := Polynomial.X
  let U := X + 1 + (X + 1 + Polynomial.C a) ^ a + (X + 2) ^ 3
  let P := U + 2 * U ^ 2 + (U + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  classical
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  obtain ⟨B, hB, hBb, hBgrid⟩ := hconj E.basis E.filtration.lowerCentralSeries_eq_bot
    E.lattice E.grid q H t E.grid_pos hq E.inner_grid ht
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (hE.2.1.trans (Real.exp_le_exp.mpr hpt)) (hqp.trans (Real.exp_le_exp.mpr hpt))
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  have hAb : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  let N₀ := B * matrixDenominator A
  have hN₀ : 0 < N₀ := Nat.mul_pos hB (matrixDenominator_pos A)
  have hgrid : scaledIntegerGrid N₀ ⊆ bchSubgroupCoordinates D.basis (D.conjugationPullback E φ q) := by
    intro x hx
    change (⟨D.basis.equivFun.symm x⟩ : D.filtration.Group) ∈ D.conjugationPullback E φ q
    apply Subgroup.mem_iInf.mpr
    intro z
    change x ∈ bchSubgroupCoordinates D.basis
      ((E.lattice.map (MulAut.conj z.val).toMonoidHom).comap
        (NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    rw [bchSubgroupCoordinates_comap D.basis E.basis φ]
    exact hBgrid z.val z.property (matrix_mulVec_fine_grid A B hx)
  let u := t + (t + a) ^ a + (p + 2) ^ 3
  have htu : t ≤ u := by
    exact (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg a)) _)).trans
      (le_add_of_nonneg_right (pow_nonneg (by linarith) _))
  have hu : 0 ≤ u := ht.trans htu
  have hpu : p ≤ u := hpt.trans htu
  have hN₀b : (N₀ : ℝ) ≤ Real.exp u := by
    calc
      _ = (B : ℝ) * matrixDenominator A := Nat.cast_mul _ _
      _ ≤ Real.exp ((t + a) ^ a) * Real.exp ((p + 2) ^ 3) :=
        mul_le_mul hBb hAb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((t + a) ^ a + (p + 2) ^ 3) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [u]; linarith)
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hNb, hin, hout⟩ :=
    D.filtration.exists_normal_cover_exp_quadratic D.basis D.lattice (D.conjugationPullback E φ q)
      D.grid N₀ D.grid_pos hN₀ D.inner_grid D.outer_grid hgrid hu
      (by simpa only [Fintype.card_fin] using hD.1.trans hpu)
      (hD.2.1.trans (Real.exp_le_exp.mpr hpu)) hN₀b
  have hsum : u + 2 * u ^ 2 + (u + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, U, X, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C :=
    ((le_add_of_nonneg_right (by positivity : 0 ≤ 2 * u ^ 2)).trans
      (le_add_of_nonneg_right (sq_nonneg (u + 2)))).trans hsum
  have hiC : 2 * u ^ 2 ≤ (p + C) ^ C :=
    ((le_add_of_nonneg_left hu).trans (le_add_of_nonneg_right (sq_nonneg (u + 2)))).trans hsum
  have hgC : (u + 2) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (add_nonneg hu (by positivity))).trans hsum
  exact ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hiC), N, hN, hin, hout,
    D.withLattice_geometry Λ N hN hin hout hD (hpu.trans huC) (hNb.trans (Real.exp_le_exp.mpr hgC))⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem real_conjugationPullback_property {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) (hq : 0 < q) (Λ : Subgroup D.filtration.Group)
    (hΛ : Λ ≤ D.conjugationPullback E φ q)
    (r : E.RealGroup) (hr : (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q) :
    ∀ γ ∈ Λ.map realificationHom,
      r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice := by
  obtain ⟨z, hz, rfl⟩ := (realification_grid_iff
    (hnil := E.filtration.lowerCentralSeries_eq_bot) E.basis q hq r).mp hr
  intro γ hγ
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hγ
  have h := Subgroup.mem_iInf.mp (hΛ hc) ⟨z, hz⟩
  change NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ c ∈
      E.lattice.map (MulAut.conj z).toMonoidHom at h
  obtain ⟨v, hv, heq⟩ := Subgroup.mem_map.mp h
  have hconj : z⁻¹ * NilpotentLieBCHGroup.map (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ c * z = v := by
    rw [← heq]
    change z⁻¹ * (z * v * z⁻¹) * z = v
    group
  rw [realificationMap_realificationHom, ← map_inv, ← map_mul, ← map_mul, hconj]
  exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem mapped_normal_conjugation_mem {G H : Type*} [Group G] [Group H]
    (Γ Λ : Subgroup G) (hle : Λ ≤ Γ) (hnormal : (Λ.subgroupOf Γ).Normal)
    (f : G →* H) {κ x : H} (hκ : κ ∈ Γ.map f) (hx : x ∈ Λ.map f) :
    κ * x * κ⁻¹ ∈ Λ.map f := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hκ
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨k * y * k⁻¹,
    (Subgroup.normal_subgroupOf_iff hle).mp hnormal y k hy hk, ?_⟩
  simp only [map_mul, map_inv]

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem normalized_right_compatibility {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) (hq : 0 < q) (Λ : Subgroup D.filtration.Group)
    (hconj : Λ ≤ D.conjugationPullback E φ q) (hle : Λ ≤ D.lattice)
    (hnormal : (Λ.subgroupOf D.lattice).Normal)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice) (r : E.RealGroup)
    (hr : (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q) :
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    ∀ x ∈ Λ.map realificationHom, (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) ∈ E.realLattice := by
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hright := D.real_conjugationPullback_property E φ q hq Λ hconj r hr
  dsimp only
  intro x hx
  have hmem := mapped_normal_conjugation_mem D.lattice Λ hle hnormal realificationHom hκ hx
  have heq : (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) = r⁻¹ * ψ (κ * x * κ⁻¹) * r := by
    simp only [map_mul, map_inv]
    group
  rw [heq]
  exact hright _ hmem

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_coset_map (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∃ (f : Q.Space → E.Space) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (letI := Q.metricSpace; letI := E.metricSpace; LipschitzWith K f) ∧
              ∀ x : Q.RealGroup, f (QuotientGroup.mk x) = QuotientGroup.mk
                (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r) := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + X +
    (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  have hsum : (p + c₀) ^ c₀ + p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcovC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    exact (((le_add_of_nonneg_right hp).trans
      (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg c₁)) _))).trans
      (le_add_of_nonneg_right (sq_nonneg (t + 2)))).trans hsum
  have hcostC : p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    have hc : 0 ≤ (p + c₀) ^ c₀ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c₀)) _
    linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have he : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht he hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht hd he hH (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcovC),
    N, hN, hin, hout, hQ.mono Q hcovC, ?_⟩
  intro a r ha hr
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  let f := frozenCosetMap Q.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r hconj
  have hf : letI := Q.metricSpace; letI := E.metricSpace; LipschitzWith (A * B) f :=
    Q.lipschitz_native_frozenCosetMap E φ a r hconj hBLip ha'
  refine ⟨f, A * B, ?_, hf, fun _ => rfl⟩
  calc
    _ = (A : ℝ) * B := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) :=
      mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le
    _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_map (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∃ h : ∀ γ ∈ Q.realLattice,
                r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice,
              ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q.metricSpace
                 letI := E.metricSpace
                 LipschitzWith K (frozenCosetMap Q.realLattice E.realLattice
                   (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                     (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h)) := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + X +
    (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  have hsum : (p + c₀) ^ c₀ + p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcovC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    exact (((le_add_of_nonneg_right hp).trans
      (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg c₁)) _))).trans
      (le_add_of_nonneg_right (sq_nonneg (t + 2)))).trans hsum
  have hcostC : p + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    have hc : 0 ≤ (p + c₀) ^ c₀ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c₀)) _
    linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have he : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht he hH
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht hd he hH (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcovC),
    N, hN, hin, hout, hQ.mono Q hcovC, ?_⟩
  intro a r ha hr
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  refine ⟨hconj, A * B, ?_, Q.lipschitz_native_frozenCosetMap E φ a r hconj hBLip ha'⟩
  calc
    _ = (A : ℝ) * B := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) :=
      mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le
    _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem realificationMap_id_apply {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (x : D.RealGroup) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x = x := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L) x.coord = x.coord
  generalize x.coord = y
  induction y using TensorProduct.inductionOn with
  | tmul a y => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

theorem exists_uniform_unit_frozen_cover (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d r : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (p : ℝ), 0 ≤ p → R.ComplexityLE p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (R.withLattice Λ N hN hin hout).ComplexityLE ((p + C) ^ C) ∧
          ∀ (V : D.UnitVerticalObservable (R.realSubgroup s r) I p) (a u : D.RealGroup),
            (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun u.coord ∈ realDenominatorGrid q →
            ∃ U : (D.withLattice Λ N hN hin hout).UnitVerticalObservable
                ((R.withLattice Λ N hN hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧ ∀ i x,
                U.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk (a * x * u)) := by
  obtain ⟨b, _, hcover⟩ := exists_uniform_frozen_coset_map s k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d r D R p hp hR q hq hqp
  classical
  have hcost : p + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hbp : 0 ≤ (p + b) ^ b := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hbC : (p + b) ^ b ≤ (p + C) ^ C := by linarith
  have hidheight (i j : Fin d) : rationalLogHeight (D.basis.repr ((LieHom.id : L →ₗ⁅ℚ⁆ L) (D.basis j)) i) ≤ p := by
    change rationalLogHeight (D.basis.repr (D.basis j) i) ≤ p
    by_cases hji : j = i
    · subst i
      simpa [rationalLogHeight] using hp
    · simpa [Basis.repr_self, Finsupp.single_apply, hji, rationalLogHeight] using hp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmaps⟩ :=
    hcover D D (LieHom.id : L →ₗ⁅ℚ⁆ L) p hp hR.1 hR.1 hidheight q hq hqp
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hbC),
    N, hN, hin, hout, R.withLattice_complexity Λ N hN hin hout hR hpC
      (hQ.mono _ hbC), ?_⟩
  intro V a u ha hu
  obtain ⟨f, K, hK, hLip, hf⟩ := hmaps a u ha hu
  have hfid (x : D.RealGroup) : f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * u) := by
    simpa only [D.realificationMap_id_apply] using hf x
  have hVK : ((V.lipBound * K : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (V.lipBound : ℝ) * K := NNReal.coe_mul _ _
      _ ≤ Real.exp p * Real.exp ((p + b) ^ b) :=
        mul_le_mul V.lip_bound hK K.coe_nonneg (Real.exp_pos p).le
      _ = Real.exp (p + (p + b) ^ b) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  let U := V.frozenCover R Λ hΛ N hN hin hout a u f hfid K hLip hpC hVK
  refine ⟨U, rfl, ?_⟩
  intro i x
  exact congrArg (V.observable i) (hfid x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_shared_frozen_unit_observable (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r) {p ε : ℝ},
      0 ≤ p → R.ComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
        (H : Finset G) (a u : G → D.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, (D.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m),
          (R.withLattice Λ m hm hin hout).ComplexityLE ((p + C) ^ C) ∧
          ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (D.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((R.withLattice Λ m hm hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧
              ∀ h ∈ H', ∀ i x, ‖V.observable i (QuotientGroup.mk (a h * x * u h)) -
                U.observable i (QuotientGroup.mk x)‖ ≤ (V.lipBound : ℝ) * ε := by
  obtain ⟨b, _, hselect⟩ := exists_native_frozen_parameter_fiber s k
  obtain ⟨c, _, hcover⟩ := exists_uniform_unit_frozen_cover s k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C b) ^ b + (Polynomial.X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro G L I _ _ _ _ _ _ _ d r D R p ε hp hR hε hεp q hq hqp V H a u hH ha hu hugrid
  have hsum : (p + b) ^ b + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hb : (p + b) ^ b ≤ (p + C) ^ C := by
    have : 0 ≤ (p + c) ^ c := by positivity
    linarith
  have hc : (p + c) ^ c ≤ (p + C) ^ C := by
    have : 0 ≤ (p + b) ^ b := by positivity
    linarith
  obtain ⟨H', hsub, hnonempty, hdense, a₀, u₀, ha₀, _, hu₀, hclose⟩ :=
    hselect D hp hR.1 hε hεp q hq hqp H a u hH ha hu hugrid
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout, hRank, hU⟩ :=
    hcover (I := I) D R p hp hR q hq hqp
  obtain ⟨U, hfreq, hval⟩ := hU V a₀ u₀ ha₀ hu₀
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hc),
    m, hm, hin, hout, hRank.mono _ hc, H', hsub, hnonempty, ?_, U.mono hc, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hb))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh i x
    let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    obtain ⟨hdist, hu⟩ := hclose h hh
    change ‖V.observable i (QuotientGroup.mk (a h * x * u h)) -
      U.observable i (QuotientGroup.mk x)‖ ≤ _
    rw [hval, hu]
    exact (D.frozen_observable_change_left (V.observable i) (V.lipschitz i) (a h) a₀ x u₀).trans
      (mul_le_mul_of_nonneg_left hdist V.lipBound.coe_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem NativeCorrelationStructure.replacedRankResidual_norm_sub_le
    {s r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p F) (hF : ∀ x, ‖F x‖ ≤ 1)
    (h : ZMod N) (c c' : Fin W.family.outputDim → ZMod N → ℂ)
    (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) (x : ZMod N) :
    ‖W.replacedRankResidual h c ij x - W.replacedRankResidual h c' ij x‖ ≤
      ‖c ij.2 x - c' ij.2 x‖ := by
  unfold NativeCorrelationStructure.replacedRankResidual
  rw [← mul_sub, ← star_sub, norm_mul, norm_mul, norm_star, norm_star]
  have hd := multiplicativeDerivative_norm_le_one F hF h x
  have hm := W.mixed.norm_eval ij.1 (fun j => (((correlationInput h x) j).val : ℤ))
  have hmul : ‖multiplicativeDerivative F h x‖ *
      ‖W.mixed.evalCyclic N ij.1 (correlationInput h x)‖ ≤ 1 := by
    exact (mul_le_mul hd hm (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  exact mul_le_of_le_one_left (norm_nonneg _) hmul

theorem exists_native_shared_frozen_correlations (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      0 ≤ P → p ≤ P → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp P →
      ∀ (H : Finset (ZMod N)) (a u : ZMod N → W.family.model.RealGroup)
        (b : ZMod N → ZMod N → W.family.model.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(W.family.model.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((P + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(W.family.model.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((P + 2) ^ k)) →
      (∀ h ∈ H, (W.family.model.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N P
        (W.replacedRankResidual h (fun i x => W.family.vertical.observable i
          (QuotientGroup.mk (a h * b h x * u h)))))) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid m),
          (W.family.rank.withLattice Λ m hm hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (W.family.model.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ m hm hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk (b h x))))) := by
  obtain ⟨a₀, _, hshared⟩ := exists_shared_frozen_unit_observable s k
  let Q : Polynomial ℕ := 3 * Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C a₀) ^ a₀ + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P F W hF hP hpP q hq hqP H a u b hH ha hu hugrid hcorr
  let T := 3 * P + 2
  let ε := Real.exp (-T)
  have hPT : P ≤ T := by dsimp only [T]; linarith
  have hpT : p ≤ T := hpP.trans hPT
  have hT : 0 ≤ T := hP.trans hPT
  have hε : 0 < ε := Real.exp_pos _
  have hεT : 1 / ε ≤ Real.exp T := by simp only [ε, one_div, ← Real.exp_neg, neg_neg, le_refl]
  have hsum : T + (T + a₀) ^ a₀ + 2 ≤ (P + C) ^ C := by
    simpa [Q, T, Polynomial.eval₂_pow] using hbudget P hP
  have hTC : (T + a₀) ^ a₀ ≤ (P + C) ^ C := by linarith
  have hPC : P + 1 ≤ (P + C) ^ C := by
    have : 0 ≤ (T + a₀) ^ a₀ := by positivity
    linarith
  have hbound : Real.exp ((P + 2) ^ k) ≤ Real.exp ((T + 2) ^ k) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, happ⟩ :=
    hshared W.family.model W.family.rank hT (W.family.complexity.mono _ hpT)
      hε hεT q hq (hqP.trans (Real.exp_le_exp.mpr hPT))
      (W.family.vertical.mono hpT) H a u hH
      (fun h hh i => (ha h hh i).trans hbound)
      (fun h hh i => (hu h hh i).trans hbound) hugrid
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hTC),
    m, hm, hin, hout, hRank.mono _ hTC, H', hsub, hnonempty, ?_, U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hTC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    have hprecision : (W.family.vertical.lipBound : ℝ) * ε ≤ Real.exp (-(2 * P)) / 2 := by
      calc
        _ ≤ Real.exp P * ε := mul_le_mul_of_nonneg_right
          (W.family.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP)) hε.le
        _ = Real.exp (-(2 * P) - 2) := by
          dsimp only [ε, T]
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-(2 * P) - 1) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ _ := exp_sub_one_le_half_exp _
    obtain ⟨V⟩ := hcorr h (hsub hh)
    obtain ⟨V'⟩ := V.exists_of_uniform_approx
      (W.replacedRankResidual h (fun i x => (U.mono hTC).observable i (QuotientGroup.mk (b h x))))
      (fun ij x => (W.replacedRankResidual_norm_sub_le hF h _ _ ij x).trans
        ((happ h hh ij.2 (b h x)).trans hprecision))
    exact ⟨V'.mono hPC⟩

end Erdos3

end

end OAI
