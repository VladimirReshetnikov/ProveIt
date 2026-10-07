import OAI.Combinatorics.Progressions.Estimates.CappedDistanceReconstruction
import OAI.Combinatorics.Progressions.Linear.SingleRefilteredKernel

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_native_positive_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (E.realLattice ⊓ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
        D.realLattice.map (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ)) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
      (letI := D.metricSpace; LipschitzWith ℓ u) →
      (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
      (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
      ∃ (v : E.Space → ℂ) (K : ℝ≥0),
        (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := E.metricSpace; LipschitzWith K v) ∧
        (∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) ∧ (∀ y, ‖v y‖ ≤ 1) ∧
        ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨c, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ hcover u ℓ hℓ hu hunit hker
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHt : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have ht : 0 ≤ p + 1 := add_nonneg hp zero_le_one
  have hpt : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr hpt
  have hub : ∀ x, ‖u x‖ ≤ (1 : ℝ≥0) := by
    intro x
    rw [← positiveClip_eq_self (u x) (hunit x)]
    exact norm_positiveClip_le_one _
  let := E.metricSpace
  obtain ⟨v, K, hK, hv, _, heval⟩ := hrec D.filtration.lowerCentralSeries_eq_bot
    E.filtration.lowerCentralSeries_eq_bot D.basis E.basis φ D.lattice E.lattice
    D.grid E.grid H D.grid_pos E.grid_pos hH D.outer_grid E.inner_grid E.outer_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (fun i j => rationalHeightLE_ceil_exp (hφ i j)) hcover u hker ℓ 1 hu hub
    (p + 1) ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt)
    hHt (hE.2.1.trans hexp) (hℓ.trans hexp) (by simpa only [NNReal.coe_one] using Real.one_le_exp ht)
  obtain ⟨v', hv', hunit', hcap', heval'⟩ := exists_positive_lipschitz_reconstruction
    (fun x : D.RealGroup => u (QuotientGroup.mk x)) (fun x => hunit (QuotientGroup.mk x))
    (fun x => (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ x) : E.Space)) v hv heval
  have hcost : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨v', K, hK.trans (Real.exp_le_exp.mpr hcost), hv', hunit', hcap', heval'⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_uniform_native_positive_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          let Q := E.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := D.metricSpace; LipschitzWith ℓ u) →
            (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
            (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
              u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
            ∃ (v : Q.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := Q.metricSpace; LipschitzWith K v) ∧
              (∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) ∧ (∀ y, ‖v y‖ ≤ 1) ∧
              ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨a, _, hcover⟩ := exists_native_image_cover s
  obtain ⟨b, _, hrec⟩ := exists_native_positive_reconstruction s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a
  let P := Q + (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hidx, N, hN, hin, hout, hQ, hLift⟩ :=
    hcover D E φ hp hD hE hφ
  let q := p + (p + a) ^ a
  have hpq : p ≤ q := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)
  have hq : 0 ≤ q := hp.trans hpq
  have hBq : (p + a) ^ a ≤ q := le_add_of_nonneg_left hp
  have hbound : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hq (Nat.cast_nonneg b)) _)).trans hbound
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hidx.trans (Real.exp_le_exp.mpr (hBq.trans hqC)), N, hN, hin, hout,
    hQ.mono _ (hBq.trans hqC), ?_⟩
  intro u ℓ hℓ hu hunit hker
  obtain ⟨v, K, hK, hv, hunit', hcap, heval⟩ := hrec D (E.withLattice Λ N hN hin hout) φ hq
    (hD.mono D hpq) (hQ.mono _ hBq) (fun i j => (hφ i j).trans hpq) hLift
    u ℓ (hℓ.trans (Real.exp_le_exp.mpr hpq)) hu hunit hker
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hunit', hcap, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_immersion_local_inverse (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M), Function.Injective φ → ∀ {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          let Q := E.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := D.metricSpace
          letI := Q.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ x y : D.RealGroup,
            dist (QuotientGroup.mk (ψ x) : Q.Space) (QuotientGroup.mk (ψ y)) <
              Real.exp (-((p + C) ^ C)) →
            dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk y) ≤
              Real.exp ((p + C) ^ C) *
                dist (QuotientGroup.mk (ψ x) : Q.Space) (QuotientGroup.mk (ψ y)) := by
  obtain ⟨C, hC, hreconstruct⟩ := exists_uniform_native_positive_reconstruction s
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ hφ p hp hD hE hheight
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hrec⟩ :=
    hreconstruct D E φ hp hD hE hheight
  let Q := E.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hψ : Function.Injective ψ := by
    let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
    have hf := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) φ.toLinearMap hφ
    intro x y hxy
    apply NilpotentLieBCHGroup.ext
    exact hf (congrArg NilpotentLieBCHGroup.coord hxy)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, ?_⟩
  let := D.metricSpace
  let := Q.metricSpace
  let K : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), (Real.exp_pos _).le⟩
  have hcapped : ∀ a : D.Space, ∃ (v : Q.Space → ℂ) (B : ℝ≥0), B ≤ K ∧
      LipschitzWith B v ∧ ∀ x : D.RealGroup,
        v (QuotientGroup.mk (ψ x)) = cappedDistanceTest a (QuotientGroup.mk x) := by
    intro a
    obtain ⟨v, B, hB, hv, _, _, heval⟩ := hrec (cappedDistanceTest a) 1
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
      (cappedDistanceTest_lipschitz a) (cappedDistanceTest_unit_interval a) (by
        intro k hk x
        have hk1 : k = 1 := hψ ((MonoidHom.mem_ker.mp hk).trans (map_one ψ).symm)
        simp only [hk1, one_mul])
    exact ⟨v, B, hB, hv, heval⟩
  dsimp only
  intro x y hnear
  apply local_dist_le_of_positive_reconstruction
    (fun x : D.RealGroup => (QuotientGroup.mk x : D.Space))
    (fun x : D.RealGroup => (QuotientGroup.mk (ψ x) : Q.Space)) K hcapped x y
  change Real.exp ((p + C) ^ C) *
    dist (QuotientGroup.mk (ψ x) : Q.Space) (QuotientGroup.mk (ψ y)) < 1
  calc
    _ < Real.exp ((p + C) ^ C) * Real.exp (-((p + C) ^ C)) :=
      mul_lt_mul_of_pos_left hnear (Real.exp_pos ((p + C) ^ C))
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_positive_frozen_observable (s k : ℕ) :
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
            ∀ (u : E.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := E.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              ∃ (v : Q.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := Q.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : Q.RealGroup, v (QuotientGroup.mk x) = u (QuotientGroup.mk
                  (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
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
  intro a r ha hr u ℓ hℓ hu hunit
  have hconj := D.real_conjugationPullback_property E φ q hq Λ htarget r hr
  have ha' : LipschitzWith A (fun x => a * x) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) _)))
  obtain ⟨v, hv, hunitv, hcap, heval⟩ :=
    Q.exists_positive_frozen_observable E φ a r hconj hBLip ha' u hu hunit
  refine ⟨v, ℓ * (A * B), ?_, hv, hunitv, hcap, heval⟩
  calc
    _ = (ℓ : ℝ) * ((A : ℝ) * B) := by simp only [NNReal.coe_mul]
    _ ≤ Real.exp p * (Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2)) :=
      mul_le_mul hℓ (mul_le_mul hA hB B.coe_nonneg (Real.exp_pos _).le)
        (mul_nonneg A.coe_nonneg B.coe_nonneg) (Real.exp_pos p).le
    _ = Real.exp (p + (t + c₁) ^ c₁ + (t + 2) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hcostC

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M N : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] N)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] N)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] N)] [T2Space (ℝ ⊗[ℚ] N)]
      {d e f : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (T : RationalFilteredNilmanifold N s f) (φ : L →ₗ⁅ℚ⁆ M) (ψ : L →ₗ⁅ℚ⁆ N) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p → T.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (T.basis.repr (ψ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
        (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
        (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (B : ℕ) (hB : 0 < B)
          (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
          (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
          let V := T.withLattice Λ B hB hin hout
          V.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : E.RealGroup,
            (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (u : E.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := E.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              (∀ z ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x : D.RealGroup,
                u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
                u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r))) →
              ∃ (v : V.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := V.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : D.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := T.filtration.lowerCentralSeries_eq_bot) ψ x)) =
                  u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨a₀, _, hfreeze⟩ := exists_uniform_positive_frozen_observable s k
  obtain ⟨b₀, _, hrec⟩ := exists_uniform_native_positive_reconstruction s
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C a₀) ^ a₀
  let P := R + (R + Polynomial.C b₀) ^ b₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e f D E T φ ψ p hp hD hE hT hφ hψ q hq hqp
  obtain ⟨Γ, _, _, _, _, _, A, hA, hAin, hAout, hQ, hfrozen⟩ :=
    hfreeze D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Γ A hA hAin hAout
  let t := p + (p + a₀) ^ a₀
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a₀)) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hQt : (p + a₀) ^ a₀ ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + b₀) ^ b₀ ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (t + b₀) ^ b₀ ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hBin, hBout, hV, hreconstruct⟩ :=
    hrec Q T ψ ht (hQ.mono Q hQt) (hT.mono T hpt) (fun i j => (hψ i j).trans hpt)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcost),
    B, hB, hBin, hBout, hV.mono _ hcost, ?_⟩
  intro a r ha hr u ℓ hℓ hu hunit hkernel
  obtain ⟨w, K₀, hK₀, hw, hunitw, _, hevalw⟩ := hfrozen a r ha hr u ℓ hℓ hu hunit
  have hker : ∀ z ∈ (realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
      (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x,
      w (QuotientGroup.mk (z * x)) = w (QuotientGroup.mk x) := by
    intro z hz x
    rw [hevalw, hevalw]
    exact hkernel z hz x
  obtain ⟨v, K, hK, hv, hunitv, hcap, hevalv⟩ := hreconstruct w K₀
    (hK₀.trans (Real.exp_le_exp.mpr hQt)) hw hunitw hker
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hunitv, hcap,
    fun x => (hevalv x).trans (hevalw x)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded),
      let H := (pi D).filtration.gradedRefiltrationSubalgebra W
      ∀ {e n : ℕ} (E : RationalFilteredNilmanifold H (s + 1) e)
        (Q : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n),
      let N := ∀ j : Option {i : ι // i ≠ a},
        optionLieSpace (H ⧸ E.filtration.layerIdeal (s + 1)) (fun i : {i : ι // i ≠ a} => L i.val) j
      ∀ [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
        [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
        [TopologicalSpace (ℝ ⊗[ℚ] N)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] N)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] N)] [T2Space (ℝ ⊗[ℚ] N)] (p : ℝ),
      let T := nativeRefilteredTarget D a W E Q
      E.filtration = (pi D).filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → (D a).GeometryComplexityLE p → T.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((D a).basis.repr (refilteredComponentMap D W a (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (T.basis.repr (nativeRefilteredMap D a W E (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
        (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
        (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (B : ℕ) (hB : 0 < B)
          (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
          (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
          let V := T.withLattice Λ B hB hin hout
          V.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ {J : Type*} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
            (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
              realifyFunctional (piFrequency (eta j)) x = 0) →
            ∀ l r : (D a).RealGroup,
              (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
              ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
                (letI := (D a).metricSpace; LipschitzWith ℓ S) →
                (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
                (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
                ∃ (v : V.Space → ℂ) (K : ℝ≥0),
                  (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := V.metricSpace; LipschitzWith K v) ∧
                  (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                  ∀ x : E.RealGroup,
                    v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := T.filtration.lowerCentralSeries_eq_bot) (nativeRefilteredMap D a W E) x)) =
                    S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a) x * r)) := by
  obtain ⟨C, hC, hrec⟩ := exists_uniform_frozen_reconstruction (s + 1) k
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a W H e n E Q N _ _ _ _ _ _ _ _ _ _ _ _ p T hEF hp hE hD hT hφ hψ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, hfrozen⟩ :=
    hrec E (D a) (nativeRefilteredTarget D a W E Q)
      (refilteredComponentMap D W a) (nativeRefilteredMap D a W E)
      p hp hE hD hT hφ hψ q hq hqp
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, ?_⟩
  intro J eta hfrequency l r hl hr S ℓ hℓ hS hunit hinvariant
  apply hfrozen l r hl hr S ℓ hℓ hS hunit
  intro z hz x
  apply native_refiltered_frozen_invariant D a W E Q hEF eta S hinvariant hfrequency l r z x
  exact congrArg NilpotentLieBCHGroup.coord (MonoidHom.mem_ker.mp hz)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let T := nativeRefilteredTarget D a W E Q
  let N := ∀ j : Option {i : ι // i ≠ a}, optionLieSpace
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1))
    (fun i : {i : ι // i ≠ a} => L i.val) j
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  letI := realification_moduleTopology_t2 T.basis
  ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
    (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
    (Λ.subgroupOf T.lattice).FiniteIndex ∧
    (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
    ∃ (B : ℕ) (hB : 0 < B)
      (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
      (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
      let V := T.withLattice Λ B hB hin hout
      V.GeometryComplexityLE cost ∧
      ∀ {J : Type u} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (eta j)) x = 0) →
        ∀ l r : (D a).RealGroup,
          (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := (D a).metricSpace; LipschitzWith ℓ S) →
            (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
            (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
            ∃ (v : V.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp cost ∧
              (letI := V.metricSpace; LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              (∀ x, ‖v x‖ ≤ 1) ∧ ∀ x : E.RealGroup,
              v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := T.filtration.lowerCentralSeries_eq_bot) (nativeRefilteredMap D a W E) x)) =
              S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := (D a).filtration.lowerCentralSeries_eq_bot)
                (refilteredComponentMap D W a) x * r))

theorem RefilteredRecoveryFamily.mono {p p' cost cost' : ℝ} {q k : ℕ}
    (h : RefilteredRecoveryFamily D a W E Q p q k cost)
    (hp' : 0 ≤ p') (hpp : p' ≤ p) (hc : cost ≤ cost') :
    RefilteredRecoveryFamily D a W E Q p' q k cost' := by
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, hfrozen⟩ := h
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hc),
    B, hB, hin, hout, hV.mono _ hc, ?_⟩
  intro J eta hfrequency l r hl hr S ℓ hℓ hS hunit hinvariant
  have hl' : ∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k) := by
    intro i
    exact (hl i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨v, K, hK, hv, hunitv, hcap, heval⟩ := hfrozen eta hfrequency l r hl' hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp)) hS hunit hinvariant
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hc), hv, hunitv, hcap, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def LowerRefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I, L i.val) (s + 1)
        (Fintype.card (Σ i : I, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      ∀ {J : Type u} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (eta j)) x = 0) →
        ∀ l r : (D a).RealGroup,
          (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := (D a).metricSpace; LipschitzWith ℓ S) →
            (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
            (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
            ∃ (v : Q'.Space × Z.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp cost ∧
              (letI := Q'.metricSpace; letI := Z.metricSpace; LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              ∀ x : E.RealGroup,
                v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := Q'.filtration.lowerCentralSeries_eq_bot)
                    (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x),
                  QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := Z.filtration.lowerCentralSeries_eq_bot)
                    (liePiMap (fun i : I => refilteredComponentMap D W i.val)) x)) =
                  S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := (D a).filtration.lowerCentralSeries_eq_bot)
                    (refilteredComponentMap D W a) x * r))

theorem LowerRefilteredRecoveryFamily.mono_cost {p cost cost' : ℝ} {q k : ℕ}
    (h : LowerRefilteredRecoveryFamily D a W E Q p q k cost) (hc : cost ≤ cost') :
    LowerRefilteredRecoveryFamily D a W E Q p q k cost' := by
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hrec⟩ := h
  refine ⟨Q', hQF, hQb, hQle, hQ.mono Q' hc, Z, hZF, hZb, hZle, hZ.mono Z hc, ?_⟩
  intro J eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  obtain ⟨v, K, hK, hv, hpos, heval⟩ := hrec eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hc), hv, hpos, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_uniform_refilteredRecoveryFamily (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      (p : ℝ),
      E.filtration = (pi D).filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → (D a).GeometryComplexityLE p →
      (nativeRefilteredTarget D a W E Q).GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((D a).basis.repr (refilteredComponentMap D W a (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight ((nativeRefilteredTarget D a W E Q).basis.repr
        (nativeRefilteredMap D a W E (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      RefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  obtain ⟨C, hC, hrec⟩ := exists_uniform_refiltered_reconstruction s k
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a _ _ _ _ W e n E Q p hEF hp hE hD hT hφ hψ q hq hqp
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let N := ∀ j : Option {i : ι // i ≠ a}, optionLieSpace
    (H ⧸ E.filtration.layerIdeal (s + 1)) (fun i : {i : ι // i ≠ a} => L i.val) j
  let T := nativeRefilteredTarget D a W E Q
  let := moduleTopology ℝ (ℝ ⊗[ℚ] H)
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] H)
  let := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 T.basis
  exact hrec D a W E Q p hEF hp hE hD hT hφ hψ q hq hqp

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def LowerRefilteredCyclicExpansionSpec
    (p : ℝ) (q k : ℕ) (cost : ℝ) (C : ℕ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
        (Fintype.card (Σ i : I₀, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      letI := Z.metricSpace
      let w := fun _ : Unit => 1
      let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
      let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Z.filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
      ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (freq j)) x = 0) →
        ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
          (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) {ρ η : ℝ},
          0 < ρ → 0 ≤ η →
          (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
          (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
          ∀ (S : ZMod N → (D a).Niltest w),
            (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
            (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (freq j a) z.coord = 0) →
              ∀ x, (S h).observable (z • x) = (S h).observable x) →
            ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
              (κ : ZMod N → (D a).RealGroup)
              (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
              (∀ h, κ h ∈ (D a).realLattice) →
              (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
              (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ k)) (slow h)) →
              (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
              ∀ (anchor : I → ZMod N → ℝ) (r₀ : I → ZMod N → (D a).RealGroup),
                (∀ i h, |anchor i h| ≤ N) →
                (∀ i h b, |((D a).basis.baseChange ℝ).repr
                  ((D a).filtration.adaptedPolynomialRealValueHom w (fun _ => anchor i h) (slow h)).coord b| ≤
                    Real.exp ((p + 2) ^ k)) →
                (∀ i h, ((D a).basis.baseChange ℝ).equivFun (r₀ i h).coord ∈ realDenominatorGrid q) →
                (∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
                  |(x.val : ℝ) - anchor i h| ≤ (N : ℝ) * ρ) →
                (∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
                  (QuotientGroup.mk ((D a).filtration.adaptedPolynomialRealValueHom w
                    (fun _ => (x.val : ℝ)) (rat h)) : (D a).Space) = QuotientGroup.mk (r₀ i h)) →
                (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                  0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                  dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                    (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
                    (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                      (fun _ => (y.val : ℤ)) (g h)))) ≤ η) →
                ∃ U : I → J → ZMod N → Q'.Niltest w,
                  (∀ i j h, (U i j h).UnitIntervalValued) ∧
                  (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                  (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                    ∀ x, (U i j h).eval x = 0) ∧
                  ∃ err : ZMod N → ZMod N → ℝ,
                    (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                      (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                    ∀ h, (𝔼 x, |err h x|) ≤
                      Real.exp ((p + C) ^ C) * ρ + Real.exp cost * η + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

theorem exists_lower_refiltered_cyclic_expansion (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
      {p cost : ℝ} {q : ℕ}, 1 ≤ p → 0 ≤ cost → Q.filtration = E.filtration.quotientTop →
      LowerRefilteredRecoveryFamily D a W E Q p q k cost →
      LowerRefilteredCyclicExpansionSpec D a W E Q p q k cost C := by
  obtain ⟨C, hC, hfreeze⟩ := Niltest.exists_slow_factor_freezing (s + 1) k
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a W e n E Q _ _ _ _ p cost q hp hcost hquot hrec
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hreconstruct⟩ := hrec
  refine ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, ?_⟩
  let := Q'.metricSpace
  let := Z.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B ρ η hρ hη hA hB hAsum hBsum
    S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hmiddle
    anchor r₀ hanchor hleft hright hnear hrat hdiam
  let w := fun _ : Unit => 1
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
  let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot)
    (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
  let qg := fun h => E.topQuotientOrbit Q' (hQF.trans hquot) (g h)
  let left := fun i h => (D a).filtration.adaptedPolynomialRealValueHom w
    (fun _ => anchor i h) (slow h)
  have hLip (h : ZMod N) : ((S h).lipBound : ℝ) ≤ Real.exp p := by
    have hb := Niltest.observable_budget (hS h)
    linarith [(S h).normBound.coe_nonneg]
  have hex (i : I) (h : ZMod N) := hreconstruct freq hfreq (left i h) (r₀ i h)
    (hleft i h) (hright i h) (S h).observable (S h).lipBound (hLip h)
    (S h).lipschitz (hpositive h) (hinvariant h)
  choose v K hK hv hpos heval using hex
  let bound : ℝ≥0 := ⟨Real.exp cost, (Real.exp_pos cost).le⟩
  let F := fun i h (z : Q'.Space) (a : Z.Space) => (v i h (z, a)).re
  have hF (i : I) (h : ZMod N) (z : Q'.Space) (a : Z.Space) :
      0 ≤ F i h z a ∧ F i h z a ≤ 1 := (hpos i h (z, a)).2
  have hvbound (i : I) (h : ZMod N) : LipschitzWith bound (v i h) :=
    (hv i h).weaken (hK i h)
  have hFirst (i : I) (h : ZMod N) (a : Z.Space) : LipschitzWith bound (fun z => F i h z a) := by
    simpa only [F, one_mul, mul_one, Function.comp_def, RCLike.re_eq_complex_re] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp ((hvbound i h).comp (LipschitzWith.prodMk_right a))
  have hSecond (i : I) (h : ZMod N) (z : Q'.Space) : LipschitzWith bound (F i h z) := by
    simpa only [F, one_mul, mul_one, Function.comp_def, RCLike.re_eq_complex_re] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp ((hvbound i h).comp (LipschitzWith.prodMk_left z))
  have hbudget : Real.log (3 + (bound : ℝ)) ≤ cost + 2 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp cost := Real.one_le_exp hcost
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    change 3 + Real.exp cost ≤ Real.exp (cost + 2)
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg cost)]
  let xi : ZMod N → ZMod N → Z.Space := fun h x =>
    QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w (fun _ => (x.val : ℤ)) (g h)))
  let target := fun h x => ((S h).evalCyclic N (fun _ => x)).re
  have htarget (h x : ZMod N) : 0 ≤ target h x ∧ target h x ≤ 1 :=
    (hpositive h _).2
  have happrox (i : I) (h x : ZMod N) (hx : x ∉ cyclicWrapExceptional h ρ) (hAx : 0 < A i x) :
      |target h x - F i h (Q'.cyclicOrbitPoint (qg h) N (fun _ => x)) (xi h x)| ≤
        Real.exp ((p + C) ^ C) * ρ := by
    have hxN : |((x.val : ℤ) : ℝ)| ≤ (N : ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (Nat.le_of_lt (ZMod.val_lt x))
    have hfrozen := hfreeze (D a) w (fun _ => by decide) p (by linarith)
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) (S h) (hS h)
      (slow h) (middle h) (rat h) (κ h) (hκ h) (hfactor h) (fun _ => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (hslow h)
      (fun _ => (x.val : ℤ)) (fun _ => anchor i h) (r₀ i h) ρ hρ.le
      (fun _ => hxN) (fun _ => hanchor i h)
      (fun _ => by simpa only [Int.cast_natCast] using hnear i h x hx hAx)
      (by simpa only [Int.cast_natCast] using hrat i h x hx hAx)
    have hsection := heval i h
      (E.filtration.realification.polynomialOrbitEval w (fun _ => (x.val : ℤ)) (g h))
    have hreal : F i h (Q'.cyclicOrbitPoint (qg h) N (fun _ => x)) (xi h x) =
        ((S h).observable (QuotientGroup.mk (left i h *
          (D a).filtration.adaptedPolynomialRealValueHom w (fun _ => ((x.val : ℤ) : ℝ)) (middle h) * r₀ i h))).re := by
      dsimp only [F, qg, xi]
      rw [E.topQuotientOrbit_cyclicOrbitPoint]
      rw [hmiddle h (fun _ => (x.val : ℤ))]
      exact congrArg Complex.re hsection
    rw [hreal]
    exact (Complex.abs_re_le_norm _).trans hfrozen
  obtain ⟨U, hU, hUcomplexity, hUempty, _, err, herr, hmean⟩ :=
    exists_cyclic_cellwise_niltest_approximation N (fun _ => Q') qg F A B xi target
      hρ (by positivity) hη hA hB hAsum hBsum hF hFirst hSecond
      (fun _ => hQ.mono Q' (by linarith)) hbudget htarget happrox hdiam
  exact ⟨U, hU, hUcomplexity, hUempty, err, herr, hmean⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
