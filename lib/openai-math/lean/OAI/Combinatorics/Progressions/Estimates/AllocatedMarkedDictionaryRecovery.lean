/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.NativeOptionProductBudget
import OAI.Combinatorics.Progressions.Estimates.NativeSquareRecovery
import OAI.Combinatorics.Progressions.Linear.FrozenDiagramKernelInvariance

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open scoped TensorProduct

theorem realificationMap_id_eq_changeStep {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s t : ℕ} (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) :
    (realificationMap (hnil := hs) (hM := ht) (LieHom.id : L →ₗ⁅ℚ⁆ L) : _ → _) =
      (changeStep (realification_lowerCentralSeries_eq_bot hs)
        (realification_lowerCentralSeries_eq_bot ht) : _ → _) := by
  funext x
  apply ext
  exact realificationLieHom_id_apply x.coord

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

noncomputable def loweredCoverMap :
    (D.loweredCover hst Λ N hN hin hout).Space →
      ((D.raiseStep hst).withLattice Λ N hN hin hout).Space :=
  cosetMap (D.loweredCover hst Λ N hN hin hout).realLattice
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L) (D.lowerCoverLattice hst Λ) Λ
      (D.lowerCoverLattice_forward hst Λ))

theorem loweredCoverMap_mk (x : (D.loweredCover hst Λ N hN hin hout).RealGroup) :
    D.loweredCoverMap hst Λ N hN hin hout (QuotientGroup.mk x) =
      QuotientGroup.mk (changeStep D.filtration.realification.lowerCentralSeries_eq_bot
        (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot x) := by
  change QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) = _
  rw [realificationMap_id_eq_changeStep]

theorem loweredCoverMap_surjective :
    Function.Surjective (D.loweredCoverMap hst Λ N hN hin hout) := by
  apply cosetMap_surjective
  rw [realificationMap_id_eq_changeStep]
  exact (changeStep _ _).surjective

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem loweredCoverMap_lipschitz :
    letI := (D.loweredCover hst Λ N hN hin hout).metricSpace
    letI := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace
    LipschitzWith 1 (D.loweredCoverMap hst Λ N hN hin hout) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
    rw [realificationMap_id_eq_changeStep]
    exact lipschitz_changeStep (D.basis.baseChange ℝ) _ _
  exact lipschitz_cosetMap (D.loweredCover hst Λ N hN hin hout).realLattice
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice
    (D.loweredCover hst Λ N hN hin hout).realLattice_closed_discrete.1
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice_closed_discrete.1
    _ _ hLip

end Metric

theorem loweredCoverMap_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.loweredCoverMap hst Λ N hN hin hout
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) =
      QuotientGroup.mk ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
        (D.raiseStepRealOrbit hst g)) := by
  rw [D.loweredCoverMap_mk]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L Z : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
  (v : ((D.raiseStep hst).withLattice Λ N hN hin hout).Space × Z → ℂ)

noncomputable def loweredCoverPullback : (D.loweredCover hst Λ N hN hin hout).Space × Z → ℂ :=
  fun y => v (D.loweredCoverMap hst Λ N hN hin hout y.1, y.2)

theorem loweredCoverPullback_mk (x : D.RealGroup) (z : Z) :
    D.loweredCoverPullback hst Λ N hN hin hout v (QuotientGroup.mk x, z) =
      v (QuotientGroup.mk (changeStep D.filtration.realification.lowerCentralSeries_eq_bot
        (D.raiseStep hst).filtration.realification.lowerCentralSeries_eq_bot x), z) := by
  unfold loweredCoverPullback
  rw [D.loweredCoverMap_mk]

theorem loweredCoverPullback_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) (z : Z) :
    D.loweredCoverPullback hst Λ N hN hin hout v
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g), z) =
      v (QuotientGroup.mk ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
        (D.raiseStepRealOrbit hst g)), z) := by
  unfold loweredCoverPullback
  rw [D.loweredCoverMap_orbit]

theorem loweredCoverPullback_bounds
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [PseudoMetricSpace Z]
    {K : ℝ≥0}
    (hv : letI := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace; LipschitzWith K v)
    (hpositive : ∀ y, (v y).im = 0 ∧ 0 ≤ (v y).re ∧ (v y).re ≤ 1) :
    letI := (D.loweredCover hst Λ N hN hin hout).metricSpace
    LipschitzWith K (D.loweredCoverPullback hst Λ N hN hin hout v) ∧
      ∀ y, (D.loweredCoverPullback hst Λ N hN hin hout v y).im = 0 ∧
        0 ≤ (D.loweredCoverPullback hst Λ N hN hin hout v y).re ∧
        (D.loweredCoverPullback hst Λ N hN hin hout v y).re ≤ 1 := by
  let := (D.loweredCover hst Λ N hN hin hout).metricSpace
  let := ((D.raiseStep hst).withLattice Λ N hN hin hout).metricSpace
  have hm := ((D.loweredCoverMap_lipschitz hst Λ N hN hin hout).comp
    (LipschitzWith.prod_fst (β := Z))).prodMk
      (LipschitzWith.prod_snd (α := (D.loweredCover hst Λ N hN hin hout).Space))
  have hpair : LipschitzWith 1 (fun y : (D.loweredCover hst Λ N hN hin hout).Space × Z =>
      (D.loweredCoverMap hst Λ N hN hin hout y.1, y.2)) := by
    simpa only [mul_one, max_self, Function.comp_def] using hm
  refine ⟨?_, fun y => hpositive _⟩
  unfold loweredCoverPullback
  simpa only [mul_one, Function.comp_def] using hv.comp hpair

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_split_reconstruction_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]
      {s : ℕ} {d : Option ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (Λ : Subgroup (pi D).filtration.Group) (m : ℕ) (hm : 0 < m)
      (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Λ)
      (hΛout : bchSubgroupCoordinates (pi D).basis Λ ⊆ denominatorGrid m)
      {p : ℝ}, 0 ≤ p → (Fintype.card (Option ι) : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : Option ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        ∃ _hsub : (pi E).lattice ≤ Λ,
          (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
            ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
            ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
          (pi E).GeometryComplexityLE ((p + C) ^ C) ∧
          (pi (fun i => E (some i))).GeometryComplexityLE ((p + C) ^ C) ∧
          let V := (pi D).withLattice Λ m hm hΛin hΛout
          ∀ (u : V.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := V.metricSpace; LipschitzWith ℓ u) →
            (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
            ∃ (v : (E none).Space × (pi (fun i => E (some i))).Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (letI := (E none).metricSpace
               letI := (pi (fun i => E (some i))).metricSpace
               LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              ∀ x : (pi E).RealGroup,
                v (optionProductSpaceEquiv E (QuotientGroup.mk x)) = u (QuotientGroup.mk x) := by
  obtain ⟨A, _, hcover⟩ := exists_native_factorwise_covers
  obtain ⟨B, _, hmetric⟩ := exists_optionProductMetric_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let P := T + (T + 2) ^ 2 + X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ s d D Λ m hm hΛin hΛout p hp hι hD hmp
  obtain ⟨Δ, N, hN, hin, hout, hindex, hE, hprod, hsub⟩ :=
    hcover D Λ m hm hΛin hp hι hD hmp
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let V := (pi D).withLattice Λ m hm hΛin hΛout
  let t := p + (p + A) ^ A
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hsum : t + (t + 2) ^ 2 + p + (p + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htc : t ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (t + 2), pow_nonneg (show 0 ≤ p + B by positivity) B]
  have hrestc : (t + 2) ^ 2 ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ p + B by positivity) B]
  have hlipc : p + (p + B) ^ B ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (t + 2)]
  have hι' : (Fintype.card ι : ℝ) ≤ t := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hι
    linarith
  have hrest := pi_geometry (fun i => E (some i)) (hp.trans hpt) hι'
    (fun i => (hE (some i)).mono _ hAt)
  refine ⟨Δ, N, hN, hin, hout, hsub, ?_, fun i => (hE i).mono _ (hAt.trans htc),
    hprod.mono _ (hAt.trans htc), hrest.mono _ hrestc, ?_⟩
  · intro i
    obtain ⟨hle, hc, hn, hf, hi⟩ := hindex i
    exact ⟨hle, hc, hn, hf, hi.trans (Real.exp_le_exp.mpr (hAt.trans htc))⟩
  · dsimp only
    intro u ℓ hℓ hu hpositive
    let M := (1 + productMetricBound (fun i => d (some i))) * productMetricBound d
    have hM : (M : ℝ) ≤ Real.exp ((p + B) ^ B) := hmetric d hp hι (fun i => (hD i).1)
    have hK : ((ℓ * M : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
      calc
        _ ≤ Real.exp p * Real.exp ((p + B) ^ B) := by push_cast; gcongr
        _ = Real.exp (p + (p + B) ^ B) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlipc
    obtain ⟨hLip, hunit, heval⟩ := splitCoverProjection_pullback E V hsub rfl u hu hpositive
    exact ⟨u ∘ splitCoverProjection E V hsub, ℓ * M, hK, hLip, hunit, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem exists_lowered_split_reconstruction_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type v} [Fintype ι] [DecidableEq ι]
      {L₀ : Type u} {L : ι → Type u}
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, optionLieSpace L₀ L i))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {s t d₀ : ℕ} {d : ι → ℕ} (Q : RationalFilteredNilmanifold L₀ s d₀) (hst : s ≤ t)
      (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i)),
      let F := optionFactors (Q.raiseStep hst) D
      ∀ (Λ : Subgroup (pi F).filtration.Group) (m : ℕ) (hm : 0 < m)
        (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi F).basis Λ)
        (hΛout : bchSubgroupCoordinates (pi F).basis Λ ⊆ denominatorGrid m) {p : ℝ},
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → Q.GeometryComplexityLE p →
        (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
        ∃ (Δ : ∀ i, Subgroup (F i).filtration.Group) (N : Option ι → ℕ)
          (hN : ∀ i, 0 < N i)
          (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (F i).basis (Δ i))
          (hout : ∀ i, bchSubgroupCoordinates (F i).basis (Δ i) ⊆ denominatorGrid (N i)),
          let E := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
          let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hin none) (hout none)
          ∃ _hsub : (pi E).lattice ≤ Λ,
            (∀ i, Δ i ≤ (F i).lattice ∧ ((Δ i).subgroupOf (F i).lattice).Characteristic ∧
              ((Δ i).subgroupOf (F i).lattice).Normal ∧ ((Δ i).subgroupOf (F i).lattice).FiniteIndex ∧
              ((Δ i).relIndex (F i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            Q'.filtration = Q.filtration ∧ Q'.lattice ≤ Q.lattice ∧
            Q'.GeometryComplexityLE ((p + C) ^ C) ∧
            (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
            (pi (fun i => E (some i))).GeometryComplexityLE ((p + C) ^ C) ∧
            let V := (pi F).withLattice Λ m hm hΛin hΛout
            ∀ (u : V.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := V.metricSpace; LipschitzWith ℓ u) →
              (∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) →
              ∃ (v : Q'.Space × (pi (fun i => E (some i))).Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q'.metricSpace
                 letI := (pi (fun i => E (some i))).metricSpace
                 LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
                ∀ x : (pi E).RealGroup,
                  v (QuotientGroup.mk (changeStep (E none).filtration.realification.lowerCentralSeries_eq_bot
                      Q.filtration.realification.lowerCentralSeries_eq_bot (productProjectionHom E none x)),
                    (optionProductSpaceEquiv E (QuotientGroup.mk x)).2) = u (QuotientGroup.mk x) := by
  obtain ⟨A, _, hsplit⟩ := exists_split_reconstruction_cover
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 1 + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L₀ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s t d₀ d Q hst D F Λ m hm hΛin hΛout p hp hι hQ hD hmp
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := fun i =>
    match i with
    | none => inferInstance
    | some i => inferInstance
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  let : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  let : ∀ i, T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
    intro i
    cases i <;> infer_instance
  have hpp : p ≤ p + 1 := by linarith
  have hF : ∀ i, (F i).GeometryComplexityLE (p + 1) := by
    intro i
    cases i with
    | none => exact (Q.raiseStep_geometry hst hQ).mono _ hpp
    | some i => exact (hD i).mono _ hpp
  obtain ⟨Δ, N, hN, hin, hout, hsub, hindex, hE, _, hrest, hrec⟩ :=
    hsplit F Λ m hm hΛin hΛout (by linarith : 0 ≤ p + 1)
      (by simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]; linarith)
      hF (hmp.trans (Real.exp_le_exp.mpr hpp))
  let E := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hin none) (hout none)
  have hsum : p + (p + 1 + A) ^ A ≤ (p + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) A)).trans hsum
  have hcost : (p + 1 + A) ^ A ≤ (p + C) ^ C := (le_add_of_nonneg_left hp).trans hsum
  have hlow : Q'.GeometryComplexityLE ((p + C) ^ C) :=
    Q.loweredCover_geometry hst (Δ none) (N none) (hN none) (hin none) (hout none) hQ hpC
      ((hE none).2.1.trans (Real.exp_le_exp.mpr hcost))
  refine ⟨Δ, N, hN, hin, hout, hsub, ?_, rfl,
    Q.lowerCoverLattice_le hst (Δ none) (hindex none).1, hlow,
    fun i => (hE i).mono _ hcost, hrest.mono _ hcost, ?_⟩
  · intro i
    obtain ⟨hle, hc, hn, hf, hi⟩ := hindex i
    exact ⟨hle, hc, hn, hf, hi.trans (Real.exp_le_exp.mpr hcost)⟩
  · dsimp only
    intro u ℓ hℓ hu hpositive
    obtain ⟨v, K, hK, hv, hunit, heval⟩ := hrec u ℓ
      (hℓ.trans (Real.exp_le_exp.mpr hpp)) hu hpositive
    let := (pi (fun i => E (some i))).metricSpace
    obtain ⟨hLip, hpos⟩ := Q.loweredCoverPullback_bounds hst (Δ none) (N none)
      (hN none) (hin none) (hout none) v hv hunit
    refine ⟨Q.loweredCoverPullback hst (Δ none) (N none) (hN none) (hin none) (hout none) v,
      K, hK.trans (Real.exp_le_exp.mpr hcost), hLip, hpos, ?_⟩
    intro x
    have h := Q.loweredCoverPullback_mk hst (Δ none) (N none) (hN none) (hin none) (hout none) v
      (changeStep (E none).filtration.realification.lowerCentralSeries_eq_bot
        Q.filtration.realification.lowerCentralSeries_eq_bot (productProjectionHom E none x))
      (optionProductSpaceEquiv E (QuotientGroup.mk x)).2
    apply h.trans
    change v ((optionProductSpaceEquiv E (QuotientGroup.mk x)).1,
      (optionProductSpaceEquiv E (QuotientGroup.mk x)).2) = u (QuotientGroup.mk x)
    simpa only [Prod.mk.eta] using heval x

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem exists_uniform_frozen_split_reconstruction (t k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H M L₀ ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {s e f d₀ : ℕ} {d : ι → ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀) (_hst : s ≤ t)
      (F : ∀ i, RationalFilteredNilmanifold (L i) t (d i))
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i, (F i).GeometryComplexityLE p) →
      (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (ψ₀ (E.basis j)) i) ≤ p) →
      (∀ a i j, rationalLogHeight ((F a).basis.repr (ψ a (E.basis j)) i) ≤ p) →
      Function.Injective (optionProductMap ψ₀ ψ) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      let Z₀ := pi F
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := realification_moduleTopology_t2 Z₀.basis
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ Z : RationalFilteredNilmanifold (∀ i, L i) t (Fintype.card (Σ i, Fin (d i))),
          Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
          Z.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              ∃ (v : Q'.Space × Z.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q'.metricSpace; letI := Z.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
                ∀ x : E.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x),
                    QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := Z.filtration.lowerCentralSeries_eq_bot) (liePiMap ψ) x)) =
                    S (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨A, _, hfrozen⟩ := exists_uniform_frozen_reconstruction t k
  obtain ⟨B, _, hsplit⟩ := exists_lowered_split_reconstruction_cover
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + 3) ^ 2
  let P₁ := P₀ + (P₀ + Polynomial.C A) ^ A
  let P₂ := P₁ + (P₁ + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P₂
  refine ⟨C, hC, ?_⟩
  intro H M L₀ ι _ _ L _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s e f d₀ d E D Q hst F φ ψ₀ ψ p hp hι hE hD hQ hF hφ hψ₀ hψ hψinj q hq hqp
    Z₀
  let T := optionProduct (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := realification_moduleTopology_t2 Z₀.basis
  let Mprod := ∀ i : Option ι, optionLieSpace L₀ L i
  let Aprod := optionFactors (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Mprod)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] Mprod)
  let := realification_moduleTopology_t2 T.basis
  let p₀ := (p + 3) ^ 2
  let p₁ := p₀ + (p₀ + A) ^ A
  have hp₀ : 0 ≤ p₀ := sq_nonneg _
  have hpp₀ : p ≤ p₀ := by dsimp only [p₀]; nlinarith [sq_nonneg p]
  have hp₀p₁ : p₀ ≤ p₁ := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hp₁ : 0 ≤ p₁ := hp₀.trans hp₀p₁
  have hAp₁ : (p₀ + A) ^ A ≤ p₁ := le_add_of_nonneg_left hp₀
  have hsum : p₁ + (p₁ + B) ^ B ≤ (p + C) ^ C := by
    simpa [P₂, P₁, P₀, X, p₀, p₁, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p₁ + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hp₁).trans hsum
  have hT : T.GeometryComplexityLE p₀ :=
    optionProduct_geometry (Q.raiseStep hst) F hp hι (Q.raiseStep_geometry hst hQ) hF
  have hmap : ∀ i j, rationalLogHeight (T.basis.repr (optionProductMap ψ₀ ψ (E.basis j)) i) ≤ p₀ := by
    intro i j
    exact (optionProductMap_logHeight (Q.raiseStep hst) F E.basis ψ₀ ψ hψ₀ hψ i j).trans hpp₀
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin, hout, hV, hrec⟩ :=
    hfrozen E D T φ (optionProductMap ψ₀ ψ) p₀ hp₀ (hE.mono E hpp₀)
      (hD.mono D hpp₀) hT (fun i j => (hφ i j).trans hpp₀) hmap q hq
      (hqp.trans (Real.exp_le_exp.mpr hpp₀))
  obtain ⟨Δ, N, hN, hNin, hNout, _, hindex, hQfil, hQle, hQgeom, _, hZgeom, hsplitrec⟩ :=
    hsplit Q hst F Λ m hm hin hout hp₁ (hι.trans (hpp₀.trans hp₀p₁))
      (hQ.mono Q (hpp₀.trans hp₀p₁))
      (fun i => (hF i).mono (F i) (hpp₀.trans hp₀p₁))
      (hV.2.1.trans (Real.exp_le_exp.mpr hAp₁))
  let G := fun i => (Aprod i).withLattice (Δ i) (N i) (hN i) (hNin i) (hNout i)
  let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hNin none) (hNout none)
  let Z := pi (fun i : ι => G (some i))
  have hZle : Z.lattice ≤ Z₀.lattice := by
    intro x hx
    have hmem := (mem_piBCHSubgroup (fun i : ι => (G (some i)).filtration)
      (fun i : ι => (G (some i)).lattice) x).mp hx
    apply (mem_piBCHSubgroup (fun i : ι => (F i).filtration)
      (fun i : ι => (F i).lattice) x).mpr
    intro i
    exact (hindex (some i)).1 (hmem i)
  refine ⟨Q', hQfil, rfl, hQle, hQgeom.mono Q' hcost,
    Z, rfl, rfl, hZle, hZgeom.mono Z hcost, ?_⟩
  intro a r ha hr S ℓ hℓ hS hpositive
  have hkernel := frozenDiagramKernelInvariance_of_injective E D T φ (optionProductMap ψ₀ ψ)
    hψinj S a r
  have ha₀ : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p₀ + 2) ^ k) := by
    intro i
    exact (ha i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨u, K₀, hK₀, hu, hunit, _, heval⟩ := hrec a r ha₀ hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp₀)) hS hpositive hkernel
  obtain ⟨v, K, hK, hv, hpos, hveval⟩ :=
    hsplitrec u K₀ (hK₀.trans (Real.exp_le_exp.mpr hAp₁)) hu hunit
  refine ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hpos, ?_⟩
  intro x
  let maps := optionMaps ψ₀ ψ
  let y : (pi G).RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi G).filtration.lowerCentralSeries_eq_bot) (liePiMap maps) x
  have hfirst := lowered_productProjectionHom_realificationMap E.filtration G Q maps x
  have hsecond := congrArg Prod.snd (optionProductSpaceEquiv_realificationMap E.filtration G maps x)
  have hargs := congrArg₂ Prod.mk
    (congrArg (QuotientGroup.mk : Q'.RealGroup → Q'.Space) hfirst.symm) hsecond.symm
  exact (congrArg v hargs).trans ((hveval y).trans (heval x))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem exists_diagram_native_external_net (s t k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H M L₀ ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {e f d₀ : ℕ} {d : ι → ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀) (_hst : s ≤ t)
      (F : ∀ i, RationalFilteredNilmanifold (L i) t (d i))
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i, (F i).GeometryComplexityLE p) →
      (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (ψ₀ (E.basis j)) i) ≤ p) →
      (∀ a i j, rationalLogHeight ((F a).basis.repr (ψ a (E.basis j)) i) ≤ p) →
      Function.Injective (optionProductMap ψ₀ ψ) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      let Z₀ := pi F
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := realification_moduleTopology_t2 Z₀.basis
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ Z : RationalFilteredNilmanifold (∀ i, L i) t (Fintype.card (Σ i, Fin (d i))),
          Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
          Z.GeometryComplexityLE ((p + C) ^ C) ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          letI := Q'.metricSpace
          letI := Z.metricSpace
          let diagram := fun x : E.RealGroup =>
            ((QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x) : Q'.Space),
              (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Z.filtration.lowerCentralSeries_eq_bot) (liePiMap ψ) x) : Z.Space))
          ∀ {O R IO : Type*} [Fintype R] [Fintype IO]
            (S : O → D.Space → ℂ) (oc : IO → O) (r : R → D.RealGroup)
            (ℓ B : ℝ≥0) {ε : ℝ},
            (ℓ : ℝ) ≤ Real.exp p → 1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ k) →
            0 < ε → 1 / ε ≤ Real.exp p →
            (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
            (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
            (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
            (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
            (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid q) →
            let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
              (D.basis.baseChange ℝ) B
            let frozen := fun o (a : A) j (x : E.RealGroup) =>
              S o (QuotientGroup.mk (a.val * realificationMap
                (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r j))
            ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ centers : Fin n → Q'.Space → ℂ,
                (∀ i, LipschitzWith K (centers i)) ∧
                (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
                (∀ i y, ‖centers i y‖ ≤ 1) ∧
                (∀ o a j x, positiveImageSlice diagram K (frozen o a j)
                  (diagram x).2 (diagram x).1 = frozen o a j x) ∧
                ∀ o a j z, ∃ i, ∀ y,
                  ‖positiveImageSlice diagram K (frozen o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨A, _, hrec⟩ := exists_uniform_frozen_split_reconstruction t k
  obtain ⟨B, _, hnet⟩ := exists_controlled_native_external_net t t k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A
  let P := R + (R + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro H M L₀ ι _ _ L _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    e f d₀ d E D Q hst F φ ψ₀ ψ p hp hι hE hD hQ hF hφ hψ₀ hψ hinj q hq hqp
  let Z₀ := pi F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom, hrecovery⟩ :=
    hrec E D Q hst F φ ψ₀ ψ hp hι hE hD hQ hF hφ hψ₀ hψ hinj q hq hqp
  let b := (p + A) ^ A
  let p' := p + b
  have hb : 0 ≤ b := pow_nonneg (by positivity) _
  have hpp : p ≤ p' := le_add_of_nonneg_right hb
  have hp' : 0 ≤ p' := hp.trans hpp
  have hbp : b ≤ p' := le_add_of_nonneg_left hp
  have hsum : p' + (p' + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, R, X, p', b, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p' + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hp').trans hsum
  have hpC : p' ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) B)).trans hsum
  let K : ℝ≥0 := ⟨Real.exp b, (Real.exp_pos _).le⟩
  refine ⟨Q', hQF, hQb, hQle, hQgeom.mono Q' (hbp.trans hpC),
    Z, hZF, hZb, hZle, hZgeom.mono Z (hbp.trans hpC),
    K, Real.exp_le_exp.mpr (hbp.trans hpC), ?_⟩
  let := Q'.metricSpace
  let := Z.metricSpace
  intro diagram O J IO _ _ S oc r ℓ Bbox ε hℓ hBbox hBbound hε hεinv hIO hJ hS hpositive hO hr
  have hBp : (Bbox : ℝ) ≤ Real.exp ((p' + 2) ^ k) := hBbound.trans
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  have hexp := Real.exp_le_exp.mpr hpp
  have hconstructed := hnet D Z Bbox K ℓ hp' (hD.mono D hpp) (hZgeom.mono Z hbp)
    hBbox hBp (Real.exp_le_exp.mpr hbp) (hℓ.trans hexp)
    hε (hεinv.trans hexp) (hIO.trans hexp) (hJ.trans hexp)
    S (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) φ) r diagram oc hS hpositive hO
      (fun o a j => by
        obtain ⟨v, K', hK', hv, _, heval⟩ := hrecovery a.val (r j)
          (fun i => (a.property i).trans hBbound) (hr j) (S o) ℓ hℓ (hS o) (hpositive o)
        exact ⟨v, K', hK', hv, heval⟩)
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover⟩ := hconstructed
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr hcost), centers, hLip, hunit, hcap, heval, hcover⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace optionDimension

theorem exists_uniform_frozen_two_target_reconstruction (t k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H M L₀ L₁ : Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
      {s e f d₀ d₁ : ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀) (_hst : s ≤ t)
      (F₁ : RationalFilteredNilmanifold L₁ t d₁)
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ₁ : H →ₗ⁅ℚ⁆ L₁) {p : ℝ},
      1 ≤ p →
      E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      F₁.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (ψ₀ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (F₁.basis.repr (ψ₁ (E.basis j)) i) ≤ p) →
      Function.Injective (optionProductMap ψ₀ (fun _ : Unit => ψ₁)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ F' : RationalFilteredNilmanifold L₁ t d₁,
          F'.filtration = F₁.filtration ∧ F'.basis = F₁.basis ∧ F'.lattice ≤ F₁.lattice ∧
          F'.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              ∃ (v : Q'.Space × F'.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q'.metricSpace; letI := F'.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
                ∀ x : E.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x),
                    QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := F'.filtration.lowerCentralSeries_eq_bot) ψ₁ x)) =
                    S (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨A, _, hfrozen⟩ := exists_uniform_frozen_reconstruction t k
  obtain ⟨B, _, hsplit⟩ := exists_lowered_split_reconstruction_cover
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + 3) ^ 2
  let P₁ := P₀ + (P₀ + Polynomial.C A) ^ A
  let P₂ := P₁ + (P₁ + Polynomial.C B) ^ B + (X + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P₂
  refine ⟨C, hC, ?_⟩
  intro H M L₀ L₁ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s e f d₀ d₁ E D Q hst F₁ φ ψ₀ ψ₁ p hpone hE hD hQ hF₁ hφ hψ₀ hψ₁ hψinj q hq hqp
  have hp : 0 ≤ p := le_trans zero_le_one hpone
  let F := fun _ : Unit => F₁
  let ψ := fun _ : Unit => ψ₁
  have hι : (Fintype.card Unit : ℝ) ≤ p := by simpa using hpone
  have hF : ∀ i, (F i).GeometryComplexityLE p := fun _ => hF₁
  have hψ : ∀ a i j, rationalLogHeight ((F a).basis.repr (ψ a (E.basis j)) i) ≤ p :=
    fun _ => hψ₁
  let Z₀ := pi F
  let T := optionProduct (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Unit → L₁))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (Unit → L₁))
  let := realification_moduleTopology_t2 Z₀.basis
  let Mprod := ∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i
  let Aprod := optionFactors (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Mprod)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] Mprod)
  let := realification_moduleTopology_t2 T.basis
  let p₀ := (p + 3) ^ 2
  let p₁ := p₀ + (p₀ + A) ^ A
  have hp₀ : 0 ≤ p₀ := sq_nonneg _
  have hpp₀ : p ≤ p₀ := by dsimp only [p₀]; nlinarith [sq_nonneg p]
  have hp₀p₁ : p₀ ≤ p₁ := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hp₁ : 0 ≤ p₁ := hp₀.trans hp₀p₁
  have hAp₁ : (p₀ + A) ^ A ≤ p₁ := le_add_of_nonneg_left hp₀
  have hsum : p₁ + (p₁ + B) ^ B + (p + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P₂, P₁, P₀, X, p₀, p₁, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p₁ + B) ^ B ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (p + 2)]
  have htotal : (p₁ + B) ^ B + (p + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hT : T.GeometryComplexityLE p₀ :=
    optionProduct_geometry (Q.raiseStep hst) F hp hι (Q.raiseStep_geometry hst hQ) hF
  have hmap : ∀ i j, rationalLogHeight (T.basis.repr (optionProductMap ψ₀ ψ (E.basis j)) i) ≤ p₀ := by
    intro i j
    exact (optionProductMap_logHeight (Q.raiseStep hst) F E.basis ψ₀ ψ hψ₀ hψ i j).trans hpp₀
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin, hout, hV, hrec⟩ :=
    hfrozen E D T φ (optionProductMap ψ₀ ψ) p₀ hp₀ (hE.mono E hpp₀)
      (hD.mono D hpp₀) hT (fun i j => (hφ i j).trans hpp₀) hmap q hq
      (hqp.trans (Real.exp_le_exp.mpr hpp₀))
  obtain ⟨Δ, N, hN, hNin, hNout, _, hindex, hQfil, hQle, hQgeom, hGgeom, hZgeom, hsplitrec⟩ :=
    hsplit Q hst F Λ m hm hin hout hp₁ (hι.trans (hpp₀.trans hp₀p₁))
      (hQ.mono Q (hpp₀.trans hp₀p₁))
      (fun i => (hF i).mono (F i) (hpp₀.trans hp₀p₁))
      (hV.2.1.trans (Real.exp_le_exp.mpr hAp₁))
  let G := fun i => (Aprod i).withLattice (Δ i) (N i) (hN i) (hNin i) (hNout i)
  let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hNin none) (hNout none)
  let F' : RationalFilteredNilmanifold L₁ t d₁ := G (some ())
  let Z := pi (fun _ : Unit => F')
  refine ⟨Q', hQfil, rfl, hQle, hQgeom.mono Q' hcost,
    F', rfl, rfl, (hindex (some ())).1, (hGgeom (some ())).mono F' hcost, ?_⟩
  intro a r ha hr S ℓ hℓ hS hpositive
  have hkernel := frozenDiagramKernelInvariance_of_injective E D T φ (optionProductMap ψ₀ ψ)
    hψinj S a r
  have ha₀ : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p₀ + 2) ^ k) := by
    intro i
    exact (ha i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨u, K₀, hK₀, hu, hunit, _, heval⟩ := hrec a r ha₀ hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp₀)) hS hpositive hkernel
  obtain ⟨v, K, hK, hv, hpos, hveval⟩ :=
    hsplitrec u K₀ (hK₀.trans (Real.exp_le_exp.mpr hAp₁)) hu hunit
  let := Q'.metricSpace
  let := F'.metricSpace
  let := Z.metricSpace
  let L : ℝ≥0 := max 1 (productMetricBound (fun _ : Unit => d₁))
  let v' : Q'.Space × F'.Space → ℂ := fun z => v (z.1, F'.singletonProductSpace z.2)
  have hmapLip : LipschitzWith L (fun z : Q'.Space × F'.Space =>
      (z.1, F'.singletonProductSpace z.2)) := by
    have h := (LipschitzWith.prod_fst (β := F'.Space)).prodMk
      (F'.singletonProductSpace_lipschitz.comp
        (LipschitzWith.prod_snd (α := Q'.Space)))
    simpa only [mul_one, Function.comp_def, optionDimension, L] using h
  have hL : (L : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    exact max_le (Real.one_le_exp (sq_nonneg _))
      (productMetricBound_singleton_le_exp hp hF₁.1)
  have hKL : (K * L : ℝ≥0) ≤ Real.exp ((p + C) ^ C) := by
    calc
      (K * L : ℝ≥0) = (K : ℝ) * (L : ℝ) := NNReal.coe_mul K L
      _ ≤ Real.exp ((p₁ + B) ^ B) * Real.exp ((p + 2) ^ 2) :=
        mul_le_mul hK hL (NNReal.coe_nonneg L) (Real.exp_nonneg _)
      _ = Real.exp ((p₁ + B) ^ B + (p + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr htotal
  refine ⟨v', K * L, hKL, hv.comp hmapLip, fun z => hpos _, ?_⟩
  intro x
  dsimp only [v', Prod.fst, Prod.snd]
  rw [F'.singletonProductSpace_realificationMap E.filtration ψ₁ x]
  let maps := optionMaps ψ₀ ψ
  let y : (pi G).RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi G).filtration.lowerCentralSeries_eq_bot) (liePiMap maps) x
  have hfirst := lowered_productProjectionHom_realificationMap E.filtration G Q maps x
  have hsecond := congrArg Prod.snd (optionProductSpaceEquiv_realificationMap E.filtration G maps x)
  have hargs := congrArg₂ Prod.mk
    (congrArg (QuotientGroup.mk : Q'.RealGroup → Q'.Space) hfirst.symm) hsecond.symm
  exact (congrArg v hargs).trans ((hveval y).trans (heval x))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

section Conclusion

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]

def AllocatedMarkedDiagramRecoveryCovers (k q : ℕ) (p cost : ℝ) : Prop :=
  ∃ Q' : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ F' : RationalFilteredNilmanifold
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF,
      F'.filtration = Fref.filtration ∧ F'.basis = Fref.basis ∧ F'.lattice ≤ Fref.lattice ∧
      F'.GeometryComplexityLE cost ∧
      let K : ℝ≥0 := ⟨Real.exp cost, (Real.exp_pos _).le⟩
      letI := Q'.metricSpace
      letI := F'.metricSpace
      let diagram := Dref.markedTopQuotientDiagram F'
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q'
      ∀ a r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
        ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
          (letI := D.metricSpace; LipschitzWith ℓ S) →
          (∀ y, (S y).im = 0 ∧ 0 ≤ (S y).re ∧ (S y).re ≤ 1) →
          let frozen := fun x : Dref.RealGroup => S (QuotientGroup.mk
            (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra W).incl x * r))
          ∀ x : Dref.RealGroup,
            positiveImageSlice diagram K frozen (diagram x).2 (diagram x).1 = frozen x

end Conclusion

theorem exists_allocated_marked_diagram_recovery_covers (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type u}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d f nD nF nQ : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (Dref : RationalFilteredNilmanifold
        (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
      (_hDref : Dref.filtration = D.filtration.gradedRefiltration W)
      (Fref : RationalFilteredNilmanifold
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))] {p : ℝ},
      1 ≤ p → Dref.GeometryComplexityLE p → D.GeometryComplexityLE p →
      Q.GeometryComplexityLE p → Fref.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (Dref.basis j : L) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)) (Dref.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Fref.basis.repr
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (Dref.basis j)) i) ≤ p) →
      (∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        AllocatedMarkedDiagramRecoveryCovers D Fmark φ hφ W Dref Fref Q k q p ((p + C) ^ C) := by
  obtain ⟨C, hC, hconstruct⟩ := exists_uniform_frozen_two_target_reconstruction (s + 1) k
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d f nD nF nQ D Fmark φ hφ W Dref hDref Fref Q
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp hDrefGeom hDGeom hQGeom hFrefGeom
    hinc hquot hmark hker q hq hqp
  obtain ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, hrec⟩ :=
    hconstruct Dref D Q (Nat.le_succ s) Fref
      (D.filtration.gradedRefiltrationSubalgebra W).incl
      (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)))
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      hp hDrefGeom hDGeom hQGeom hFrefGeom hinc hquot hmark
      (D.allocatedMarkedDiagram_injective_of_top_kernel Fmark φ hφ W Dref hDref hker)
      q hq hqp
  refine ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, ?_⟩
  let K : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), (Real.exp_pos _).le⟩
  let := Q'.metricSpace
  let := F'.metricSpace
  dsimp only
  intro a r ha hr S ℓ hℓ hS hpositive x
  obtain ⟨v, Lrec, hLrec, hv, _, heval⟩ := hrec a r ha hr S ℓ hℓ hS hpositive
  have hL : Lrec ≤ K := hLrec
  refine positiveImageSlice_eq _ _ _ (fun x => hpositive _) ?_ x
  intro y z
  have h := (hv.weaken hL).dist_le_mul
    (Dref.markedTopQuotientDiagram F'
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q' y)
    (Dref.markedTopQuotientDiagram F'
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q' z)
  simpa only [dist_eq_norm, markedTopQuotientDiagram, heval] using h

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

section Conclusion

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem NativeGridRightDictionary.markedTopQuotient_recovery
    {inputDenominator : ℕ} {bound : ℝ}
    (dictionary : D.NativeGridRightDictionary inputDenominator bound)
    (K : ℝ≥0) (observable : D.Space → ℂ) (a r : D.RealGroup)
    (hr : (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid inputDenominator)
    (hrecovery :
      letI := Q.metricSpace
      letI := Fref.metricSpace
      let diagram := Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
      ∀ j : Fin dictionary.count,
        let frozen := fun source : Dref.RealGroup => observable (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl source * dictionary.representative j))
        ∀ source, positiveImageSlice diagram K frozen
          (diagram source).2 (diagram source).1 = frozen source) :
    letI := Q.metricSpace
    letI := Fref.metricSpace
    let diagram := Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
    let frozen := fun source : Dref.RealGroup => observable (QuotientGroup.mk
      (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source * r))
    ∀ source, positiveImageSlice diagram K frozen
      (diagram source).2 (diagram source).1 = frozen source := by
  let := Q.metricSpace
  let := Fref.metricSpace
  dsimp only at hrecovery ⊢
  obtain ⟨label, hlabel⟩ := dictionary.labeling (fun _ : Unit => r) (fun _ => hr)
  let inclusion : Dref.RealGroup → D.RealGroup :=
    realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl
  have hfrozen : (fun source : Dref.RealGroup => observable (QuotientGroup.mk
        (a * inclusion source * r))) =
      (fun source : Dref.RealGroup => observable (QuotientGroup.mk
        (a * inclusion source * dictionary.representative (label ())))) := by
    funext source
    exact congrArg observable ((hlabel ()).2 (a * inclusion source))
  change ∀ source, positiveImageSlice
    (Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    (fun x => observable (QuotientGroup.mk (a * inclusion x * r)))
    ((Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) source).2
    ((Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) source).1 =
      (fun x => observable (QuotientGroup.mk (a * inclusion x * r))) source
  rw [hfrozen]
  exact hrecovery (label ())

theorem AllocatedMarkedDiagramRecoveryCovers.of_nativeGridRightDictionary
    {inputDenominator k : ℕ} {bound p cost : ℝ}
    (dictionary : D.NativeGridRightDictionary inputDenominator bound)
    (hcovers : AllocatedMarkedDiagramRecoveryCovers D Fmark φ hφ W Dref Fref Q
      k dictionary.denominator p cost) :
    AllocatedMarkedDiagramRecoveryCovers D Fmark φ hφ W Dref Fref Q
      k inputDenominator p cost := by
  obtain ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, hrec⟩ :=
    hcovers
  refine ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, ?_⟩
  let K : ℝ≥0 := ⟨Real.exp cost, (Real.exp_pos _).le⟩
  let := Q'.metricSpace
  let := F'.metricSpace
  dsimp only at hrec ⊢
  intro a r ha hr observable ℓ hℓ hLip hpositive
  apply dictionary.markedTopQuotient_recovery D Fmark φ hφ W Dref F' Q' K
    observable a r hr
  dsimp only
  intro j
  exact hrec a (dictionary.representative j) ha
    (dictionary.representative_bounds j).2 observable ℓ hℓ hLip hpositive

end Conclusion

end Erdos3.RationalFilteredNilmanifold

end

end OAI
