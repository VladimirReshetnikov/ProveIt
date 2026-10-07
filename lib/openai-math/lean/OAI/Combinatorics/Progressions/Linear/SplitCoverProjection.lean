import OAI.Combinatorics.Progressions.Estimates.OptionComplementCover

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D E : RationalFilteredNilmanifold L s d)

noncomputable def sublatticeProjection (h : E.lattice ≤ D.lattice) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (MonoidHom.id _) (Subgroup.map_mono h)

@[simp] theorem sublatticeProjection_mk (h : E.lattice ≤ D.lattice) (x : E.RealGroup) :
    sublatticeProjection D E h (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

theorem sublatticeProjection_surjective (h : E.lattice ≤ D.lattice) :
    Function.Surjective (sublatticeProjection D E h) :=
  cosetMap_surjective E.realLattice D.realLattice (MonoidHom.id _) (Subgroup.map_mono h)
    Function.surjective_id

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem sublatticeProjection_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (sublatticeProjection D E h) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1 (MonoidHom.id D.RealGroup) := LipschitzWith.id
  have hc := lipschitz_cosetMap E.realLattice D.realLattice E.realLattice_closed_discrete.1
    D.realLattice_closed_discrete.1 (MonoidHom.id _) (Subgroup.map_mono h) hLip
  change @LipschitzWith E.Space D.Space
    (quotientMetricSpace (E.basis.baseChange ℝ) E.realLattice
      E.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    (quotientMetricSpace (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    1 (sublatticeProjection D E h)
  rw [hb]
  exact hc

theorem sublattice_pullback_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis)
    (u : D.Space → ℂ) {K : ℝ≥0} (hu : letI := D.metricSpace; LipschitzWith K u) :
    letI := E.metricSpace
    LipschitzWith K (u ∘ sublatticeProjection D E h) := by
  let := E.metricSpace
  let := D.metricSpace
  simpa only [mul_one] using hu.comp (sublatticeProjection_lipschitz D E h hb)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (V : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))))
  (hsub : (pi D).lattice ≤ V.lattice)

noncomputable def splitCoverProjection :
    (D none).Space × (pi (fun i => D (some i))).Space → V.Space :=
  sublatticeProjection V (pi D) hsub ∘ (optionProductSpaceEquiv D).symm

theorem splitCoverProjection_surjective : Function.Surjective (splitCoverProjection D V hsub) :=
  (sublatticeProjection_surjective V (pi D) hsub).comp (optionProductSpaceEquiv D).symm.surjective

theorem splitCoverProjection_mk (x : (pi D).RealGroup) :
    splitCoverProjection D V hsub (optionProductSpaceEquiv D (QuotientGroup.mk x)) =
      QuotientGroup.mk x := by
  simp only [splitCoverProjection, Function.comp_apply, Equiv.symm_apply_apply,
    sublatticeProjection_mk]

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

theorem splitCoverProjection_lipschitz (hb : (pi D).basis = V.basis) :
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    letI := V.metricSpace
    LipschitzWith ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)
      (splitCoverProjection D V hsub) := by
  let := (D none).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  let := (pi D).metricSpace
  let := V.metricSpace
  simpa only [one_mul, splitCoverProjection] using
    (sublatticeProjection_lipschitz V (pi D) hsub hb).comp (optionProductSpaceEquiv_symm_lipschitz D)

theorem splitCoverProjection_pullback (hb : (pi D).basis = V.basis)
    (u : V.Space → ℂ) {K : ℝ≥0} (hu : letI := V.metricSpace; LipschitzWith K u)
    (hpositive : ∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) :
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    let v := u ∘ splitCoverProjection D V hsub
    LipschitzWith (K * ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)) v ∧
      (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
      ∀ x : (pi D).RealGroup, v (optionProductSpaceEquiv D (QuotientGroup.mk x)) =
        u (QuotientGroup.mk x) := by
  let := (D none).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  let := V.metricSpace
  exact ⟨hu.comp (splitCoverProjection_lipschitz D V hsub hb),
    fun x => hpositive _, fun x => congrArg u (splitCoverProjection_mk D V hsub x)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
