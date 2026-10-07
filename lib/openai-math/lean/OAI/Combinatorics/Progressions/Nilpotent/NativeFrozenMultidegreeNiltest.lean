import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (S : Finset σ)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]

theorem exists_frozen_niltest {n : ℕ}
    (E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
      (multidegreeWeight (retainedCoordinateWeight S) bound) n)
    (hEF : E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S))
    (hEL : E.lattice = D.lattice.comap
      (mapOfSteps (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl))
    (b : σ → ℤ) (p : M.filtration.realification.PolynomialOrbit)
    (u : D.Space → ℂ) (ℓ B : ℝ≥0)
    (hu : letI := D.metricSpace; LipschitzWith ℓ u) (hub : ∀ x, ‖u x‖ ≤ B)
    (a γ : D.RealGroup) (hγ : γ ∈ D.realLattice)
    (hfactor : M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ)
    (A : ℝ≥0) (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (H : ℕ) (he : ∀ i k, RationalHeightLE (D.basis.repr (E.basis i : L) k) H) :
    ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
      T.lipBound = ℓ * (A * coordinateLipschitzBound d n H) ∧
      E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = u (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) p)) := by
  let c := retainedCoordinateWeight S
  let K := M.filtration.weightedSubalgebra c
  let F := M.filtration.weightedFiltration c
  have hΓ : E.lattice ≤ D.lattice.comap (mapOfSteps K.incl) := by rw [hEL]
  let φ : E.RealGroup →* D.RealGroup := realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot) (hM := D.filtration.lowerCentralSeries_eq_bot) K.incl
  have hφ : E.realLattice ≤ D.realLattice.comap φ :=
    realificationMap_subgroup K.incl E.lattice D.lattice hΓ
  let π : E.Space → D.Space := cosetMap E.realLattice D.realLattice φ hφ
  have hπ : letI := E.metricSpace; letI := D.metricSpace
      LipschitzWith (coordinateLipschitzBound d n H) π := by
    let : MetricSpace (E.RealGroup ⧸ E.lattice.map realificationHom) :=
      realificationQuotientMetricSpace E.basis E.lattice E.grid E.grid_pos E.outer_grid
    let : MetricSpace (D.RealGroup ⧸ D.lattice.map realificationHom) :=
      realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
    exact (lipschitz_realificationMap_quotient E.basis D.basis K.incl E.lattice D.lattice hΓ
      E.grid D.grid E.grid_pos D.grid_pos E.outer_grid D.outer_grid H
      (fun k i => he i k)).weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  obtain ⟨q, hq, hval⟩ := M.filtration.exists_real_normalized_frozen_orbit S b p a γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let qE := F.realification.orbitEquivOfEq hF (fun _ : S => 1) q
  have hqE (x : S → ℤ) : E.filtration.realification.polynomialOrbitEval _ x qE =
      F.realification.polynomialOrbitEval _ x q :=
    F.realification.orbitEquivOfEq_eval hF _ q x
  have hvalE (x : S → ℤ) : φ (E.filtration.realification.polynomialOrbitEval _ x qE) =
      a⁻¹ * M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
    rw [hqE]
    exact hval x
  let T : E.Niltest (fun _ : S => 1) :=
    { orbit := qE
      observable := fun x => u (a • π x)
      normBound := B
      lipBound := ℓ * (A * coordinateLipschitzBound d n H)
      norm_le := fun _ => hub _
      lipschitz := by
        let := E.metricSpace
        let := D.metricSpace
        exact hu.comp (hA.comp hπ) }
  refine ⟨T, rfl, rfl, (hqE 0).trans hq, ?_⟩
  intro x
  change u (a • π (QuotientGroup.mk
    (E.filtration.realification.polynomialOrbitEval _ x qE))) = _
  rw [show π (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x qE)) =
      QuotientGroup.mk (φ (E.filtration.realification.polynomialOrbitEval _ x qE)) from rfl, hvalE]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact congrArg u (QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
