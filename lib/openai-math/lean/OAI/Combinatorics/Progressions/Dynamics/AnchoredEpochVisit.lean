import OAI.Combinatorics.Progressions.Lattices.FixedAffineEpochTransition

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem FixedAffineEpochTransition.on_anchored_box
    {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1))
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (work cost : ℝ) (P C B : ℕ)
    (lo₀ u₀ : σ → ℤ) (N₀ : σ → ℕ) (M₀ : ℕ) (hM₀ : 0 < M₀)
    (hu₀ : ∀ i, lo₀ i ≤ u₀ i ∧ u₀ i < lo₀ i + N₀ i)
    (htransition : FixedAffineEpochTransition D ω hF W T
      (fun i => (N₀ i : ℝ) / M₀) V child work cost P C B)
    (p : ℝ) (hp : 0 ≤ p) (hpwork : p ≤ work)
    (lo u v : σ → ℤ) (N : σ → ℕ) (M : ℕ) (J : σ → ℕ) (hM : 0 < M)
    (hdiv : M₀ ∣ M) (hucompat : ∀ i, u i ≡ u₀ i [ZMOD (M₀ : ℤ)])
    (hu : ∀ i, lo i ≤ u i ∧ u i < lo i + N i)
    (hsub : ∀ i, lo₀ i ≤ lo i ∧ lo i + N i ≤ lo₀ i + N₀ i)
    (hN : ∀ i, 0 < N i)
    (S : D.Niltest (fun _ : σ => 1))
    (hS : S.orbit = D.filtration.realification.scalarAffineOrbitHom (M / M₀ : ℕ)
      (fun i => (commonStrideIndex u₀ M₀ u i : ℚ)) T.orbit)
    (hunit : S.UnitIntervalValued) (hcost : S.ComplexityLE p)
    (q rho : ℝ) (hpq : p ≤ q) (hσ : (Fintype.card σ : ℝ) ≤ q)
    (hfreq : verticalDecompositionBudget p ≤ q) (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp p)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hcop : ∀ i, (M * (M * P)).Coprime (J i))
    (hsteplarge : ∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ))
    (Δ ε δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : ε < 1 / 2)
    (hprojection : 2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2)
    (hfreezing : 8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ Δ / 4)
    (hlarge : ∀ i, 8 ≤ δ * (N i : ℝ))
    (hcount : (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8)
    (hgap : Δ ≤ ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖) :
    ResiduePairDimensionDrop D ω hF S W lo N M u v J ((q + B) ^ B) ∨
    AnchoredChildResidueComparison V
      (V.filtration.realification.scalarAffineOrbitHom (M / M₀ : ℕ)
        (fun i => (commonStrideIndex u₀ M₀ u i : ℚ)) child)
      cost (Δ / 4) δ lo N M P u v J := by
  obtain ⟨hA, hshift, hscale, hphysical⟩ := anchored_residue_refinement_bounds
    lo₀ lo u₀ u N₀ N hM₀ hM hdiv hucompat hu₀ hsub hu hN
  have h := htransition p hp hpwork ((M / M₀ : ℕ) : ℤ) (commonStrideIndex u₀ M₀ u)
    (fun i => (N i : ℝ) / M) hA hshift
    (fun i => by simpa only [Int.cast_natCast] using hscale i) S
    (by simpa only [Int.cast_natCast] using hS) hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  simpa only [Int.cast_natCast] using h

end Erdos3

end

end OAI
