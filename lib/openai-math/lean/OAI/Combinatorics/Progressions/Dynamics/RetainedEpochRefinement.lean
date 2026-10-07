import OAI.Combinatorics.Progressions.Lattices.RetainedAffineResidueEpoch

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct

theorem RetainedAffineResidueEpoch.compatible_refinement
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (u : σ → ℤ) (M : ℕ) (hM : 0 < M)
    (A : σ → ℝ) (p cost : ℝ) (C : ℕ)
    (hepoch : RetainedAffineResidueEpoch D ω hF W
      (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))) A p cost C) :
    ∃ (q P : ℕ) (hP : 0 < P) (κ : D.RealGroup)
      (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      0 < q ∧ (q : ℝ) ≤ Real.exp p ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ κ ∈ D.realLattice ∧
      HasFixedAffineResidueChild D W b p q P hP C 1 cost ∧
      ∀ (N : ℕ) (v : σ → ℤ), M ∣ N → (∀ i, v i ≡ u i [ZMOD (M : ℤ)]) →
      ∀ B : σ → ℝ, (∀ i, 0 < B i) →
      (∀ i, |(v i : ℝ) - (u i : ℝ)| ≤ (M : ℝ) * A i) →
      (∀ i, (N : ℝ) * B i ≤ (M : ℝ) * A i) →
      let r : ℚ := (N / M : ℕ)
      let delta : σ → ℚ := fun i => (commonStrideIndex u M v i : ℚ)
      let E' := D.filtration.realification.scalarAffineAdaptedHom r delta E
      let b' := D.filtration.realification.scalarAffineAdaptedHom r delta b
      let R' := D.filtration.realification.scalarAffineAdaptedHom r delta R
      E' * b' * R' * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨(T.scalarAffinePullback (N : ℚ) (fun i => (v i : ℚ))).orbit.log,
          (T.scalarAffinePullback (N : ℚ) (fun i => (v i : ℚ))).orbit.property⟩⟩ ∧
      D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) B (Real.exp (p + 2)) E' ∧
      D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q R' := by
  obtain ⟨v₀, q, P, hP, κ, E, b, R, _, _, _, hq, hqp, hPb, hκ, hprod,
    _, hslow, hgrid, _, _, _, hchild⟩ := hepoch
  refine ⟨q, P, hP, κ, E, b, R, hq, hqp, hPb, hκ, hchild, ?_⟩
  intro N v hMN hv B hB hoffset hspan r delta E' b' R'
  have hbounds := residue_refinement_parameter_bounds u v hM hMN hv A B hoffset hspan
  have horbit : ((T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).scalarAffinePullback r delta).orbit =
      (T.scalarAffinePullback (N : ℚ) (fun i => (v i : ℚ))).orbit :=
    T.scalarAffinePullback_refinement_orbit u v hMN hv
  have hprod' := (T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).scalarAffinePullback_normalized_factorization
    E b R κ hprod r delta
  refine ⟨?_, ?_, ?_⟩
  · simpa only [horbit] using hprod'
  · exact hslow B hB r delta
      (fun i => by simpa only [delta, Rat.cast_intCast] using hbounds.1 i)
      (fun i => by simpa only [r, Rat.cast_natCast] using hbounds.2 i)
  · simpa only [Int.cast_natCast] using D.filtration.polynomialRationalGrid_scalarAffine_integer
      D.basis q R hgrid ((N / M : ℕ) : ℤ) (commonStrideIndex u M v)

end Erdos3

end

end OAI
