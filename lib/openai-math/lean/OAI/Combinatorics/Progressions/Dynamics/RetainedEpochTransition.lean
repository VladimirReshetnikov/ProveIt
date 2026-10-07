import OAI.Combinatorics.Progressions.Lattices.FixedAffineEpochTransition

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_retained_affine_epoch_transition (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ) (p cost : ℝ) (C : ℕ),
      0 ≤ p → RetainedAffineResidueEpoch D ω hF W T A p cost C →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        ∃ (n : ℕ) (_hn : n ≤ d)
          (Q : RationalFilteredNilmanifold
            ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n),
          Q.filtration = E.filtration.quotientTop ∧
          let H := D.filtration.gradedRefiltrationSubalgebra W
          let N := H ⧸ E.filtration.layerIdeal (s + 1)
          let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
          let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
          let := realification_moduleTopology_t2 Q.basis
          ∃ V : RationalFilteredNilmanifold N s n,
            V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
            ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
              DegreeLE (fun _ => 1) s child.log ∧
              FixedAffineEpochTransition D ω hF W T A V child p cost P C B := by
  obtain ⟨B, hB, htransition⟩ := exists_fixed_affine_epoch_transition (s + 1) (by omega)
  refine ⟨B, hB, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF W T A p cost C hp hepoch
  obtain ⟨v, q, P, hP, κ, E, b, R, _, _, _, _, _, hPb, hκ, hprod,
    _, hslow, hgrid, _, _, _, hchild⟩ := hepoch
  obtain ⟨E₀, hE₀, n, hn, Q, hQ, hfixed⟩ := hchild
  refine ⟨P, hP, hPb, E₀, hE₀, n, hn, Q, hQ, ?_⟩
  intro H N _ _ _
  obtain ⟨V, hVF, hVL, hV, child, hdegree, hdescent⟩ := hfixed
  exact ⟨V, hVF, hVL, hV, child, hdegree,
    htransition D V ω hF W T A p cost q P C hP hp E b R κ hκ hprod hgrid hslow child hdescent⟩

end Erdos3

end

end OAI
