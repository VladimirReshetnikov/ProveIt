import OAI.Combinatorics.Progressions.Lattices.FixedAffineEpochTransition

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ L K : Type*} [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}

theorem FixedAffineEpochTransition.rebase_child
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
    (V : RationalFilteredNilmanifold K t e) (F : V.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (V.basis.repr (F.basis i) j) H)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (work cost cost' : ℝ) (P C B : ℕ)
    (hcomplex : ∀ U : V.Niltest (fun _ : σ => 1), U.ComplexityLE cost →
      (F.rebaseNiltest H hH U).ComplexityLE cost')
    (htransition : FixedAffineEpochTransition D ω hF W T A V child work cost P C B) :
    FixedAffineEpochTransition D ω hF W T A F.model child work cost' P C B := by
  intro p hp hpwork r h A' hA' hh hr S hS hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  rcases htransition p hp hpwork r h A' hA' hh hr S hS hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap with hevent | hchild
  · exact Or.inl hevent
  · exact Or.inr (hchild.rebase V F H hH _ cost cost' (Δ / 4) δ lo N M P u v J hcomplex)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_controlled_adapted_epoch_child :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
      (V : RationalFilteredNilmanifold K t e)
      (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
      (work cost : ℝ) (P C B : ℕ), 0 ≤ cost → V.GeometryComplexityLE cost →
      FixedAffineEpochTransition D ω hF W T A V child work cost P C B →
      ∃ F : V.AdaptedModelData,
        finrank ℚ K = e ∧ F.model.GeometryComplexityLE ((cost + R) ^ R) ∧
        FixedAffineEpochTransition D ω hF W T A F.model child work ((cost + R) ^ R) P C B := by
  obtain ⟨R, hR, hrebase⟩ := exists_controlled_adapted_rebase
  refine ⟨R, hR, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ s d t e D ω hF W T A V child work cost P C B
    hcost hV htransition
  obtain ⟨F, H, hH, _, hgeom, hcomplex, _⟩ := hrebase V hcost hV
  refine ⟨F, ?_, hgeom, ?_⟩
  · simpa only [Fintype.card_fin] using finrank_eq_card_basis V.basis
  · exact htransition.rebase_child D ω hF W T A V F H hH child work cost ((cost + R) ^ R)
      P C B (fun U hU => hcomplex U hU)

end Erdos3

end

end OAI
