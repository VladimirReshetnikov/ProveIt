import OAI.Combinatorics.Progressions.Dynamics.RetainedEpochRefinement
import OAI.Combinatorics.Progressions.Estimates.AdaptedAnchoredComparison

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_separated_residue_event_or_child (s : ℕ) (hs : 1 ≤ s) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (V : RationalFilteredNilmanifold K t e)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p work q rho : ℝ), 0 ≤ p → p ≤ work → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (q₀ P C a : ℕ) (hP : 0 < P) (cost : ℝ),
      FixedResidueDescent D W V (fun _ : σ => 1) b child work q₀ P hP C a cost →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (E R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
          ⟨⟨T.orbit.log, T.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q₀ R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A (Real.exp ((work + 2) ^ a)) E →
          ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (_hM : 0 < M) (u v : σ → ℤ) (J : σ → ℕ),
          (∀ i, 0 < J i) → ∀ _hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)],
          (∀ i, (M * (M * P)).Coprime (J i)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) →
          ∀ Δ ε δ : ℝ, 0 < δ → δ ≤ 1 → ε < 1 / 2 →
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2 →
          8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ Δ / 4 →
          (∀ i, 8 ≤ δ * (N i : ℝ)) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 →
          Δ ≤ ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ →
          ResiduePairDimensionDrop D ω hF T W lo N M u v J ((q + B) ^ B) ∨
          AnchoredChildResidueComparison V child cost (Δ / 4) δ lo N M P u v J := by
  obtain ⟨B, hB, hstep⟩ := exists_residue_pair_stability_step s hs
  refine ⟨B, hB, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ d t e D V ω hF p work q rho hp hpwork hpq hσ hfreq hrho hrhop
    W b child q₀ P C a hP cost hdesc T hunit hT E R κ hκ hprod hgrid A hA hE
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  rcases hstep D ω hF p q rho hp hpq hσ hfreq hrho hrhop T hunit hT W lo N M u v J
    hM hJ hv hsteplarge with hevent | hprojected
  · exact Or.inl hevent
  · obtain ⟨S, hunitS, hS, hSo, hinvariant, _, hSgap⟩ := hprojected
    have hprodS : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ := by
      simpa only [hSo] using hprod
    have hgapS : Δ / 2 ≤
        ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ := by
      linarith
    simp only [residuePairMean_false, residuePairMean_true] at hgapS
    have hresult := hdesc.half_discrepancy S (hS.mono hpwork) hunitS hinvariant E R κ hκ hprodS hgrid A hA hE
      M hM lo N u v J hJ hv hcop (Δ / 2) ε δ hδ hδone hε
      (by nlinarith : 8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ (Δ / 2) / 2)
      hlarge hphysical hcount hgapS
    obtain ⟨H, hH, hHN, hlower, hupper, k, hk₀, hk₁, U, hU, hunitU, hcostU, hgapU⟩ := hresult
    exact Or.inr (anchored_child_comparison_of_piece V child cost (Δ / 4) δ lo N H hH hHN
      hlower hupper M P hM hP u v J hv hcop k hk₀ hk₁ U hU hunitU hcostU
      (by simpa only [show (Δ / 2) / 2 = Δ / 4 by ring] using hgapU))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

noncomputable def FixedAffineEpochTransition
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
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (work cost : ℝ) (P C B : ℕ) : Prop :=
  ∀ p : ℝ, 0 ≤ p → p ≤ work → ∀ (r : ℤ) (h : σ → ℤ) (A' : σ → ℝ),
    (∀ i, 0 < A' i) → (∀ i, |(h i : ℝ)| ≤ A i) →
    (∀ i, |(r : ℝ)| * A' i ≤ A i) →
    ∀ S : D.Niltest (fun _ : σ => 1),
      S.orbit = D.filtration.realification.scalarAffineOrbitHom (r : ℚ)
        (fun i => (h i : ℚ)) T.orbit →
      S.UnitIntervalValued → S.ComplexityLE p →
      ∀ q rho : ℝ, p ≤ q → (Fintype.card σ : ℝ) ≤ q →
        verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
        ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ), 0 < M →
          ∀ (u v : σ → ℤ) (J : σ → ℕ), (∀ i, 0 < J i) →
          (∀ i, v i ≡ u i [ZMOD (M : ℤ)]) →
          (∀ i, (M * (M * P)).Coprime (J i)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) →
          ∀ Δ ε δ : ℝ, 0 < δ → δ ≤ 1 → ε < 1 / 2 →
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2 →
          8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ Δ / 4 →
          (∀ i, 8 ≤ δ * (N i : ℝ)) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A' i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A' i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 →
          Δ ≤ ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ →
          ResiduePairDimensionDrop D ω hF S W lo N M u v J ((q + B) ^ B) ∨
          AnchoredChildResidueComparison V
            (V.filtration.realification.scalarAffineOrbitHom (r : ℚ) (fun i => (h i : ℚ)) child)
            cost (Δ / 4) δ lo N M P u v J

theorem exists_fixed_affine_epoch_transition (s : ℕ) (hs : 1 ≤ s) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (V : RationalFilteredNilmanifold K t e)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
      (work cost : ℝ) (q₀ P C : ℕ) (hP : 0 < P), 0 ≤ work →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup),
      κ ∈ D.realLattice →
      E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨T.orbit.log, T.orbit.property⟩⟩ →
      D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q₀ R →
      (∀ A' : σ → ℝ, (∀ i, 0 < A' i) → ∀ (r : ℚ) (h : σ → ℚ),
        (∀ i, |(h i : ℝ)| ≤ A i) → (∀ i, |(r : ℝ)| * A' i ≤ A i) →
        D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A' (Real.exp (work + 2))
          (D.filtration.realification.scalarAffineAdaptedHom r h E)) →
      ∀ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      FixedAffineResidueDescent D W V b child work q₀ P hP C 1 cost →
      FixedAffineEpochTransition D ω hF W T A V child work cost P C B := by
  obtain ⟨B, hB, hstep⟩ := exists_separated_residue_event_or_child s hs
  refine ⟨B, hB, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ d t e D V ω hF W T A work cost q₀ P C hP _hwork
    E b R κ hκ hprod hgrid hslow child hchild p hp hpwork r h A' hA' hh hr S hS hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  let E' := D.filtration.realification.scalarAffineAdaptedHom (r : ℚ) (fun i => (h i : ℚ)) E
  let b' := D.filtration.realification.scalarAffineAdaptedHom (r : ℚ) (fun i => (h i : ℚ)) b
  let R' := D.filtration.realification.scalarAffineAdaptedHom (r : ℚ) (fun i => (h i : ℚ)) R
  have horbit : (T.scalarAffinePullback (r : ℚ) (fun i => (h i : ℚ))).orbit = S.orbit := hS.symm
  have hprod' : E' * b' * R' *
      D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ := by
    simpa only [horbit] using T.scalarAffinePullback_normalized_factorization E b R κ hprod
      (r : ℚ) (fun i => (h i : ℚ))
  have hgrid' := D.filtration.polynomialRationalGrid_scalarAffine_integer D.basis q₀ R hgrid r h
  have hslow' := hslow A' hA' (r : ℚ) (fun i => (h i : ℚ))
    (fun i => by simpa only [Rat.cast_intCast] using hh i)
    (fun i => by simpa only [Rat.cast_intCast] using hr i)
  exact hstep D V ω hF p work q rho hp hpwork hpq hσ hfreq hrho hrhop W b'
    (V.filtration.realification.scalarAffineOrbitHom (r : ℚ) (fun i => (h i : ℚ)) child)
    q₀ P C 1 hP cost (hchild r h) S hunit hcost E' R' κ hκ hprod' hgrid' A' hA'
    (by simpa only [pow_one] using hslow') lo N M hM u v J hJ hv hcop hsteplarge
    Δ ε δ hδ hδone hε hprojection hfreezing hlarge hphysical hcount hgap

end Erdos3

end

end OAI
