import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_translationMajorDetectedPotentialData (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ B L ι : Type} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (w : B → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
      {e : ℕ} (D : RationalFilteredNilmanifold L d e),
      let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      ∀ (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : σ => 1))
        (partner : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (η : weightedSubalgebra w d →ₗ[ℚ] ℚ),
        η (centralRationalElement w d hd 1) = 1 →
      ∀ (T : σ → ℝ) (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
        (Fintype.card B : ℝ) ≤ p →
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ p) →
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) T
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            D orbit partner b ω hLayers) p →
      ∃ (l : ℕ) (E P R : N.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : ι → N.filtration.AssociatedGraded)
        (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial B ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
        E * P * R = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          D orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1) T (Real.exp p) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l R ∧
        (∀ t : σ → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : σ => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : σ => 1))
              P.coord)) ∈ realificationLieSubalgebra U) ∧
        U = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ p) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : σ => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤
          Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_associatedGraded_controlled_potential d hd
  refine ⟨C, hC, ?_⟩
  intro σ B L ι _ _ _ _ w hw hwd _ M hM e D N orbit partner b ω hLayers η hη
    T p hp hι hB hb hfactor
  obtain ⟨l, E, P, R, W, v, hl, hlp, hprod, hE, hR, hv, hW, hheight, hkill, hP⟩ := hfactor
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
  have hφ : ∀ j, ∀ x ∈ N.filtration.layer j, φ x ∈ (weightedFiltration w d hwd).layer j :=
    pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
  let U := W.map (weightedTranslationGradedProjection N.filtration w d hw hwd φ hφ)
  have hentries (i : ι) (j : WeightedBasisIndex w d) :
      rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p := by
    have h := productProjection_coordinate_logHeight
      (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (b i) (hb i) true (weightedIndexOrder w d j)
    change rationalLogHeight ((weightedOrderedBasis w d hw).repr (φ (b i))
      (weightedIndexOrder w d j)) ≤ p at h
    have he := weightedOrderedBasis_repr w d hw (φ (b i)) (weightedIndexOrder w d j)
    have he' : (weightedOrderedBasis w d hw).repr (φ (b i)) (weightedIndexOrder w d j) =
        (weightedBasis w d hw).repr (φ (b i)) j :=
      he.trans (congrArg ((weightedBasis w d hw).repr (φ (b i)))
        ((weightedIndexOrder w d).symm_apply_apply j))
    exact he' ▸ h
  have hkill' : ∀ x ∈ W,
      basisGradeProjection (N.filtration.associatedGradedBasis b ω hLayers) ω d x = x →
      N.filtration.gradedFrequency b ω hLayers (η.comp φ.toLinearMap) x = 0 := by
    simpa only [pairFrequency_zero_comp] using hkill
  obtain ⟨V, q, hV, hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential N.filtration b ω hLayers w hw hwd φ hφ W hW v hv p hp hι hB
      hentries hheight η hη hkill'
  refine ⟨l, E, P, R, W, v, U, V, q, hl, hlp, hprod, hE, hR, ?_, rfl, hv, hW, hheight, hP, hV, hderiv,
    hq, hqp, hgrid, hmass, hcoeff⟩
  intro t
  have hm := N.filtration.projected_realSymbolRepresentative_mem_homogeneous_image
    (weightedFiltration w d hwd) b ω hLayers
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ (fun _ : σ => 1) W P.coord hP t
  convert hm using 1
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
