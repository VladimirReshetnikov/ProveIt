import OAI.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartKeepBounds
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialSliceInterpolation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

attribute [local irreducible] realChartSubstitute

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

theorem mark_log_on_slice (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    eval₂ (fun i => (u i : ℝ))
      (map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) candidate.orbit.log) =
    eval₂ (fun i => (u i : ℝ))
      (realChartSubstitute (integerSampledRealChart C.integerChart) marked.log) := by
  have he := candidate.mark_on_slice u hu
  rw [← D.filtration.realification.polynomialOrbitRealEval_integer _ candidate.orbit u,
    ← Fmark.realification.polynomialOrbitRealEval_integer _ marked (C.chartValues u)] at he
  have hc := congrArg NilpotentLieBCHGroup.coord he
  rw [eval₂_map, eval₂_realChartSubstitute]
  refine hc.trans ?_
  apply congrArg (fun z => eval₂ z marked.log)
  funext i
  exact (integerSampledRealChart_eval C.integerChart u i).symm

private theorem chart_mark_degreeLE :
    DegreeLE (fun _ : C.Variables => 1) t
      (realChartSubstitute (integerSampledRealChart C.integerChart) marked.log) :=
  Fmark.realification.adapted_degreeLE _
    (Fmark.adapted_realChartSubstitute_weightedSupport
      (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support marked.adapted)

theorem formal_mark (hlength : ∀ i, max s t < C.slice.length i) :
    map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) candidate.orbit.log =
      realChartSubstitute (integerSampledRealChart C.integerChart) marked.log := by
  refine eq_of_eval₂_eq_on_residueBoxSlice C.slice C.step_pos ?_ ?_ hlength ?_
  · intro α hα
    exact (candidate.orbit.degreeLE.map _ ) α ((le_max_left s t).trans_lt hα)
  · intro α hα
    exact chart_mark_degreeLE α ((le_max_right s t).trans_lt hα)
  · intro j
    exact candidate.mark_log_on_slice _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem formal_mark_group
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (hlength : ∀ i, max s t < C.slice.length i) :
    D.filtration.realPolynomialGroupMap Fmark φ hφ (fun _ : C.Variables => 1)
      (D.filtration.realification.polynomialOrbitCoordinates _ candidate.orbit) =
    Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart) C.integerChart_support
      (Fmark.realification.polynomialOrbitCoordinates _ marked) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact candidate.formal_mark hlength

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalChart

theorem degree_lt_slice_length_of_dense (r : ℕ) {sliceCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      sliceCost C.slice.integerPoints)
    (hlong : ∀ i : C.Variables,
      Real.exp (sliceCost + (r : ℝ) + 1) ≤ (A.sides i.val : ℝ)) :
    ∀ i, r < C.slice.length i := by
  intro i
  have hlength := C.slice.length_lower_of_dense C.step_pos hdense i
  have hlower : Real.exp ((r : ℝ) + 1) ≤ (C.slice.length i : ℝ) := by
    calc
      _ = Real.exp (-sliceCost) * Real.exp (sliceCost + (r : ℝ) + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-sliceCost) * (A.sides i.val : ℝ) :=
        mul_le_mul_of_nonneg_left (hlong i) (Real.exp_nonneg _)
      _ ≤ _ := hlength
  have hstrict : (r : ℝ) < (C.slice.length i : ℝ) := by
    linarith [Real.add_one_le_exp ((r : ℝ) + 1)]
  exact_mod_cast hstrict

theorem degree_lt_slice_length (r : ℕ)
    (hlong : ∀ i : C.Variables,
      Real.exp (cost + (r : ℝ) + 1) ≤ (A.sides i.val : ℝ)) :
    ∀ i, r < C.slice.length i :=
  degree_lt_slice_length_of_dense r C.dense hlong

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

theorem exists_marked_chart_symbol_factors
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    [Fintype (SymbolBasisIndex (fun _ : C.Variables => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : C.Variables => 1) ν)]
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : C.Variables => 1) ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : C.Variables => 1) ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (q : ℝ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked),
      (∀ i, s < C.slice.length i) →
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : C.Variables => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates _ candidate.orbit) →
      ∃ El Pl Rl : Fmark.RealPolynomialSymbolGroup (fun _ : C.Variables => 1),
        El * Pl * Rl = Fmark.realPolynomialSymbolHom bF ν hF (fun _ => 1)
          (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
            C.integerChart_support (Fmark.realification.polynomialOrbitCoordinates _ marked)) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ => 1)
            (W.map (D.filtration.associatedGradedMap Fmark φ hφ))) ∧
        Fmark.SymbolSlowBound bF ν hF (fun _ => 1)
          (fun i : C.Variables => (A.sides i.val : ℝ))
          (Real.exp ((p + 2) ^ 3 + q)) El ∧
        Fmark.SymbolRationalGrid bF ν hF (fun _ => 1) m Rl := by
  obtain ⟨m, hm, hmp, hlm, hmap⟩ :=
    D.filtration.exists_common_refiltered_marked_symbol_factors Fmark bD ω hD bF ν hF
      φ hφ hH hl hentries hp hsource htarget hHp hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro q W candidate hlength hfactor
  have hside (i : C.Variables) : (0 : ℝ) < A.sides i.val := by
    apply Nat.cast_pos.mpr
    change 0 < Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val
    cases i.val with
    | inl z => exact S.positive
    | inr z => exact allocatedPrincipalSides_pos B U b S z
  obtain ⟨El, Pl, Rl, hprod, hPl, hEl, hRl⟩ :=
    hmap (fun i : C.Variables => (A.sides i.val : ℝ)) hside q W
      (D.filtration.realification.polynomialOrbitCoordinates _ candidate.orbit) hfactor
  refine ⟨El, Pl, Rl, ?_, hPl, hEl, hRl⟩
  rw [candidate.formal_mark_group hφ (by simpa only [max_self] using hlength)] at hprod
  exact hprod

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

private theorem adaptedChart_eq_of_chart_eq
    {V K L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : V → ℕ) (v : K → ℕ)
    (β γ : V → MvPolynomial K ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
    (heq : β = γ) (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v β hβ g = F.weightedAdaptedRealChartHom w v γ hγ g := by
  cases heq
  rfl

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

theorem withKeep_chart_integerChart (z : P.productive) :
    ((P.withKeep keep hkeep).chart z).integerChart =
      allocatedFrozenIntegerFullChart B U b o poly hm P.centerLift
        z.val.1.val z.val.2.val (P.chart z).sample keep
        ((P.withKeep keep hkeep).chart z).fixed := by
  change allocatedFrozenIntegerFullChart B U b o poly hm (P.chart z).centerLift
      (P.chart z).path.1.val (P.chart z).path.2.val (P.chart z).sample keep
      ((P.withKeep keep hkeep).chart z).fixed = _
  rw [P.chart_centerLift z, P.chart_path z]

theorem withKeep_chart_recovered (z : P.productive) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      P.centerLift z.val.1.val z.val.2.val (P.chart z).sample (P.chart z).read := by
  have h := (P.chart z).recovered
  simpa only [P.chart_centerLift z, P.chart_path z] using h

theorem exists_withKeep_marked_frozen_symbol_factors
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν)]
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ den : ℕ, 0 < den ∧ (den : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ den ∧
      ∀ (z : P.productive) (q : ℝ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded),
      (∀ i, s < ((P.withKeep keep hkeep).chart z).slice.length i) →
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates _
          ((P.withKeep keep hkeep).candidate z).orbit) →
      ∃ El Pl Rl : Fmark.RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1),
        El * Pl * Rl = Fmark.realPolynomialSymbolHom bF ν hF (fun _ => 1)
          (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : {i // keep i} => 1)
            (integerSampledRealChart
              (allocatedFrozenIntegerFullChart B U b o poly hm P.centerLift
                z.val.1.val z.val.2.val (P.chart z).sample keep
                ((P.withKeep keep hkeep).chart z).fixed))
            (allocatedFrozenIntegerFullChart_support B U b o poly hm P.centerLift
              z.val.1.val z.val.2.val (P.chart z).sample keep
              ((P.withKeep keep hkeep).chart z).fixed)
            (Fmark.realification.polynomialOrbitCoordinates _ marked)) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ => 1)
            (W.map (D.filtration.associatedGradedMap Fmark φ hφ))) ∧
        Fmark.SymbolSlowBound bF ν hF (fun _ => 1)
          (fun i : {i // keep i} => (A.sides i.val : ℝ))
          (Real.exp ((p + 2) ^ 3 + q)) El ∧
        Fmark.SymbolRationalGrid bF ν hF (fun _ => 1) den Rl := by
  obtain ⟨den, hden, hdenBound, hlden, hmap⟩ :=
    D.filtration.exists_common_refiltered_marked_symbol_factors (σ := {i // keep i})
      Fmark bD ω hD bF ν hF φ hφ hH hl hentries hp hsource htarget hHp hlp
  refine ⟨den, hden, hdenBound, hlden, ?_⟩
  intro z q W hlength hfactor
  have hside (i : {i // keep i}) : (0 : ℝ) < A.sides i.val := by
    apply Nat.cast_pos.mpr
    change 0 < Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val
    cases i.val with
    | inl x => exact S.positive
    | inr x => exact allocatedPrincipalSides_pos B U b S x
  obtain ⟨El, Pl, Rl, hprod, hPl, hEl, hRl⟩ :=
    hmap (fun i : {i // keep i} => (A.sides i.val : ℝ)) hside q W
      (D.filtration.realification.polynomialOrbitCoordinates _
        ((P.withKeep keep hkeep).candidate z).orbit) hfactor
  refine ⟨El, Pl, Rl, ?_, hPl, hEl, hRl⟩
  have hmark := ((P.withKeep keep hkeep).candidate z).formal_mark_group hφ
    (by simpa only [max_self] using hlength)
  have hmarked := hprod.trans (congrArg
    (Fmark.realPolynomialSymbolHom bF ν hF (fun _ : {i // keep i} => 1)) hmark)
  apply hmarked.trans
  apply congrArg (Fmark.realPolynomialSymbolHom bF ν hF (fun _ : {i // keep i} => 1))
  apply adaptedChart_eq_of_chart_eq
  exact congrArg integerSampledRealChart (P.withKeep_chart_integerChart keep hkeep z)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
