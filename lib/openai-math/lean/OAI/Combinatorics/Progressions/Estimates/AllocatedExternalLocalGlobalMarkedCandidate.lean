import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
import OAI.Combinatorics.Progressions.Geometry.GlobalMarkedNativeChartResetConditions

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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

namespace AllocatedExternalLocalCandidate
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (orbit : Dref.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))

noncomputable def ofRefilteredIncludedMark
    (hincluded : ∀ u ∈ C.slice.integerPoints,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u orbit)) =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) markedMiddle)) :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle where
  orbit := orbit
  mark_on_slice u hu := by
    apply realificationMap_incl_injective (hnil := Fmark.filtration.lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    rw [← D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref]
    exact hincluded u hu

noncomputable def ofNativeRefilteredMiddle
    (nativeMiddle : (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (nativeMark : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (hprojection : D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) nativeMiddle = nativeMark)
    (hinclusion : ∀ u ∈ C.slice.integerPoints,
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u orbit) =
      D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ)) nativeMiddle)
    (hmarked : ∀ u ∈ C.slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ)) nativeMark =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) markedMiddle)) :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle :=
  ofRefilteredIncludedMark C D Fmark φ hφ W Dref Fref markedMiddle orbit
    (fun point hpoint =>
      (congrArg (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ)
        (hinclusion point hpoint)).trans
      ((D.filtration.realPolynomialGroupMap_value Fmark.filtration φ hφ
        (fun _ => 1) nativeMiddle (fun index => (point index : ℝ))).symm.trans
      ((congrArg (Fmark.filtration.adaptedPolynomialRealValueHom
        (fun _ : C.Variables => 1) (fun index => (point index : ℝ))) hprojection).trans
        (hmarked point hpoint))))

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
    {w : σ → ℕ} {W : LieSubalgebra ℚ F.AssociatedGraded}
    {g : (F.realification.adaptedPolynomialFiltration w).Group}
    {E R : F.RealPolynomialSymbolGroup w}
    (A : GlobalMarkedNativeFactors F b ω hF w W g E R)
    (Fref : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s d)
    (hFref : Fref.filtration = F.gradedRefiltration W)

noncomputable def markedMiddleOn : Fref.filtration.realification.PolynomialOrbit w :=
  (F.gradedRefiltration W).realPolynomialOrbitChangeFiltration
    Fref.filtration hFref w A.markedMiddle

@[simp] theorem markedMiddleOn_log :
    (A.markedMiddleOn Fref hFref).log = A.markedMiddle.log := rfl

theorem markedMiddleOn_values (t : σ → ℝ) :
    realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      (Fref.filtration.realification.polynomialOrbitRealEval w t
        (A.markedMiddleOn Fref hFref)) =
      F.adaptedPolynomialRealValueHom w t A.middle := by
  apply NilpotentLieBCHGroup.ext
  exact congrArg NilpotentLieBCHGroup.coord (A.middle_values t)

end Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

namespace AllocatedExternalLocalChart

variable {M κ : Type*} [LieRing M] [LieAlgebra ℚ M] {s f : ℕ}
    {F : NilpotentLieFiltration M s} {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    {g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors F c ν hF (fullTaggedVariableWeight J) W g EF RF)
    (Fref : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s f)
    (hFref : Fref.filtration = F.gradedRefiltration W)

theorem globalMarked_middle_values (u : C.Variables → ℤ) :
    F.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1) (fun i => (u i : ℝ))
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support factors.middle) =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) (factors.markedMiddleOn Fref hFref)) := by
  rw [F.adaptedPolynomialRealValueHom_weightedChart]
  have heval : (fun i => MvPolynomial.eval (fun j => (u j : ℝ))
      (integerSampledRealChart C.integerChart i)) =
      (fun i => (C.chartValues u i : ℝ)) := by
    funext i
    exact integerSampledRealChart_eval C.integerChart u i
  rw [heval, ← factors.markedMiddleOn_values Fref hFref,
    polynomialOrbitRealEval_integer]

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (nativeMiddle : (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (native : (D.filtration.gradedRefiltration W).realification.PolynomialOrbit
      (fun _ : C.Variables => 1))
    (hprojection : D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) nativeMiddle =
      Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support factors.middle)
    (hlog : map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap native.log =
      (nativeMiddle.coord : VectorPolynomial C.Variables ℚ (ℝ ⊗[ℚ] L)))

noncomputable def ofGlobalMarkedNativeMiddle :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (factors.markedMiddleOn Fref hFref) :=
  ofNativeRefilteredMiddle C D Fmark φ hφ W Dref Fref
    (factors.markedMiddleOn Fref hFref)
    ((D.filtration.gradedRefiltration W).realPolynomialOrbitChangeFiltration
      Dref.filtration hDref (fun _ : C.Variables => 1) native)
    nativeMiddle _ hprojection
    (by
      intro u _
      rw [← polynomialOrbitRealEval_integer]
      apply NilpotentLieBCHGroup.ext
      exact congrArg NilpotentLieBCHGroup.coord
        (D.filtration.native_refiltered_orbit_real_value W
          (fun _ : C.Variables => 1) native _ hlog (fun i => (u i : ℝ))))
    (by
      intro u _
      exact C.globalMarked_middle_values factors Fref hFref u)

@[simp] theorem ofGlobalMarkedNativeMiddle_orbit_log :
    (ofGlobalMarkedNativeMiddle C D Fmark φ hφ W Dref hDref Fref hFref
      factors nativeMiddle native hprojection hlog).orbit.log = native.log := rfl

theorem ofGlobalMarkedNativeMiddle_included_log :
    map (realLieHomToRat (realificationLieHom
      (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      (ofGlobalMarkedNativeMiddle C D Fmark φ hφ W Dref hDref Fref hFref
        factors nativeMiddle native hprojection hlog).orbit.log =
      (nativeMiddle.coord : VectorPolynomial C.Variables ℚ (ℝ ⊗[ℚ] L)) := hlog

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
