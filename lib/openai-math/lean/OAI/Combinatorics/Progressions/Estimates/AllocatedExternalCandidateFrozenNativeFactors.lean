import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredFactorsNestedFreeze
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartKeepBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (adapted : D.AdaptedModelData)

def adaptedRebase : AllocatedExternalLocalCandidate C adapted.model Fmark φ marked where
  orbit := candidate.orbit
  mark_on_slice := candidate.mark_on_slice

@[simp] theorem adaptedRebase_orbit :
    (candidate.adaptedRebase adapted).orbit = candidate.orbit := rfl

@[simp] theorem adaptedRebase_value (u : C.Variables → ℤ) :
    (candidate.adaptedRebase adapted).value u = candidate.value u := rfl

@[simp] theorem adaptedRebase_siteValue (site : A.Site) :
    (candidate.adaptedRebase adapted).siteValue site = candidate.siteValue site := rfl

@[simp] theorem adaptedRebase_score :
    (candidate.adaptedRebase adapted).score observable weight =
      candidate.score observable weight := rfl

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (adapted : D.AdaptedModelData)

def adaptedRebase :
    AllocatedExternalCandidateProblem (E := E) A adapted.model Fmark φ marked observable weight
      cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (P.candidate z).adaptedRebase adapted
  score := P.score

@[simp] theorem adaptedRebase_productive :
    (P.adaptedRebase adapted).productive = P.productive := rfl

@[simp] theorem adaptedRebase_chart (z : P.productive) :
    (P.adaptedRebase adapted).chart z = P.chart z := rfl

@[simp] theorem adaptedRebase_localLaw (z : P.productive) :
    ((P.adaptedRebase adapted).chart z).localLaw = (P.chart z).localLaw := rfl

@[simp] theorem adaptedRebase_centerLift :
    (P.adaptedRebase adapted).centerLift = P.centerLift := rfl

@[simp] theorem adaptedRebase_candidate_orbit (z : P.productive) :
    ((P.adaptedRebase adapted).candidate z).orbit = (P.candidate z).orbit := rfl

@[simp] theorem adaptedRebase_candidate_value (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    ((P.adaptedRebase adapted).candidate z).value u = (P.candidate z).value u := rfl

@[simp] theorem adaptedRebase_candidate_score (z : P.productive) :
    ((P.adaptedRebase adapted).candidate z).score observable weight =
      (P.candidate z).score observable weight := rfl

@[simp] theorem adaptedRebase_ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.adaptedRebase adapted).ambientScore ambient z points =
      P.ambientScore ambient z points := rfl

def conclusion_of_adaptedRebase {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore where
  ambient := result.ambient
  marked := result.marked
  retained := result.retained
  subset := result.subset
  mass := result.mass
  step := result.step
  step_pos := result.step_pos
  slice := result.slice
  dense := result.dense
  inside := result.inside
  score := result.score

def conclusion_adaptedRebase {outputCost outputMass outputScore : ℝ}
    (result : P.Conclusion outputCost outputMass outputScore) :
    (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore where
  ambient := result.ambient
  marked := result.marked
  retained := result.retained
  subset := result.subset
  mass := result.mass
  step := result.step
  step_pos := result.step_pos
  slice := result.slice
  dense := result.dense
  inside := result.inside
  score := result.score

def conclusionAdaptedRebaseEquiv {outputCost outputMass outputScore : ℝ} :
    P.Conclusion outputCost outputMass outputScore ≃
      (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore where
  toFun := P.conclusion_adaptedRebase adapted
  invFun := P.conclusion_of_adaptedRebase adapted
  left_inv result := by cases result; rfl
  right_inv result := by cases result; rfl

@[simp] theorem conclusion_of_adaptedRebase_ambient {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_adaptedRebase adapted result).ambient = result.ambient := rfl

@[simp] theorem conclusion_of_adaptedRebase_retained {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_adaptedRebase adapted result).retained = result.retained := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

namespace Erdos3.RationalFilteredNilmanifold.AdaptedModelData

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d} (adapted : D.AdaptedModelData)
    {σ : Type*} (side : σ → ℝ) (q : ℝ) (den : ℕ)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)

@[simp] theorem model_commonFactors_iff :
    adapted.model.filtration.HasCommonRefilteredOrbitFactors
        adapted.model.basis adapted.weight adapted.model_layers side q den W g ↔
      D.filtration.HasCommonRefilteredOrbitFactors
        adapted.basis adapted.weight adapted.layers side q den W g := Iff.rfl

theorem commonFactors_model
    (h : D.filtration.HasCommonRefilteredOrbitFactors
      adapted.basis adapted.weight adapted.layers side q den W g) :
    adapted.model.filtration.HasCommonRefilteredOrbitFactors
      adapted.model.basis adapted.weight adapted.model_layers side q den W g := h

end Erdos3.RationalFilteredNilmanifold.AdaptedModelData

end

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
    {L M ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

theorem hasCommonRefilteredOrbitFactors_withKeep
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.withKeep keep hkeep).orbit) := by
  cases hkeep
  exact h

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
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
    {L M ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalCandidateProblem

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem withKeep_commonFactors
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (den : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hfactor : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q den W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)) :
    ∀ z : (P.withKeep keep hkeep).productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q den W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          ((P.withKeep keep hkeep).candidate z).orbit) := by
  intro z
  exact (P.candidate z).hasCommonRefilteredOrbitFactors_withKeep
    keep (hkeep z) bD ω hD q den W (hfactor z)

theorem adaptedRebase_withKeep_commonFactors
    (adapted : D.AdaptedModelData)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    (q : ℝ) (den : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hfactor : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors adapted.basis adapted.weight adapted.layers
        (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q den W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)) :
    ∀ z : ((P.adaptedRebase adapted).withKeep keep hkeep).productive,
      adapted.model.filtration.HasCommonRefilteredOrbitFactors
        adapted.model.basis adapted.weight adapted.model_layers
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q den W
        (adapted.model.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (((P.adaptedRebase adapted).withKeep keep hkeep).candidate z).orbit) := by
  apply (P.adaptedRebase adapted).withKeep_commonFactors
    keep hkeep adapted.model.basis adapted.weight adapted.model_layers q den W
  exact hfactor

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

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

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

def axisVariableEquiv : {i // keep i} ≃ {i : C.Variables // keep i.val} where
  toFun i := ⟨⟨i.val, hkeep i.val i.property⟩, i.property⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hkeep in

theorem hasCommonRefilteredOrbitFactors_axisPolynomial
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
    (F : NilpotentLieFiltration L s) (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W g) :
    F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // keep i} => 1) (C.axisPolynomial keep fixed)
        (C.axisPolynomial_support keep fixed) g) := by
  let localKeep : C.Variables → Prop := fun i => keep i.val
  let β := frozenCoordinate localKeep (fun i => (fixed i : ℝ))
  let e := C.axisVariableEquiv keep hkeep
  let γ : {i : C.Variables // localKeep i} → MvPolynomial {i // keep i} ℝ :=
    fun i => MvPolynomial.X (e.symm i)
  have hβ := frozenCoordinate_support localKeep (fun i => (fixed i : ℝ))
  have hγ : ∀ i, γ i ∈ weightedSupportLE (fun _ : {i // keep i} => 1) 1 :=
    fun i => weightedSupportLE_X (fun _ : {i // keep i} => 1) (e.symm i)
  have hf := HasCommonRefilteredOrbitFactors.freeze F bD ω hF localKeep
    (fun i => (fixed i : ℝ)) (fun i : C.Variables => (A.sides i.val : ℝ)) q l W g h
  have hr := HasCommonRefilteredOrbitFactors.reindex F bD ω hF e
    (fun i : {i : C.Variables // localKeep i} => (A.sides i.val.val : ℝ)) q l W
    (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
      (fun _ : {i : C.Variables // localKeep i} => 1) β hβ g) hf
  have hcomp : (fun i => MvPolynomial.aeval γ (β i)) = C.axisPolynomial keep fixed := by
    funext i
    by_cases hi : keep i.val <;>
      simp [β, γ, e, localKeep, frozenCoordinate, axisVariableEquiv, axisPolynomial, hi]
  have hcompose := F.weightedAdaptedRealChartHom_comp
    (fun _ : C.Variables => 1) (fun _ : {i : C.Variables // localKeep i} => 1)
    (fun _ : {i // keep i} => 1) β γ hβ hγ
    (weightedRealChart_comp_support _ _ _ β γ hβ hγ) g
  rw [← hcompose] at hr
  simpa only [hcomp, e, axisVariableEquiv, Equiv.coe_fn_mk] using hr

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem hasCommonRefilteredOrbitFactors_freezeAxes
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).orbit) := by
  change D.filtration.HasCommonRefilteredOrbitFactors bD ω hD _ q l W
    (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) candidate.orbit))
  rw [D.filtration.polynomialOrbitRealChart_polynomialCoordinates]
  exact C.hasCommonRefilteredOrbitFactors_axisPolynomial keep hkeep
    D.filtration bD ω hD fixed q l W _ h

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem problem_nativeFactors
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (P.candidate z).orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (freezing.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (freezing.problem.candidate z).orbit) :=
  (P.candidate z).hasCommonRefilteredOrbitFactors_freezeAxes (shortCost := shortCost)
    (keep z) (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
    bD ω hD q l W h

theorem withKeep_nativeFactors
    (commonKeep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : freezing.problem.productive,
      (freezing.problem.chart z).keep = commonKeep)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (P.candidate z).orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // commonKeep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        ((freezing.problem.withKeep commonKeep hkeep).candidate z).orbit) :=
  (freezing.problem.candidate z).hasCommonRefilteredOrbitFactors_withKeep
    commonKeep (hkeep z) bD ω hD q l W
    (freezing.problem_nativeFactors bD ω hD q l W z h)

end AllocatedExternalCandidateProblem.AxisFreezing

end Erdos3.VectorPolynomial

end

end OAI
