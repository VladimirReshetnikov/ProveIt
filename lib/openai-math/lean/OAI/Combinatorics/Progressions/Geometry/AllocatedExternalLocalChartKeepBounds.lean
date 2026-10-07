import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRefinementLabels

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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

noncomputable def withKeep : AllocatedExternalLocalChart (E := E) A cost where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := keep
  fixed := hkeep ▸ C.fixed
  fixed_in_box := by cases hkeep; exact C.fixed_in_box
  step := C.step
  step_pos := C.step_pos
  slice := hkeep ▸ C.slice
  dense := by cases hkeep; exact C.dense

@[simp] theorem withKeep_self : C.withKeep C.keep rfl = C := rfl

theorem withKeep_slice_transport {q : ℕ} {outputCost outputScore : ℝ}
    (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hdense : IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val)
      outputCost slice.integerPoints)
    (hinside : slice.integerPoints ⊆ (C.withKeep keep hkeep).slice.integerPoints)
    (f : (X → ℤ) → (X ⊕ (Σ j, J j) → ℤ) → ℂ)
    (hscore : outputScore ≤ (𝔼 u ∈ slice.integerPoints,
      f ((C.withKeep keep hkeep).physical u) ((C.withKeep keep hkeep).chartValues u)).re) :
    ∃ oldSlice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) q,
      IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
        outputCost oldSlice.integerPoints ∧
      oldSlice.integerPoints ⊆ C.slice.integerPoints ∧
      outputScore ≤ (𝔼 u ∈ oldSlice.integerPoints, f (C.physical u) (C.chartValues u)).re := by
  cases hkeep
  exact ⟨slice, hdense, hinside, hscore⟩

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

noncomputable def withKeep :
    AllocatedExternalLocalCandidate (C.withKeep keep hkeep) D Fmark φ marked := by
  cases hkeep
  exact candidate

@[simp] theorem withKeep_score :
    (candidate.withKeep keep hkeep).score observable weight = candidate.score observable weight := by
  cases hkeep
  rfl

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

noncomputable def withKeep :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart z := (P.chart z).withKeep keep (hkeep z)
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side z := by
    change ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost
    rw [← hkeep z]
    exact P.frozen_side z
  candidate z := (P.candidate z).withKeep keep (hkeep z)
  score z := by rw [AllocatedExternalLocalCandidate.withKeep_score]; exact P.score z

@[simp] theorem withKeep_chart_keep (z : P.productive) :
    ((P.withKeep keep hkeep).chart z).keep = keep := rfl

noncomputable def conclusion_of_withKeep {outputCost outputMass outputScore : ℝ}
    (result : (P.withKeep keep hkeep).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore := by
  have hex (z : result.retained) :
      ∃ slice : ResidueBoxSlice
          (fun i : (P.chart ⟨z.val, result.subset z.property⟩).Variables => A.sides i.val)
          (result.step z),
        IsDenseCommonStrideBox
          (fun i : (P.chart ⟨z.val, result.subset z.property⟩).Variables => A.sides i.val)
          outputCost slice.integerPoints ∧
        slice.integerPoints ⊆ (P.chart ⟨z.val, result.subset z.property⟩).slice.integerPoints ∧
        outputScore ≤ P.ambientScore result.ambient ⟨z.val, result.subset z.property⟩
          slice.integerPoints := by
    exact (P.chart ⟨z.val, result.subset z.property⟩).withKeep_slice_transport
      keep (hkeep _) (result.slice z) (result.dense z) (result.inside z)
      (fun x y => weight x * observable x (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          y result.ambient))) (result.score z)
  choose slice hdense hinside hscore using hex
  exact
    { ambient := result.ambient
      marked := result.marked
      retained := result.retained
      subset := result.subset
      mass := result.mass
      step := result.step
      step_pos := result.step_pos
      slice := slice
      dense := hdense
      inside := hinside
      score := hscore }

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem slice_transport_of_eq_withKeep
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)
    (C' : AllocatedExternalLocalChart (E := Deck) A cost)
    (hchart : C' = C.withKeep keep hkeep)
    {q : ℕ} {outputCost outputScore : ℝ}
    (slice : ResidueBoxSlice (fun i : C'.Variables => A.sides i.val) q)
    (hdense : IsDenseCommonStrideBox (fun i : C'.Variables => A.sides i.val)
      outputCost slice.integerPoints)
    (hinside : slice.integerPoints ⊆ C'.slice.integerPoints)
    (f : (X → ℤ) → (X ⊕ (Σ j, J j) → ℤ) → ℂ)
    (hscore : outputScore ≤ (𝔼 u ∈ slice.integerPoints,
      f (C'.physical u) (C'.chartValues u)).re) :
    ∃ oldSlice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) q,
      IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
        outputCost oldSlice.integerPoints ∧
      oldSlice.integerPoints ⊆ C.slice.integerPoints ∧
      outputScore ≤ (𝔼 u ∈ oldSlice.integerPoints, f (C.physical u) (C.chartValues u)).re := by
  subst C'
  exact C.withKeep_slice_transport keep hkeep slice hdense hinside f hscore

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold massThreshold' scoreThreshold' : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold scoreThreshold)
    (Q : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold' scoreThreshold')

def conclusion_of_chartwise_withKeep
    (hsub : Q.productive ⊆ P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : Q.productive, (P.chart ⟨z.val, hsub z.property⟩).keep = keep)
    (hchart : ∀ z : Q.productive,
      Q.chart z = (P.chart ⟨z.val, hsub z.property⟩).withKeep keep (hkeep z))
    {outputCost outputMass outputScore : ℝ}
    (result : Q.Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore := by
  have hex (z : result.retained) :
      ∃ slice : ResidueBoxSlice
          (fun i : (P.chart ⟨z.val, hsub (result.subset z.property)⟩).Variables => A.sides i.val)
          (result.step z),
        IsDenseCommonStrideBox
          (fun i : (P.chart ⟨z.val, hsub (result.subset z.property)⟩).Variables => A.sides i.val)
          outputCost slice.integerPoints ∧
        slice.integerPoints ⊆ (P.chart ⟨z.val, hsub (result.subset z.property)⟩).slice.integerPoints ∧
        outputScore ≤ P.ambientScore result.ambient
          ⟨z.val, hsub (result.subset z.property)⟩ slice.integerPoints := by
    exact (P.chart ⟨z.val, hsub (result.subset z.property)⟩).slice_transport_of_eq_withKeep
      keep (hkeep ⟨z.val, result.subset z.property⟩)
      (Q.chart ⟨z.val, result.subset z.property⟩) (hchart ⟨z.val, result.subset z.property⟩)
      (result.slice z) (result.dense z) (result.inside z)
      (fun x y => weight x * observable x (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          y result.ambient))) (result.score z)
  choose slice hdense hinside hscore using hex
  exact {
    ambient := result.ambient
    marked := result.marked
    retained := result.retained
    subset := fun _ hz => hsub (result.subset hz)
    mass := result.mass
    step := result.step
    step_pos := result.step_pos
    slice := slice
    dense := hdense
    inside := hinside
    score := hscore
  }

@[simp] theorem conclusion_of_chartwise_withKeep_retained
    (hsub : Q.productive ⊆ P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : Q.productive, (P.chart ⟨z.val, hsub z.property⟩).keep = keep)
    (hchart : ∀ z : Q.productive,
      Q.chart z = (P.chart ⟨z.val, hsub z.property⟩).withKeep keep (hkeep z))
    {outputCost outputMass outputScore : ℝ}
    (result : Q.Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_chartwise_withKeep Q hsub keep hkeep hchart result).retained =
      result.retained := rfl

@[simp] theorem conclusion_of_chartwise_withKeep_ambient
    (hsub : Q.productive ⊆ P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : Q.productive, (P.chart ⟨z.val, hsub z.property⟩).keep = keep)
    (hchart : ∀ z : Q.productive,
      Q.chart z = (P.chart ⟨z.val, hsub z.property⟩).withKeep keep (hkeep z))
    {outputCost outputMass outputScore : ℝ}
    (result : Q.Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_chartwise_withKeep Q hsub keep hkeep hchart result).ambient =
      result.ambient := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom

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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

theorem withKeep_chart_fixed
    (β : X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
    (hfixed : ∀ x : C.Variables → ℝ,
      (fun v => MvPolynomial.eval
        (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i)) (β v)) =
      (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i))) :
    ∀ x : (C.withKeep keep hkeep).Variables → ℝ,
      (fun v => MvPolynomial.eval
        (fun i => MvPolynomial.eval x
          (integerSampledRealChart (C.withKeep keep hkeep).integerChart i)) (β v)) =
      (fun i => MvPolynomial.eval x
        (integerSampledRealChart (C.withKeep keep hkeep).integerChart i)) := by
  cases hkeep
  exact hfixed

theorem withKeep_polynomialSlowBound
    {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (basis : Basis κ ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group)
    (M : ℝ)
    (hslow : F.PolynomialSlowBound basis (fun _ : C.Variables => 1)
      (fun i : C.Variables => (A.sides i.val : ℝ)) M
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support g)) :
    F.PolynomialSlowBound basis (fun _ : (C.withKeep keep hkeep).Variables => 1)
      (fun i : (C.withKeep keep hkeep).Variables => (A.sides i.val : ℝ)) M
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : (C.withKeep keep hkeep).Variables => 1)
        (integerSampledRealChart (C.withKeep keep hkeep).integerChart)
        (C.withKeep keep hkeep).integerChart_support g) := by
  cases hkeep
  exact hslow

theorem withKeep_dense (dCost : ℝ)
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      dCost C.slice.integerPoints) :
    IsDenseCommonStrideBox (fun i : (C.withKeep keep hkeep).Variables => A.sides i.val)
      dCost (C.withKeep keep hkeep).slice.integerPoints := by
  cases hkeep
  exact hdense

theorem withKeep_original_dense :
    IsDenseCommonStrideBox (fun i : (C.withKeep keep hkeep).Variables => A.sides i.val)
      cost (C.withKeep keep hkeep).slice.integerPoints :=
  C.withKeep_dense keep hkeep cost C.dense

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
