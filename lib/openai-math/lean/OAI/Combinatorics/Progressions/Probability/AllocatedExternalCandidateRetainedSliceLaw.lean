import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidatePhysicalScore

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (points : Finset (C.Variables → ℤ))
    (hpoints : points.Nonempty)
    (hbox : points ⊆ integerBox (fun i : C.Variables => A.sides i.val))

noncomputable def retainedSite (u : points) : A.Site :=
  C.site u.val (hbox u.property)

@[simp] theorem retainedSite_val (u : points) :
    (C.retainedSite points hbox u).val = C.parameter u.val := rfl

@[simp] theorem physical_retainedSite (u : points) :
    A.physical C.path (C.retainedSite points hbox u) = C.physical u.val := rfl

@[simp] theorem retainedParameter_retainedSite (u : points) :
    C.retainedParameter (C.retainedSite points hbox u).val = u.val :=
  C.retainedParameter_parameter u.val

noncomputable def retainedLaw : FiniteProbabilityWeights A.Site :=
  (FiniteProbabilityWeights.uniformFinset points hpoints).finitePushforward
    (C.retainedSite points hbox)

theorem retainedLaw_mean_parameter (f : (LayerSamplerVariables G I n B → ℤ) → ℝ) :
    (C.retainedLaw points hpoints hbox).mean (fun site => f site.val) =
      𝔼 u ∈ points, f (C.parameter u) := by
  rw [retainedLaw, FiniteProbabilityWeights.mean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_mean _ _ (fun u => f (C.parameter u))

theorem retainedLaw_complexMean_parameter
    (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    (C.retainedLaw points hpoints hbox).complexMean (fun site => f site.val) =
      𝔼 u ∈ points, f (C.parameter u) := by
  rw [retainedLaw, FiniteProbabilityWeights.complexMean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_complexMean _ _ (fun u => f (C.parameter u))

theorem retainedLaw_mean_physical (f : (X → ℤ) → ℝ) :
    (C.retainedLaw points hpoints hbox).mean (fun site => f (A.physical C.path site)) =
      𝔼 u ∈ points, f (C.physical u) :=
  C.retainedLaw_mean_parameter points hpoints hbox
    (fun x => f (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))

theorem retainedLaw_complexMean_physical (f : (X → ℤ) → ℂ) :
    (C.retainedLaw points hpoints hbox).complexMean
        (fun site => f (A.physical C.path site)) =
      𝔼 u ∈ points, f (C.physical u) :=
  C.retainedLaw_complexMean_parameter points hpoints hbox
    (fun x => f (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))

theorem retainedLaw_support (site : A.Site)
    (hsite : 0 < (C.retainedLaw points hpoints hbox).weight site) :
    ∃ u : C.Variables → ℤ, ∃ hu : u ∈ points,
      site = C.site u (hbox hu) ∧ A.physical C.path site = C.physical u := by
  obtain ⟨u, hu, _⟩ :=
    (FiniteProbabilityWeights.finitePushforward_pos_iff
      (FiniteProbabilityWeights.uniformFinset points hpoints)
      (C.retainedSite points hbox) site).mp hsite
  refine ⟨u.val, u.property, hu.symm, ?_⟩
  rw [← hu]
  rfl

theorem retainedLaw_retainedSite_pos (u : points) :
    0 < (C.retainedLaw points hpoints hbox).weight (C.retainedSite points hbox u) := by
  apply (FiniteProbabilityWeights.finitePushforward_pos_iff
    (FiniteProbabilityWeights.uniformFinset points hpoints)
    (C.retainedSite points hbox) (C.retainedSite points hbox u)).mpr
  refine ⟨u, rfl, ?_⟩
  change 0 < (Fintype.card points : ℝ)⁻¹
  let : Nonempty points := hpoints.to_subtype
  positivity

theorem retainedLaw_original :
    C.retainedLaw C.slice.integerPoints C.dense.nonempty
      C.slice.integerPoints_subset_integerBox = C.localLaw := rfl

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

noncomputable def siteLaw (z : out.retained) : FiniteProbabilityWeights A.Site :=
  (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw
    (out.slice z).integerPoints (out.dense z).nonempty
    (out.slice z).integerPoints_subset_integerBox

theorem siteLaw_complexMean_physical (z : out.retained) (f : (X → ℤ) → ℂ) :
    (out.siteLaw z).complexMean (fun site => f (A.physical z.val site)) =
      𝔼 u ∈ (out.slice z).integerPoints,
        f ((P.chart ⟨z.val, out.subset z.property⟩).physical u) := by
  have h := (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw_complexMean_physical
    (out.slice z).integerPoints (out.dense z).nonempty
    (out.slice z).integerPoints_subset_integerBox f
  rw [P.chart_path] at h
  exact h

theorem siteLaw_support (z : out.retained) (site : A.Site)
    (hsite : 0 < (out.siteLaw z).weight site) :
    ∃ u : (P.chart ⟨z.val, out.subset z.property⟩).Variables → ℤ,
      u ∈ (out.slice z).integerPoints ∧
      u ∈ (P.chart ⟨z.val, out.subset z.property⟩).slice.integerPoints ∧
      site.val = (P.chart ⟨z.val, out.subset z.property⟩).parameter u ∧
      A.physical z.val site = (P.chart ⟨z.val, out.subset z.property⟩).physical u := by
  obtain ⟨u, hu, hs, hp⟩ :=
    (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw_support
      (out.slice z).integerPoints (out.dense z).nonempty
      (out.slice z).integerPoints_subset_integerBox site hsite
  refine ⟨u, hu, out.inside z hu, ?_, ?_⟩
  · exact congrArg Subtype.val hs
  · rw [P.chart_path] at hp
    exact hp

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem siteLaw_ambientPhysicalValue_score
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : out.retained) :
    ((out.siteLaw z).complexMean (fun site => weight (A.physical z.val site) *
      observable (A.physical z.val site)
        (P.ambientPhysicalValue ambient (A.physical z.val site)))).re =
      P.ambientScore ambient ⟨z.val, out.subset z.property⟩ (out.slice z).integerPoints := by
  rw [P.ambientScore_eq_physical hσ1 H hH hchart hsmall hp ambient
    ⟨z.val, out.subset z.property⟩ _ (out.inside z)]
  exact congrArg Complex.re (out.siteLaw_complexMean_physical z (fun x =>
    weight x * observable x (P.ambientPhysicalValue ambient x)))

theorem siteLaw_score (z : out.retained) :
    outputScore ≤ ((out.siteLaw z).complexMean (fun site => weight (A.physical z.val site) *
      observable (A.physical z.val site)
        (P.ambientPhysicalValue out.ambient (A.physical z.val site)))).re := by
  rw [out.siteLaw_ambientPhysicalValue_score hσ1 H hH hchart hsmall hp]
  exact out.score z

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
