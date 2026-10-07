import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion

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

def retainedParameter (x : LayerSamplerVariables G I n B → ℤ) : C.Variables → ℤ :=
  fun i => x i.val

@[simp] theorem retainedParameter_parameter (u : C.Variables → ℤ) :
    C.retainedParameter (C.parameter u) = u := by
  funext i
  exact finiteSplitPoint_fixed C.keep u C.fixed i

noncomputable abbrev SlicePoint := ↥C.slice.integerPoints

noncomputable def sliceSite (u : C.SlicePoint) : A.Site :=
  C.site u.val (C.slice.integerPoints_subset_integerBox u.property)

@[simp] theorem sliceSite_val (u : C.SlicePoint) :
    (C.sliceSite u).val = C.parameter u.val := rfl

@[simp] theorem physical_sliceSite (u : C.SlicePoint) :
    A.physical C.path (C.sliceSite u) = C.physical u.val := rfl

noncomputable def localLaw : FiniteProbabilityWeights A.Site :=
  (FiniteProbabilityWeights.uniformFinset C.slice.integerPoints C.dense.nonempty).finitePushforward
    C.sliceSite

theorem localLaw_mean (f : A.Site → ℝ) :
    C.localLaw.mean f = 𝔼 u : C.SlicePoint, f (C.sliceSite u) := by
  let : Nonempty C.SlicePoint := C.dense.nonempty.to_subtype
  rw [localLaw, FiniteProbabilityWeights.mean_finitePushforward]
  exact FiniteProbabilityWeights.uniform_mean _

theorem localLaw_complexMean (f : A.Site → ℂ) :
    C.localLaw.complexMean f = 𝔼 u : C.SlicePoint, f (C.sliceSite u) := by
  let : Nonempty C.SlicePoint := C.dense.nonempty.to_subtype
  rw [localLaw, FiniteProbabilityWeights.complexMean_finitePushforward]
  exact FiniteProbabilityWeights.uniform_complexMean _

theorem localLaw_mean_parameter (f : (LayerSamplerVariables G I n B → ℤ) → ℝ) :
    C.localLaw.mean (fun site => f site.val) =
      𝔼 u ∈ C.slice.integerPoints, f (C.parameter u) := by
  rw [localLaw, FiniteProbabilityWeights.mean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_mean _ _ (fun u => f (C.parameter u))

theorem localLaw_complexMean_parameter (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    C.localLaw.complexMean (fun site => f site.val) =
      𝔼 u ∈ C.slice.integerPoints, f (C.parameter u) := by
  rw [localLaw, FiniteProbabilityWeights.complexMean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_complexMean _ _ (fun u => f (C.parameter u))

theorem localLaw_mean_physical (f : (X → ℤ) → ℝ) :
    C.localLaw.mean (fun site => f (A.physical C.path site)) =
      𝔼 u ∈ C.slice.integerPoints, f (C.physical u) :=
  C.localLaw_mean_parameter (fun x => f (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))

theorem localLaw_complexMean_physical (f : (X → ℤ) → ℂ) :
    C.localLaw.complexMean (fun site => f (A.physical C.path site)) =
      𝔼 u ∈ C.slice.integerPoints, f (C.physical u) :=
  C.localLaw_complexMean_parameter (fun x => f (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))

theorem localLaw_support (site : A.Site) (hsite : 0 < C.localLaw.weight site) :
    ∃ u : C.Variables → ℤ, ∃ hu : u ∈ C.slice.integerPoints,
      site = C.site u (C.slice.integerPoints_subset_integerBox hu) ∧
      A.physical C.path site = C.physical u := by
  obtain ⟨u, hu, _⟩ :=
    (FiniteProbabilityWeights.finitePushforward_pos_iff
      (FiniteProbabilityWeights.uniformFinset C.slice.integerPoints C.dense.nonempty)
      C.sliceSite site).mp hsite
  refine ⟨u.val, u.property, hu.symm, ?_⟩
  rw [← hu]
  rfl

theorem localLaw_sliceSite_pos (u : C.SlicePoint) :
    0 < C.localLaw.weight (C.sliceSite u) := by
  apply (FiniteProbabilityWeights.finitePushforward_pos_iff
    (FiniteProbabilityWeights.uniformFinset C.slice.integerPoints C.dense.nonempty)
    C.sliceSite (C.sliceSite u)).mpr
  refine ⟨u, rfl, ?_⟩
  change 0 < (Fintype.card C.SlicePoint : ℝ)⁻¹
  let : Nonempty C.SlicePoint := C.dense.nonempty.to_subtype
  positivity

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

noncomputable def siteValue (site : A.Site) : D.Space :=
  candidate.value (C.retainedParameter site.val)

@[simp] theorem siteValue_sliceSite (u : C.SlicePoint) :
    candidate.siteValue (C.sliceSite u) = candidate.value u.val := by
  unfold siteValue
  rw [C.sliceSite_val, C.retainedParameter_parameter]

theorem localLaw_score (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) :
    (C.localLaw.complexMean (fun site => weight (A.physical C.path site) *
      observable (A.physical C.path site) (candidate.siteValue site))).re =
      candidate.score observable weight := by
  unfold score siteValue
  have h := C.localLaw_complexMean_parameter (fun x =>
    weight (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)) *
    observable (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))
      (candidate.value (C.retainedParameter x)))
  simp only [C.retainedParameter_parameter] at h
  exact congrArg Complex.re h

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
