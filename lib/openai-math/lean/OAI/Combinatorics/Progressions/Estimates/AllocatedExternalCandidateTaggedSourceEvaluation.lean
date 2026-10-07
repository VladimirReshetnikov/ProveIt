/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep

namespace OAI

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

theorem localLaw_complexMean_eq_fullSliceLaw_site (f : A.Site → ℂ) :
    C.localLaw.complexMean f =
      (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f (C.site t.val t.property)) := by
  let f' : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    fun x => if hx : x ∈ integerBox A.sides then f ⟨x, hx⟩ else 0
  calc
    C.localLaw.complexMean f = C.localLaw.complexMean (fun site => f' site.val) := by
      apply congrArg C.localLaw.complexMean
      funext site
      simp only [f', dite_eq_left site.property]
    _ = (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f' (C.parameter t.val)) := C.localLaw_complexMean_eq_fullSliceLaw f'
    _ = _ := by
      apply congrArg (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
      funext t
      simp only [f', dite_eq_left (C.parameter_mem t.val t.property)]
      rfl

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

@[simp] theorem withKeep_siteValue
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)
    (site : A.Site) :
    (candidate.withKeep keep hkeep).siteValue site = candidate.siteValue site := by
  cases hkeep
  rfl

@[simp] theorem siteValue_site (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    candidate.siteValue (C.site u hu) = candidate.value u := by
  change candidate.value (C.retainedParameter (C.parameter u)) = candidate.value u
  rw [C.retainedParameter_parameter]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {Y : Type*} {w : Y → ℕ} (reference : D.Niltest w)

@[simp] theorem withOrbit_eval (u : C.Variables → ℤ) :
    (reference.withOrbit candidate.orbit).eval u =
      reference.observable (candidate.value u) := rfl

@[simp] theorem withOrbit_eval_site (site : A.Site) :
    (reference.withOrbit candidate.orbit).eval (C.retainedParameter site.val) =
      reference.observable (candidate.siteValue site) := rfl

end AllocatedExternalLocalCandidate

end

end Erdos3.VectorPolynomial

end

end OAI
