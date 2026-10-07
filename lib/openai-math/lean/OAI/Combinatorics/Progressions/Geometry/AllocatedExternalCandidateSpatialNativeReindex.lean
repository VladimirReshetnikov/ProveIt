/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

def reindex {Ω' : Type*} (f : Ω' → Ω) :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω' Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip where
  hpoly := F.hpoly
  hτ1 := F.hτ1
  hξ := F.hξ
  hσ1 := F.hσ1
  Cgeo := F.Cgeo
  hCgeo := F.hCgeo
  hchart := F.hchart
  hsmall := F.hsmall
  sourceChart := fun a => F.sourceChart (f a)
  keep_eq := fun a => F.keep_eq (f a)
  sourceCandidate := fun a => F.sourceCandidate (f a)
  reference := fun a => F.reference (f a)
  nativeValue := F.nativeValue
  native := F.native
  twist := fun a => F.twist (f a)
  hp := F.hp
  hpLocal := F.hpLocal
  hr := F.hr
  hcost := F.hcost
  hlocal := F.hlocal
  hnative := F.hnative
  hperiod := fun a => F.hperiod (f a)
  hvariation := F.hvariation
  hV := fun a => F.hV (f a)
  η := F.η
  hηheight := F.hηheight
  hη := fun a => F.hη (f a)
  hK := F.hK

@[simp] theorem reindex_nativeValue {Ω' : Type*} (f : Ω' → Ω) :
    (F.reindex f).nativeValue = F.nativeValue := rfl

@[simp] theorem reindex_native {Ω' : Type*} (f : Ω' → Ω) :
    (F.reindex f).native = F.native := rfl

@[simp] theorem reindex_η {Ω' : Type*} (f : Ω' → Ω) :
    (F.reindex f).η = F.η := rfl

@[simp] theorem reindex_sourceChart {Ω' : Type*} (f : Ω' → Ω) (a : Ω') :
    (F.reindex f).sourceChart a = F.sourceChart (f a) := rfl

@[simp] theorem reindex_sourceCandidate {Ω' : Type*} (f : Ω' → Ω) (a : Ω') :
    (F.reindex f).sourceCandidate a = F.sourceCandidate (f a) := rfl

@[simp] theorem reindex_correlation {Ω' : Type*} (f : Ω' → Ω) (a : Ω') (j : Pivot) :
    (F.reindex f).correlation a j = F.correlation (f a) j := rfl

@[simp] theorem reindex_jointOrbit {Ω' : Type*} (f : Ω' → Ω) (a : Ω') :
    (F.reindex f).jointOrbit a = F.jointOrbit (f a) := rfl

def positiveMassRetract [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (a : Ω) : {a // a ∈ H} := by
  have hne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty,
      lt_self_iff_false] at hH)
  exact if ha : a ∈ H then ⟨a, ha⟩ else ⟨hne.choose, hne.choose_spec⟩

@[simp] theorem positiveMassRetract_mem [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (a : Ω) (ha : a ∈ H) :
    positiveMassRetract outer H hH a = ⟨a, ha⟩ := by
  simp only [positiveMassRetract, dite_eq_left ha]

variable [Fintype Ω] (outer : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (hH : 0 < outer.mass H)
    (FH : AllocatedExternalCandidateSpatialNativeFamily A Deck {a // a ∈ H} Pivot
      D Fmark φ marked keep cost p pLocal pNative r periodCap coverCap Lip)

def extend : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip :=
  FH.reindex (positiveMassRetract outer H hH)

@[simp] theorem extend_nativeValue :
    (FH.extend outer H hH).nativeValue = FH.nativeValue := rfl

@[simp] theorem extend_native :
    (FH.extend outer H hH).native = FH.native := rfl

@[simp] theorem extend_η :
    (FH.extend outer H hH).η = FH.η := rfl

@[simp] theorem extend_sourceChart (a : Ω) (ha : a ∈ H) :
    (FH.extend outer H hH).sourceChart a = FH.sourceChart ⟨a, ha⟩ := by
  change FH.sourceChart (positiveMassRetract outer H hH a) = _
  rw [positiveMassRetract_mem outer H hH a ha]

@[simp] theorem extend_sourceCandidate (a : Ω) (ha : a ∈ H) :
    HEq ((FH.extend outer H hH).sourceCandidate a) (FH.sourceCandidate ⟨a, ha⟩) := by
  change HEq (FH.sourceCandidate (positiveMassRetract outer H hH a)) _
  rw [positiveMassRetract_mem outer H hH a ha]

@[simp] theorem extend_correlation (a : Ω) (ha : a ∈ H) (j : Pivot) :
    (FH.extend outer H hH).correlation a j = FH.correlation ⟨a, ha⟩ j := by
  change FH.correlation (positiveMassRetract outer H hH a) j = _
  rw [positiveMassRetract_mem outer H hH a ha]

@[simp] theorem extend_jointOrbit (a : Ω) (ha : a ∈ H) :
    (FH.extend outer H hH).jointOrbit a = FH.jointOrbit ⟨a, ha⟩ := by
  change FH.jointOrbit (positiveMassRetract outer H hH a) = _
  rw [positiveMassRetract_mem outer H hH a ha]

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
