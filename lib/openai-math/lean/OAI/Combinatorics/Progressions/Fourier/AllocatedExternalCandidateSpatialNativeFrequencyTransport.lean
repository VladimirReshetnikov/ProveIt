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

def withFrequencies (eta : Pivot → LG →ₗ[ℚ] ℚ) (h : F.η = eta) :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip :=
  { F with
    η := eta
    hηheight := by simpa only [← h] using F.hηheight
    hη := by simpa only [← h] using F.hη }

variable (eta : Pivot → LG →ₗ[ℚ] ℚ) (h : F.η = eta)

@[simp] theorem withFrequencies_eta : (F.withFrequencies eta h).η = eta := rfl

@[simp] theorem withFrequencies_sourceChart :
    (F.withFrequencies eta h).sourceChart = F.sourceChart := rfl

@[simp] theorem withFrequencies_sourceCandidate :
    (F.withFrequencies eta h).sourceCandidate = F.sourceCandidate := rfl

@[simp] theorem withFrequencies_reference :
    (F.withFrequencies eta h).reference = F.reference := rfl

@[simp] theorem withFrequencies_nativeValue :
    (F.withFrequencies eta h).nativeValue = F.nativeValue := rfl

@[simp] theorem withFrequencies_native :
    (F.withFrequencies eta h).native = F.native := rfl

@[simp] theorem withFrequencies_twist :
    (F.withFrequencies eta h).twist = F.twist := rfl

@[simp] theorem withFrequencies_chart (a : Ω) :
    (F.withFrequencies eta h).chart a = F.chart a := rfl

@[simp] theorem withFrequencies_candidate (a : Ω) :
    (F.withFrequencies eta h).candidate a = F.candidate a := rfl

@[simp] theorem withFrequencies_localTest (a : Ω) (j : Pivot) :
    (F.withFrequencies eta h).localTest a j = F.localTest a j := rfl

@[simp] theorem withFrequencies_jointOrbit (a : Ω) :
    (F.withFrequencies eta h).jointOrbit a = F.jointOrbit a := rfl

@[simp] theorem withFrequencies_physicalBox (a : Ω)
    (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    (F.withFrequencies eta h).physicalBox a u = F.physicalBox a u := rfl

@[simp] theorem withFrequencies_sitePhysicalBox (a : Ω) (site : A.Site) :
    (F.withFrequencies eta h).sitePhysicalBox a site = F.sitePhysicalBox a site := rfl

@[simp] theorem withFrequencies_correlation (a : Ω) (j : Pivot) :
    (F.withFrequencies eta h).correlation a j = F.correlation a j := rfl

theorem withFrequencies_withBudget (q : ℝ) (hpq : p ≤ q) :
    (F.withFrequencies eta h).withBudget q hpq =
      (F.withBudget q hpq).withFrequencies eta h := rfl

theorem withFrequencies_withFactorBudget :
    (F.withFrequencies eta h).withFactorBudget =
      F.withFactorBudget.withFrequencies eta h := rfl

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
