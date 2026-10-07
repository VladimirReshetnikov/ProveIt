import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairLongUniformFactors

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
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

def longJointOrbit (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) :
    ∀ i : Option Pivot,
      (optionFactors D (fun j => (F.native j).model) i).filtration.realification.PolynomialOrbit
        (fun _ : {i // keepLong i} => 1) :=
  fun i => (optionFactors D (fun j => (F.native j).model) i).filtration.polynomialOrbitRealChart
    (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
    ((F.chart a).axisPolynomial keepLong (fun _ => 0))
    ((F.chart a).axisPolynomial_support keepLong (fun _ => 0)) (F.jointOrbit a i)

def LongCommonFactors
    (keepLong : LayerSamplerVariables G I n B → Prop)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω)
    {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i})) (qVertical qCommon : ℝ) : Prop :=
  ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
    (v : Fin (Fintype.card α) →
      (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
    (den : ℕ) (H' : Finset Ω),
    H' ⊆ H ∧ 0 < outer.mass H' ∧
    Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * outer.mass H ≤ outer.mass H' ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule
      ((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF)
      ω W.toSubmodule ∧
    (∀ i k, rationalLogHeight
      (((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis
        e ω hF).repr (v i) k) ≤ qCommon) ∧
    (∀ j x, x ∈ (optionProduct D (fun j => (F.native j).model)).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional ((pairFrequency (F.η j) (theta j)).comp
        (optionPairProjection j).toLinearMap) x = 0) ∧
    0 < den ∧ (den : ℝ) ≤ Real.exp qCommon ∧
    ∀ a ∈ H', (optionProduct D (fun j => (F.native j).model)).filtration.HasCommonRefilteredOrbitFactors
      e ω hF (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) qCommon den W
      ⟨⟨(piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.longJointOrbit keepLong a)).log,
        (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.longJointOrbit keepLong a)).property⟩⟩

end AllocatedExternalCandidateSpatialNativeFamily

private theorem compose_exponential_mass_losses {a b x y z : ℝ}
    (hfirst : Real.exp (-a) * x ≤ y) (hsecond : Real.exp (-b) * y ≤ z) :
    Real.exp (-(a + b)) * x ≤ z := by
  calc
    _ = Real.exp (-b) * (Real.exp (-a) * x) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hfirst (Real.exp_pos _).le).trans hsecond

theorem exists_allocatedExternalCandidateSpatialNativeFamily_long_common_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

    {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (F.native j).model)).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
      (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight
        ((optionProduct D (fun j => (F.native j).model)).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
    ∀ (keepLong : LayerSamplerVariables G I n B → Prop),
      (∀ i, keepLong i → keep i) →
    ∀ [Nonempty {i // keepLong i}], (Fintype.card {i // keepLong i} : ℝ) ≤ bnd →
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.LongCommonFactors keepLong outer H e ω hF qVertical qCommon := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedExternalCandidateTaggedPairFamily_long_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Ω Pivot _ _ LG LM _ _ _ _ _ _ _ _ d₀ t D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget outer H hH hcorr
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost jointCost P keepLong hLongSub _ hkeep hlong hcommonLong
  obtain ⟨retained, hretSub, hretPos, hretMass, selected,
    _hchart, _hcandidate, _hreference, _htwist, heta, _hambient, hjoint⟩ :=
    F.exists_taggedPairFamily outer H hH hpq hprecision hfrequency hbudget hcorr
  have hselectedCommon := hcommon (A := A) (D := D)
    (E := fun j => (F.native j).model) (H := retained) hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he outer hretPos selected keepLong hLongSub hkeep hlong hcommonLong
  obtain ⟨W, v, den, H', hsub, hpos, hmass, hspan, hgraded, hheight, hzero,
    hden, hdenBound, hfactor⟩ := hselectedCommon
  refine ⟨selected.θ, W, v, den, H', fun a ha => hretSub (hsub ha), hpos,
    ?_, hspan, hgraded, hheight, ?_, hden, hdenBound, ?_⟩
  · apply compose_exponential_mass_losses (hsecond := hmass)
    simpa only [neg_mul] using hretMass
  · simpa only [heta] using hzero
  · intro a ha
    have hj : selected.extendedLongJointOrbit keepLong a = F.longJointOrbit keepLong a := by
      rw [selected.extendedLongJointOrbit_mem keepLong a (hsub ha)]
      unfold AllocatedExternalCandidateTaggedPairFamily.longJointOrbit
        AllocatedExternalCandidateSpatialNativeFamily.longJointOrbit
      rw [hjoint ⟨a, hsub ha⟩]
      rfl
    simpa only [hj] using hfactor a ha

end

end Erdos3.VectorPolynomial

end

end OAI
