import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeLongCommonFactors
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalLocalCandidateOptionQuotientChart

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ τ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ} {v : τ → ℕ}

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom

theorem piRealOrbit_polynomialOrbitRealChart_log
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (piRealOrbit F (fun i => (F i).polynomialOrbitRealChart w v β hβ (g i))).log =
      realChartSubstitute β (piRealOrbit F g).log := by
  simp only [piRealOrbit, PolynomialOrbit.log, polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
    ((F i).polynomialOrbitRealChart w v β hβ (g i)).log =
      realChartSubstitute β
        (VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ) (g i).log)
  rw [polynomialOrbitRealChart_log]
  exact (realChartSubstitute_map β (realProductSingle i) (g i).log).symm

attribute [local irreducible] piRealOrbit

theorem piRealOrbit_polynomialOrbitRealChart
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    piRealOrbit F (fun i => (F i).polynomialOrbitRealChart w v β hβ (g i)) =
      (pi F).polynomialOrbitRealChart w v β hβ (piRealOrbit F g) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  exact (piRealOrbit_polynomialOrbitRealChart_log F g β hβ).trans
    ((pi F).polynomialOrbitRealChart_log w v β hβ (piRealOrbit F g)).symm

theorem piRealOrbit_polynomialOrbitRealChart_coordinates
    (g : ∀ i, (F i).realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (pi F).realification.polynomialOrbitCoordinates v
      (piRealOrbit F (fun i => (F i).polynomialOrbitRealChart w v β hβ (g i))) =
        (pi F).weightedAdaptedRealChartHom w v β hβ
          ((pi F).realification.polynomialOrbitCoordinates w (piRealOrbit F g)) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact (piRealOrbit_polynomialOrbitRealChart_log F g β hβ).trans
    ((pi F).weightedAdaptedRealChartHom_coord w v β hβ
      ((pi F).realification.polynomialOrbitCoordinates w (piRealOrbit F g))).symm

end Erdos3.NilpotentLieFiltration

end

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

def CommonFactors
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
      e ω hF (fun i : {i // keep i} => (A.sides i.val : ℝ)) qCommon den W
      ⟨⟨(piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.jointOrbit a)).log,
        (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.jointOrbit a)).property⟩⟩

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

theorem exists_allocatedExternalCandidateSpatialNativeFamily_common_factors
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
    ∀ [Nonempty {i // keep i}], (Fintype.card {i // keep i} : ℝ) ≤ bnd →
      (∀ i : {i // keep i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keep i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.CommonFactors outer H e ω hF qVertical qCommon := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedExternalCandidateTaggedPairFamily_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Ω Pivot _ _ LG LM _ _ _ _ _ _ _ _ d₀ t D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget outer H hH hcorr
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost jointCost P _ hkeep hlong hcommonLong
  obtain ⟨retained, hretSub, hretPos, hretMass, selected,
    _hchart, _hcandidate, _hreference, _htwist, heta, _hambient, hjoint⟩ :=
    F.exists_taggedPairFamily outer H hH hpq hprecision hfrequency hbudget hcorr
  have hselectedCommon := hcommon (A := A) (D := D)
    (E := fun j => (F.native j).model) (H := retained) hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he outer hretPos selected hkeep hlong hcommonLong
  obtain ⟨W, v, den, H', hsub, hpos, hmass, hspan, hgraded, hheight, hzero,
    hden, hdenBound, hfactor⟩ := hselectedCommon
  refine ⟨selected.θ, W, v, den, H', fun a ha => hretSub (hsub ha), hpos,
    ?_, hspan, hgraded, hheight, ?_, hden, hdenBound, ?_⟩
  · apply compose_exponential_mass_losses (hsecond := hmass)
    simpa only [neg_mul] using hretMass
  · simpa only [heta] using hzero
  · intro a ha
    have hj := selected.extendedJointOrbit_mem a (hsub ha)
    rw [hjoint ⟨a, hsub ha⟩] at hj
    simpa only [hj] using hfactor a ha

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

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

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

def actualSourceProblemOn
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained) :
    AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold where
  productive := retained
  mass := hmass
  chart a := F.chart a.val
  chart_path a := hpath a.val (hsub a.property)
  centerLift := sourceCenter
  chart_centerLift a := hcenter a.val (hsub a.property)
  frozen_side a := hfrozen a.val (hsub a.property)
  candidate a := F.candidate a.val
  score a := by
    exact (hscore a.val (hsub a.property)).trans_eq
      ((F.sourceCandidate a.val).withKeep_score
        (observable := observable) (weight := weight) keep (F.keep_eq a.val)).symm

def actualJointProblemOn
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained) :=
  (F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass).optionJoint
      (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)

@[simp] theorem actualJointProblemOn_productive
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained) :
    (F.actualJointProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass).productive = retained := rfl

@[simp] theorem actualJointProblemOn_keep
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained) (a : retained) :
    ((F.actualJointProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass).chart a).keep = keep := rfl

@[simp] theorem actualJointProblemOn_orbit
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained) (a : retained) :
    ((F.actualJointProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass).candidate a).orbit =
      piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
        (F.jointOrbit a.val) := by
  change piRealOrbit _ ((F.candidate a.val).optionJointLocalOrbits
    (fun j => (F.native j).model)
    (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)) = _
  congr 1

theorem CommonFactors.exists_actualJointProblem
    {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    {qVertical qCommon : ℝ} (hcommon : F.CommonFactors A.law H e ω hF qVertical qCommon) :
    ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
      (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
      0 < A.law.mass retained ∧
      ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
        (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
        (v : Fin (Fintype.card α) →
          (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
        (den : ℕ),
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
        let P := F.actualJointProblemOn H sourceCenter hpath hcenter hfrozen observable weight
          scoreThreshold hscore retained hsub hmass
        ∀ a : P.productive,
          (optionProduct D (fun j => (F.native j).model)).filtration.HasCommonRefilteredOrbitFactors
            e ω hF (fun i : {i // keep i} => (A.sides i.val : ℝ)) qCommon den W
            ⟨⟨(P.candidate a).orbit.log, (P.candidate a).orbit.property⟩⟩ := by
  obtain ⟨theta, W, v, den, retained, hsub, hpos, hmass, hspan, hgraded,
    hheight, hzero, hden, hdenBound, hfactor⟩ := hcommon
  refine ⟨retained, hsub, hmass, hpos, theta, W, v, den, hspan, hgraded,
    hheight, hzero, hden, hdenBound, ?_⟩
  intro P a
  exact hfactor a.val a.property

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

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

def jointPolynomialOrbit (a : Ω) :
    ((optionProduct D (fun j => (F.native j).model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : {i // keep i} => 1)).Group :=
  ⟨⟨(piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
      (F.jointOrbit a)).log,
    (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
      (F.jointOrbit a)).property⟩⟩

variable (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (js : List Pivot)
    {α κ : Type*} [Fintype α] [Fintype κ]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))

abbrev quotientFiltration := D.filtration.pivotProductQuotientFiltration φ F.η js
  (NilpotentLieFiltration.pi (fun j => (F.native j).model.filtration))

variable
    (c : Basis κ ℚ ((LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) × (∀ j, (F.native j).L)))
    (ν : κ → ℕ)
    (hQ : ∀ k, (F.quotientFiltration js).layer k = Submodule.span ℚ (c '' {i | k ≤ ν i}))

def QuotientFactors (qVertical qCommon pProj : ℝ) : Prop :=
  ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
    (v : Fin (Fintype.card α) → (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
    (V : LieSubalgebra ℚ (F.quotientFiltration js).AssociatedGraded) (den denQ : ℕ) (H' : Finset Ω),
    H' ⊆ H ∧ 0 < outer.mass H' ∧
    Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * outer.mass H ≤ outer.mass H' ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule ((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF)
      ω W.toSubmodule ∧
    (∀ i k, rationalLogHeight
      (((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ qCommon) ∧
    (∀ j x, x ∈ (optionProduct D (fun j => (F.native j).model)).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional ((pairFrequency (F.η j) (theta j)).comp
        (optionPairProjection j).toLinearMap) x = 0) ∧
    0 < den ∧ (den : ℝ) ≤ Real.exp qCommon ∧
    (∀ a ∈ H', (optionProduct D (fun j => (F.native j).model)).filtration.HasCommonRefilteredOrbitFactors
      e ω hF (fun i : {i // keep i} => (A.sides i.val : ℝ)) qCommon den W
      (F.jointPolynomialOrbit a)) ∧
    V = optionCommonPivotQuotientFast D (fun j => (F.native j).model) φ F.η js W ∧
    0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
    (∀ a ∈ H', ∃ El Pl Rl :
      (F.quotientFiltration js).RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1),
      El * Pl * Rl = (F.quotientFiltration js).realPolynomialSymbolHom c ν hQ (fun _ => 1)
        ((optionProduct D (fun j => (F.native j).model)).filtration.realPolynomialGroupMap (F.quotientFiltration js)
          (optionPivotProductQuotientMap D φ F.η js)
          (optionPivotProductQuotientMap_mem_layer D (fun j => (F.native j).model) φ F.η js)
          (fun _ => 1) (F.jointPolynomialOrbit a)) ∧
      Pl.coord ∈ realificationLieSubalgebra
        ((F.quotientFiltration js).symbolPointwiseSubalgebra c ν hQ (fun _ => 1) V) ∧
      (F.quotientFiltration js).SymbolSlowBound c ν hQ (fun _ => 1)
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) (Real.exp ((pProj + 2) ^ 3 + qCommon)) El ∧
      (F.quotientFiltration js).SymbolRationalGrid c ν hQ (fun _ => 1) denQ Rl) ∧
    BasisGradedSubmodule ((F.quotientFiltration js).associatedGradedBasis c ν hQ) ν V.toSubmodule ∧
    (∀ x ∈ (F.quotientFiltration js).gradedRefiltrationLayer V s,
      D.filtration.pivotProductMarkedMap φ F.η js x = 0 → x = 0) ∧
    (∀ (Gmark : NilpotentLieFiltration (LM × (∀ j, (F.native j).L)) s)
      (hmarked : ∀ k, ∀ x ∈ (F.quotientFiltration js).layer k,
        D.filtration.pivotProductMarkedMap φ F.η js x ∈ Gmark.layer k),
      ∀ a ∈ V, basisGradeProjection ((F.quotientFiltration js).associatedGradedBasis c ν hQ) ν s a = a →
        (F.quotientFiltration js).associatedGradedMap Gmark (D.filtration.pivotProductMarkedMap φ F.η js)
          hmarked a = 0 → a = 0)

private def projectedData
    (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
    (den : ℕ) (H' : Finset Ω) (qCommon pProj : ℝ) : Prop :=
  let V := optionCommonPivotQuotientFast D (fun j => (F.native j).model) φ F.η js W
  ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
    (∀ a ∈ H', ∃ El Pl Rl :
      (F.quotientFiltration js).RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1),
      El * Pl * Rl = (F.quotientFiltration js).realPolynomialSymbolHom c ν hQ (fun _ => 1)
        ((optionProduct D (fun j => (F.native j).model)).filtration.realPolynomialGroupMap (F.quotientFiltration js)
          (optionPivotProductQuotientMap D φ F.η js)
          (optionPivotProductQuotientMap_mem_layer D (fun j => (F.native j).model) φ F.η js)
          (fun _ => 1) (F.jointPolynomialOrbit a)) ∧
      Pl.coord ∈ realificationLieSubalgebra
        ((F.quotientFiltration js).symbolPointwiseSubalgebra c ν hQ (fun _ => 1) V) ∧
      (F.quotientFiltration js).SymbolSlowBound c ν hQ (fun _ => 1)
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) (Real.exp ((pProj + 2) ^ 3 + qCommon)) El ∧
      (F.quotientFiltration js).SymbolRationalGrid c ν hQ (fun _ => 1) denQ Rl) ∧
    BasisGradedSubmodule ((F.quotientFiltration js).associatedGradedBasis c ν hQ) ν V.toSubmodule ∧
    (∀ x ∈ (F.quotientFiltration js).gradedRefiltrationLayer V s,
      D.filtration.pivotProductMarkedMap φ F.η js x = 0 → x = 0) ∧
    (∀ (Gmark : NilpotentLieFiltration (LM × (∀ j, (F.native j).L)) s)
      (hmarked : ∀ k, ∀ x ∈ (F.quotientFiltration js).layer k,
        D.filtration.pivotProductMarkedMap φ F.η js x ∈ Gmark.layer k),
      ∀ a ∈ V, basisGradeProjection ((F.quotientFiltration js).associatedGradedBasis c ν hQ) ν s a = a →
        (F.quotientFiltration js).associatedGradedMap Gmark (D.filtration.pivotProductMarkedMap φ F.η js)
          hmarked a = 0 → a = 0)

omit [Fintype κ] in
private theorem assembleQuotientFactors
    {qVertical qCommon pProj : ℝ}
    (hcommon : F.CommonFactors outer H e ω hF qVertical qCommon)
    (hproject : ∀ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
      (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (den : ℕ) (H' : Finset Ω),
      BasisGradedSubmodule
        ((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF)
        ω W.toSubmodule →
      (∀ j x, x ∈ (optionProduct D (fun j => (F.native j).model)).filtration.realGradedRefiltrationLayer W s →
        realifyFunctional ((pairFrequency (F.η j) (theta j)).comp
          (optionPairProjection j).toLinearMap) x = 0) →
      0 < den → (den : ℝ) ≤ Real.exp qCommon →
      (∀ a ∈ H', (optionProduct D (fun j => (F.native j).model)).filtration.HasCommonRefilteredOrbitFactors
        e ω hF (fun i : {i // keep i} => (A.sides i.val : ℝ)) qCommon den W
        (F.jointPolynomialOrbit a)) →
      F.projectedData js c ν hQ W den H' qCommon pProj) :
    F.QuotientFactors outer H js e ω hF c ν hQ qVertical qCommon pProj := by
  obtain ⟨theta, W, v, den, H', hsub, hmass, hmassLower, hspan, hgraded, hheightW,
    hzero, hden, hdenBound, hfactor⟩ := hcommon
  obtain ⟨denQ, hdenQ, hdenQBound, hdiv, hquotient, hquotientGraded, hkernel, hgradedKernel⟩ :=
    hproject theta W den H' hgraded hzero hden hdenBound hfactor
  unfold QuotientFactors
  refine ⟨theta, W, v, ?_⟩
  let V : LieSubalgebra ℚ (F.quotientFiltration js).AssociatedGraded :=
    optionCommonPivotQuotientFast D (fun j => (F.native j).model) φ F.η js W
  refine ⟨V, den, denQ, H', ?_⟩
  refine And.intro hsub ?_
  refine And.intro hmass ?_
  refine And.intro hmassLower ?_
  refine And.intro hspan ?_
  refine And.intro hgraded ?_
  refine And.intro hheightW ?_
  refine And.intro hzero ?_
  refine And.intro hden ?_
  refine And.intro hdenBound ?_
  refine And.intro hfactor ?_
  refine And.intro rfl ?_
  refine And.intro hdenQ ?_
  refine And.intro hdenQBound ?_
  refine And.intro hdiv ?_
  exact ⟨hquotient, hquotientGraded, hkernel, hgradedKernel⟩

theorem CommonFactors.toQuotientFactors
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν)]
    {qVertical qCommon pProj : ℝ}
    (hcommon : F.CommonFactors outer H e ω hF qVertical qCommon)
    {height : ℕ} (hheight : 1 ≤ height)
    (hentries : ∀ i j,
      RationalHeightLE (c.repr (optionPivotProductQuotientMap D φ F.η js (e j)) i) height)
    (hpProj : 0 ≤ pProj) (hqProj : qCommon ≤ pProj)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω) : ℝ) ≤ pProj)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν) : ℝ) ≤ pProj)
    (hheightProj : (height : ℝ) ≤ Real.exp pProj) :
    F.QuotientFactors outer H js e ω hF c ν hQ qVertical qCommon pProj := by
  apply assembleQuotientFactors F outer H js e ω hF c ν hQ hcommon
  intro theta W den H' hgraded hzero hden hdenBound hfactor
  have hside (i : {i // keep i}) : (0 : ℝ) < A.sides i.val :=
    Nat.cast_pos.mpr (A.sides_pos i.val)
  have hdenProj : (den : ℝ) ≤ Real.exp pProj :=
    hdenBound.trans (Real.exp_le_exp.mpr hqProj)
  dsimp only [projectedData, quotientFiltration]
  exact exists_optionCommonPivotQuotient_family_symbol_factors
    D (fun j => (F.native j).model) φ F.η js e ω hF c ν hQ hheight hden hentries hpProj
    hsource htarget hheightProj hdenProj W hgraded theta hzero
    H' (fun i : {i // keep i} => (A.sides i.val : ℝ)) hside qCommon
    F.jointPolynomialOrbit hfactor

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

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

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (js : List Pivot)
    {dQ : ℕ}
    (Q : RationalFilteredNilmanifold (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)

def ActualAdaptedPivotQuotientFactors (qVertical qCommon pProj : ℝ) : Prop :=
  ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
    (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
    0 < A.law.mass retained ∧
    ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
      (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (v : Fin (Fintype.card α) →
        (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (den : ℕ),
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
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
      let F₀ := (optionProduct D (fun j => (F.native j).model)).filtration
      let FQ := adapted.model.filtration
      let ψ := optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))
      let hψ := D.optionQuotientMap_mem_layer
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)
      let V := W.map (F₀.associatedGradedMap FQ ψ hψ)
      let vQ := F₀.gradedImageSpanningFamily FQ ψ hψ v
      ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
        Submodule.span ℚ (Set.range vQ) = V.toSubmodule ∧
        BasisGradedSubmodule
          (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
          adapted.weight V.toSubmodule ∧
        (∀ a i, rationalLogHeight
          ((FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers).repr
            (vQ a) i) ≤ (pProj + 2) ^ 4) ∧
        (∀ z : target.productive,
          FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
            (fun i : {i // keep i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + qCommon) denQ V
            ⟨⟨(target.candidate z).orbit.log, (target.candidate z).orbit.property⟩⟩) ∧
        (∀ x ∈ FQ.gradedRefiltrationLayer V s,
          optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x = 0 →
          x = 0) ∧
        (∀ (Gmark : NilpotentLieFiltration
            (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i) s)
          (hmarked : ∀ k, ∀ x ∈ FQ.layer k,
            optionMarkedLieMap (L := fun j => (F.native j).L)
              (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x ∈
                Gmark.layer k),
          ∀ a ∈ V,
            basisGradeProjection
              (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
              adapted.weight s a = a →
            FQ.associatedGradedMap Gmark
              (optionMarkedLieMap (L := fun j => (F.native j).L)
                (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
              hmarked a = 0 → a = 0)

theorem CommonFactors.toActualAdaptedPivotQuotientFactors
    {qVertical qCommon pProj : ℝ}
    (hcommon : F.CommonFactors A.law H e ω hF qVertical qCommon)
    {height : ℕ}
    (hentries : ∀ i j, RationalHeightLE
      (adapted.basis.repr
        (optionMarkedLieMap (L := fun j => (F.native j).L)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) (e j)) i) height)
    (hpProj : 0 ≤ pProj) (hqProj : qCommon ≤ pProj)
    (hsource : (Fintype.card α : ℝ) ≤ pProj)
    (htarget : (finrank ℚ (∀ i : Option Pivot,
      optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (fun j => (F.native j).L) i) : ℝ) ≤ pProj)
    (hheight : (height : ℝ) ≤ Real.exp pProj) :
    F.ActualAdaptedPivotQuotientFactors H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      qVertical qCommon pProj := by
  obtain ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, hfactor⟩ :=
    hcommon.exists_actualJointProblem F H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore e ω hF
  let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass
  have hproject := source.exists_withKeep_adaptedOptionQuotient_common_factors
    (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
    (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
    keep (fun _ => rfl) e ω hF hentries hpProj hsource htarget hheight den hden
    (hdenBound.trans (Real.exp_le_exp.mpr hqProj)) W v hv hW
    (fun a i => (hvH a i).trans hqProj) hfactor
  obtain ⟨denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ⟩ := hproject
  refine ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ, ?_, ?_⟩
  · exact optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
      D (fun j => (F.native j).model) φ F.η js hker W theta hzero Q hQ
      e ω hF adapted.basis adapted.weight adapted.layers hW
  · exact optionNativeCommonPivotQuotientFast_graded_top_kernel
      D (fun j => (F.native j).model) φ F.η js hker W theta hzero Q hQ
      e ω hF adapted.basis adapted.weight adapted.layers hW

end AllocatedExternalCandidateSpatialNativeFamily

theorem exists_allocatedExternalCandidateSpatialNativeFamily_actual_adapted_quotient_factors
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

    {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
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
    ∀ [Nonempty {i // keep i}], (Fintype.card {i // keep i} : ℝ) ≤ bnd →
      (∀ i : {i // keep i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keep i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
    ∀ (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g))
      (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)
      {height : ℕ} {pProj : ℝ},
      (∀ i j, RationalHeightLE
        (adapted.basis.repr
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) (e j)) i) height) →
      0 ≤ pProj → qCommon ≤ pProj →
      (Fintype.card α : ℝ) ≤ pProj →
      (finrank ℚ (∀ i : Option Pivot,
        optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (fun j => (F.native j).L) i) : ℝ) ≤ pProj →
      (height : ℝ) ≤ Real.exp pProj →
      F.ActualAdaptedPivotQuotientFactors H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
        qVertical qCommon pProj := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost jointCost P _ hkeep hlong hcommonLong qCommon
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore
    js dQ Q hQ hker descended hrecovery adapted height pProj hentries hpProj hqProj
    hsource htarget hheight
  have hc : F.CommonFactors A.law H e ω hF qVertical qCommon :=
    hcommon F hpq hprecision hfrequency hbudget A.law H hH hcorr
      hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he hkeep hlong hcommonLong
  exact hc.toActualAdaptedPivotQuotientFactors F H sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
    hentries hpProj hqProj hsource htarget hheight

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialGroupMap

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

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (js : List Pivot)
    {dQ : ℕ}
    (Q : RationalFilteredNilmanifold (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)

def ActualAdaptedPivotQuotientLongFactors (qVertical qCommon pProj : ℝ) : Prop :=
  ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
    (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
    0 < A.law.mass retained ∧
    ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
      (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (v : Fin (Fintype.card α) →
        (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (den : ℕ),
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
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
      let F₀ := (optionProduct D (fun j => (F.native j).model)).filtration
      let FQ := adapted.model.filtration
      let ψ := optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))
      let hψ := D.optionQuotientMap_mem_layer
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)
      let V := W.map (F₀.associatedGradedMap FQ ψ hψ)
      let vQ := F₀.gradedImageSpanningFamily FQ ψ hψ v
      ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
        Submodule.span ℚ (Set.range vQ) = V.toSubmodule ∧
        BasisGradedSubmodule
          (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
          adapted.weight V.toSubmodule ∧
        (∀ a i, rationalLogHeight
          ((FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers).repr
            (vQ a) i) ≤ (pProj + 2) ^ 4) ∧
        (∀ z : target.productive,
          FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
            (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + qCommon) denQ V
            (FQ.weightedAdaptedRealChartHom
              (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
              ((target.chart z).axisPolynomial keepLong (fun _ => 0))
              ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
              (FQ.realification.polynomialOrbitCoordinates (fun _ => 1)
                (target.candidate z).orbit))) ∧
        (∀ x ∈ FQ.gradedRefiltrationLayer V s,
          optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x = 0 →
          x = 0) ∧
        (∀ (Gmark : NilpotentLieFiltration
            (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i) s)
          (hmarked : ∀ k, ∀ x ∈ FQ.layer k,
            optionMarkedLieMap (L := fun j => (F.native j).L)
              (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x ∈
                Gmark.layer k),
          ∀ a ∈ V,
            basisGradeProjection
              (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
              adapted.weight s a = a →
            FQ.associatedGradedMap Gmark
              (optionMarkedLieMap (L := fun j => (F.native j).L)
                (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
              hmarked a = 0 → a = 0)

theorem longJointOrbit_polynomialCoordinates (a : A.Path) :
    (optionProduct D (fun j => (F.native j).model)).filtration.realification.polynomialOrbitCoordinates
      (fun _ : {i // keepLong i} => 1)
      (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
        (F.longJointOrbit keepLong a)) =
    (optionProduct D (fun j => (F.native j).model)).filtration.weightedAdaptedRealChartHom
      (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
      ((F.chart a).axisPolynomial keepLong (fun _ => 0))
      ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))
      ((optionProduct D (fun j => (F.native j).model)).filtration.realification.polynomialOrbitCoordinates
        (fun _ : {i // keep i} => 1)
        (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.jointOrbit a))) :=
  piRealOrbit_polynomialOrbitRealChart_coordinates
    (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
    (F.jointOrbit a) ((F.chart a).axisPolynomial keepLong (fun _ => 0))
    ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))

theorem LongCommonFactors.toActualAdaptedPivotQuotientLongFactors
    {qVertical qCommon pProj : ℝ}
    (hcommon : F.LongCommonFactors keepLong A.law H e ω hF qVertical qCommon)
    {height : ℕ}
    (hentries : ∀ i j, RationalHeightLE
      (adapted.basis.repr
        (optionMarkedLieMap (L := fun j => (F.native j).L)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) (e j)) i) height)
    (hpProj : 0 ≤ pProj) (hqProj : qCommon ≤ pProj)
    (hsource : (Fintype.card α : ℝ) ≤ pProj)
    (htarget : (finrank ℚ (∀ i : Option Pivot,
      optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (fun j => (F.native j).L) i) : ℝ) ≤ pProj)
    (hheight : (height : ℝ) ≤ Real.exp pProj) :
    F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      qVertical qCommon pProj := by
  obtain ⟨theta, W, v, den, retained, hsub, hpos, hmass, hv, hW, hvH, hzero,
    hden, hdenBound, hfactor⟩ := hcommon
  let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass
  let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
    (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
    (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
  let F₀ := (optionProduct D (fun j => (F.native j).model)).filtration
  let FQ := adapted.model.filtration
  let ψ := optionMarkedLieMap (L := fun j => (F.native j).L)
    (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))
  let hψ := D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)
  obtain ⟨denQ, hdenQ, hdenQBound, hdiv, htransport⟩ :=
    F₀.exists_common_refiltered_mapped_orbit_factors
      (σ := {i // keepLong i}) FQ e ω hF
      adapted.model.basis adapted.weight adapted.model_layers ψ hψ
      hentries hpProj hsource (by simpa only [Fintype.card_fin] using htarget) hheight
      den hden (hdenBound.trans (Real.exp_le_exp.mpr hqProj))
  obtain ⟨hvQ, hWQ, hvQH⟩ :=
    F₀.gradedImage_bounded_spanning FQ ψ hψ e ω hF
      adapted.model.basis adapted.weight adapted.model_layers W v hv hW
      hpProj hsource (fun a i => (hvH a i).trans hqProj)
      (fun i j => rationalLogHeight_le_of_height (hentries j i) hheight)
  have hfactorLong (z : source.productive) :
      F₀.HasCommonRefilteredOrbitFactors e ω hF
        (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) qCommon den W
        (F₀.weightedAdaptedRealChartHom
          (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
          ((source.chart z).axisPolynomial keepLong (fun _ => 0))
          ((source.chart z).axisPolynomial_support keepLong (fun _ => 0))
          (F₀.realification.polynomialOrbitCoordinates (fun _ => 1)
            ((source.optionJoint (fun j => (F.native j).model)
              (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)).candidate z).orbit)) := by
    have hc := hfactor z.val z.property
    change F₀.HasCommonRefilteredOrbitFactors e ω hF
      (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) qCommon den W
      (F₀.realification.polynomialOrbitCoordinates (fun _ => 1)
        (piRealOrbit (fun i => (optionFactors D (fun j => (F.native j).model) i).filtration)
          (F.longJointOrbit keepLong z.val))) at hc
    rw [F.longJointOrbit_polynomialCoordinates keepLong z.val] at hc
    exact hc
  refine ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, ?_, ?_, ?_⟩
  · intro z
    have ht := htransport (fun i => (A.sides i.val : ℝ))
      (fun i => by exact_mod_cast A.sides_pos i.val) qCommon W _ (hfactorLong z)
    have he := ((source.withKeep keep (fun _ => rfl)).candidate z).optionJoint_lieQuotient_chart_polynomialCoordinates
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        ((target.chart z).axisPolynomial keepLong (fun _ => 0))
        ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
    exact Eq.mpr (congrArg
      (FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
        (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + qCommon) denQ
        (W.map (F₀.associatedGradedMap FQ ψ hψ))) he) ht
  · exact optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
      D (fun j => (F.native j).model) φ F.η js hker W theta hzero Q hQ
      e ω hF adapted.basis adapted.weight adapted.layers hW
  · exact optionNativeCommonPivotQuotientFast_graded_top_kernel
      D (fun j => (F.native j).model) φ F.η js hker W theta hzero Q hQ
      e ω hF adapted.basis adapted.weight adapted.layers hW

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

theorem exists_allocatedExternalCandidateSpatialNativeFamily_actual_adapted_long_quotient_factors
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

    {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
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
    ∀ (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g))
      (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)
      {height : ℕ} {pProj : ℝ},
      (∀ i j, RationalHeightLE
        (adapted.basis.repr
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) (e j)) i) height) →
      0 ≤ pProj → qCommon ≤ pProj →
      (Fintype.card α : ℝ) ≤ pProj →
      (finrank ℚ (∀ i : Option Pivot,
        optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (fun j => (F.native j).L) i) : ℝ) ≤ pProj →
      (height : ℝ) ≤ Real.exp pProj →
      F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
        qVertical qCommon pProj := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_long_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost jointCost P keepLong hLongSub _ hkeep hlong hcommonLong qCommon
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore
    js dQ Q hQ hker descended hrecovery adapted height pProj hentries hpProj hqProj
    hsource htarget hheight
  have hc : F.LongCommonFactors keepLong A.law H e ω hF qVertical qCommon :=
    hcommon F hpq hprecision hfrequency hbudget A.law H hH hcorr
      hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he keepLong hLongSub hkeep hlong hcommonLong
  exact hc.toActualAdaptedPivotQuotientLongFactors F keepLong H sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
    hentries hpProj hqProj hsource htarget hheight

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

theorem exists_allocatedExternalCandidateSpatialNativeFamily_native_long_geometry_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ Cgeometry C Cbasis K T : ℕ, 2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
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

    {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ (pGeometry : ℝ), 2 ≤ pGeometry → D.GeometryComplexityLE pGeometry →
      pNative ≤ pGeometry → (Fintype.card Pivot : ℝ) ≤ pGeometry →
    ∀ (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0),
      Q.GeometryComplexityLE pGeometry →
      (∀ i j, rationalLogHeight
        (Q.basis.repr (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (D.basis j)) i) ≤ pGeometry) →
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + p + 2
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
    ∀ (keepLong : LayerSamplerVariables G I n B → Prop)
      (_hLongSub : ∀ i, keepLong i → keep i) [Nonempty {i // keepLong i}],
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
    ∀ (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g)),
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct Q (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
          jointGeo adaptedBudget,
        F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen observable weight
          scoreThreshold hscore geometry.source.basis geometry.source.weight geometry.source.layers
          js Q hQ hker descended hrecovery geometry.target qVertical qCommon pProj := by
  obtain ⟨Cgeometry, hCgeometry, hgeometry⟩ := exists_native_adapted_map_geometry
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hfactor⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_actual_adapted_long_quotient_factors s hs
  refine ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    pGeometry hpGeometry hD hpNative hPivot js dQ Q hQ hker hQGeometry hmap
    pGeo jointGeo adaptedBudget bnd localCost jointCost P keepLong hLongSub _ hlong hcommonLong qCommon pProj
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore descended hrecovery
  have hpGeometry0 : 0 ≤ pGeometry := (by norm_num : (0 : ℝ) ≤ 2).trans hpGeometry
  have hnative (j : Pivot) : (F.native j).model.GeometryComplexityLE pGeometry :=
    (F.native j).complexity.1.mono (F.native j).model hpNative
  have hpGeo : 0 ≤ pGeo := by dsimp [pGeo]; positivity
  have hjointGeo : 0 ≤ jointGeo := by dsimp [jointGeo]; positivity
  have hGeometryJoint : pGeometry ≤ jointGeo := by dsimp [jointGeo]; nlinarith
  have hsourceGeo := optionProduct_geometry D (fun j => (F.native j).model)
    hpGeometry0 hPivot hD hnative
  have htargetGeo := optionProduct_geometry Q (fun j => (F.native j).model)
    hpGeometry0 hPivot hQGeometry hnative
  have hmapJoint := optionMarkedLieMap_native_logHeight D Q
    (fun j => (F.native j).model)
    (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) hpGeometry0 hmap
  obtain ⟨geometry⟩ := hgeometry
    (optionProduct D (fun j => (F.native j).model))
    (optionProduct Q (fun j => (F.native j).model))
    (optionMarkedLieMap (L := fun j => (F.native j).L)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
    hjointGeo hsourceGeo htargetGeo (fun i j => (hmapJoint j i).trans hGeometryJoint)
  refine ⟨geometry, ?_⟩
  have hpair (j : Pivot) : (pi (pairModels D (F.native j).model)).GeometryComplexityLE pGeo := by
    apply pi_geometry _ hpGeometry0
    · simpa only [Fintype.card_bool, Nat.cast_ofNat] using hpGeometry
    · intro k
      cases k
      · exact hnative j
      · exact hD
  have hadapted : 0 ≤ adaptedBudget := geometry.budget_nonneg
  have hpow : 0 ≤ (pGeo + 3) ^ 5 := by positivity
  have hbnd : 0 ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have habnd : adaptedBudget ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have hpbnd : p ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0]
  have hgbnd : jointGeo + 1 ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have hLongCard : (Fintype.card {i // keepLong i} : ℝ) ≤ p := by
    have hcard : Fintype.card {i // keepLong i} ≤ Fintype.card {i // keep i} :=
      Fintype.card_le_of_injective
        (fun i : {i // keepLong i} => (⟨i.val, hLongSub i.val i.property⟩ : {i // keep i}))
        (fun _ _ h => Subtype.ext (congrArg (fun i : {i // keep i} => i.val) h))
    exact (Nat.cast_le.mpr hcard).trans F.hK
  have hsourceDim : (Fintype.card (Fin (finrank ℚ
      (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))) : ℝ) ≤ bnd := by
    simpa only [Fintype.card_fin] using geometry.source_dimension.trans (by linarith only [hgbnd] : jointGeo ≤ bnd)
  have hProj : 0 ≤ pProj :=
    add_nonneg (add_nonneg (le_max_right qCommon 0) hadapted) zero_le_one
  have hqProj : qCommon ≤ pProj :=
    (le_max_left qCommon 0).trans
      ((le_add_of_nonneg_right hadapted).trans (le_add_of_nonneg_right zero_le_one))
  have haProj : adaptedBudget ≤ pProj :=
    (le_add_of_nonneg_left (le_max_right qCommon 0)).trans
      (le_add_of_nonneg_right zero_le_one)
  have hJointProj : jointGeo ≤ pProj :=
    (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans
      (geometry.forward_budget.trans haProj)
  exact hfactor F hpq hprecision hfrequency hbudget H hH hcorr
    (α := Fin (finrank ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i)))
    (pGeo := pGeo) (bnd := bnd) hpGeo hbnd hpair
    (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp])
    (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]) hsourceDim
    (hPivot.trans (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]))
    geometry.source.basis geometry.source.weight geometry.source.layers
    (fun i j k => (geometry.source_structure i j k).trans habnd)
    (fun i k => (geometry.source_forward i k).trans hgbnd)
    keepLong hLongSub (hLongCard.trans hpbnd) hlong hcommonLong
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore
    js Q hQ hker descended hrecovery geometry.target
    (height := geometry.entries_height) (pProj := pProj) geometry.entries hProj hqProj
    (by simpa only [Fintype.card_fin] using geometry.source_dimension.trans hJointProj)
    (geometry.target_dimension.trans hJointProj)
    (geometry.entries_bound.trans (Real.exp_le_exp.mpr haProj))

end

end Erdos3.VectorPolynomial

end

end OAI
