import OAI.Combinatorics.Progressions.Dynamics.PreparedComparisonPrecisionLogBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedRelativeEndpointComparisonBudget
import OAI.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget

namespace OAI

section

namespace Erdos3

theorem integerAxisSideLength_one_of_scale_one {h L : ℕ} (hL : 0 < L) (γ : ℝ) :
    integerAxisSideLength h 1 L γ = 1 := by
  have hpow : 1 ≤ L ^ h := Nat.one_le_pow _ _ hL
  have hden := inactiveDenominator_pos γ
  simp only [integerAxisSideLength, Nat.not_lt.mpr hpow, ↓reduceIte,
    inactiveSideLength]
  have hsmall : ¬2 * inactiveDenominator γ ≤ 1 := by omega
  simp only [hsmall, ↓reduceIte]

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

@[simp] theorem sides_free (g : G) : A.sides (.inl g) = S.value := rfl

@[simp] theorem sides_continuous (j : Fin m) (i : I j)
    (a : B ⟨j, .inl i⟩) (r : Fin (j.val + 1)) :
    A.sides (.inr ⟨⟨j, .inl i⟩, a, r⟩) = S.value := rfl

theorem sides_integer (j : Fin m) (i : Fin (n j))
    (a : B ⟨j, .inr i⟩) (r : Fin (j.val + 1)) :
    A.sides (.inr ⟨⟨j, .inr i⟩, a, r⟩) =
      integerAxisSideLength (j.val + 1) (basisAxisScale (b j) i) S.value
        (principalProfileSize (R j) (Fintype.card (B ⟨j, .inr i⟩))) := rfl

theorem sides_active (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (b j) i)
    (a : B ⟨j, .inr i⟩) (r : Fin (j.val + 1)) :
    A.sides (.inr ⟨⟨j, .inr i⟩, a, r⟩) = S.value := by
  rw [A.sides_integer]
  simp only [integerAxisSideLength, hactive, ↓reduceIte]

theorem sides_one_of_basisAxisScale_one (j : Fin m) (i : Fin (n j))
    (hscale : basisAxisScale (b j) i = 1)
    (a : B ⟨j, .inr i⟩) (r : Fin (j.val + 1)) :
    A.sides (.inr ⟨⟨j, .inr i⟩, a, r⟩) = 1 := by
  rw [A.sides_integer, hscale]
  exact integerAxisSideLength_one_of_scale_one S.positive _

theorem sides_long_or_bounded_integer_axis {T : ℕ} (hT : 0 < T)
    (hTS : T ≤ S.value) (v : LayerSamplerVariables G I n B) :
    T ≤ A.sides v ∨ ∃ (j : Fin m) (i : Fin (n j))
      (a : B ⟨j, .inr i⟩) (r : Fin (j.val + 1)),
      v = .inr ⟨⟨j, .inr i⟩, a, r⟩ ∧
      basisAxisScale (b j) i ≤ integerAxisShortBound (j.val + 1) T
        (principalProfileSize (R j) (Fintype.card (B ⟨j, .inr i⟩))) := by
  rcases v with g | ⟨⟨j, i⟩, a, r⟩
  · exact Or.inl hTS
  · cases i with
    | inl i => exact Or.inl hTS
    | inr i =>
      rcases integerAxisSideLength_long_or_bounded
        (K := basisAxisScale (b j) i)
        (γ := principalProfileSize (R j) (Fintype.card (B ⟨j, .inr i⟩)))
        (Nat.zero_lt_succ _) hT hTS with hlong | hbounded
      · exact Or.inl hlong
      · exact Or.inr ⟨j, i, a, r, rfl, hbounded⟩

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedNestedScalarAnchorFloor
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ) (x : ℝ) : ℕ :=
  Nat.ceil (Real.exp (candidateNestedForwardSeed A constants innerDepth outerDepth x))

theorem preparedNestedScalarAnchorFloor_bounds
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ preparedNestedScalarAnchorFloor A constants innerDepth outerDepth x ∧
    (preparedNestedScalarAnchorFloor A constants innerDepth outerDepth x : ℝ) ≤
      Real.exp (candidateNestedForwardSeed A constants innerDepth outerDepth x + 1) :=
  ⟨one_le_ceil_exp _, ceil_exp_le_exp_add_one
    (candidateNestedForwardSeed_nonneg A constants innerDepth outerDepth hx)⟩

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
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

theorem free_axis_nested_floor (g : G)
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hS : preparedNestedScalarAnchorFloor A constants innerDepth outerDepth x ≤ S.value)
    (outer : ℕ) (ho : outer ≤ outerDepth) :
    Real.exp (candidateNestedForwardSeed A constants innerDepth outer x) ≤
      (sampler.sides (.inl g) : ℝ) := by
  rw [sampler.sides_free]
  apply (Real.exp_le_exp.mpr
    (candidateNestedForwardSeed_monotone A constants innerDepth hA hx ho)).trans
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hS)

theorem exists_free_axis_nested_floor [Nonempty G]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    {x : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hS : preparedNestedScalarAnchorFloor A constants innerDepth outerDepth x ≤ S.value) :
    ∃ g : G, ∀ outer ≤ outerDepth,
      Real.exp (candidateNestedForwardSeed A constants innerDepth outer x) ≤
        (sampler.sides (.inl g) : ℝ) :=
  ⟨Classical.choice inferInstance, fun outer ho =>
    sampler.free_axis_nested_floor _ A constants innerDepth outerDepth hA hx hS outer ho⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointMinimumScale
    (seed periodLog childLog cost comparisonLog : ℝ) : ℕ :=
  max ⌈Real.exp seed⌉₊
    (preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog)

noncomputable def preparedRelativeEndpointMinimumLog
    (seed periodLog childLog cost comparisonLog : ℝ) : ℝ :=
  max (seed + 1)
    (preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog + 1)

noncomputable def preparedRelativeEndpointGoodCutoff (Ptest : ℝ) : ℕ :=
  ⌈Real.exp (2 * Ptest)⌉₊

def preparedRelativeEndpointGoodLog (Ptest : ℝ) : ℝ := 2 * Ptest + 1

def preparedRelativeEndpointAmbientLog (modelRequired nativeAmbient gridAmbient : ℝ) : ℝ :=
  max modelRequired (max nativeAmbient gridAmbient)

theorem preparedRelativeEndpointMinimumScale_nested
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    (x periodLog childLog cost comparisonLog : ℝ) :
    preparedRelativeEndpointMinimumScale
      (candidateNestedForwardSeed A constants innerDepth outerDepth x)
      periodLog childLog cost comparisonLog =
      max (preparedNestedScalarAnchorFloor A constants innerDepth outerDepth x)
        (preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog) := rfl

theorem preparedRelativeEndpointMinimumScale_bounds
    {seed : ℝ} (hseed : 0 ≤ seed) (periodLog childLog cost comparisonLog : ℝ) :
    let Lmin := preparedRelativeEndpointMinimumScale seed periodLog childLog cost comparisonLog
    let Pmin := preparedRelativeEndpointMinimumLog seed periodLog childLog cost comparisonLog
    0 ≤ Pmin ∧ 1 ≤ Lmin ∧ (Lmin : ℝ) ≤ Real.exp Pmin ∧
      ⌈Real.exp seed⌉₊ ≤ Lmin ∧
      preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ Lmin ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  intro Lmin Pmin
  obtain ⟨hF, hL, hLexp, hchild, hcost, hperiod, hcompare⟩ :=
    preparedSlicedForecastCommonFloor_bounds periodLog childLog cost comparisonLog
  have hseedFloor : ⌈Real.exp seed⌉₊ ≤ Lmin := le_max_left _ _
  have hcommon : preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ Lmin :=
    le_max_right _ _
  have hseedP : seed + 1 ≤ Pmin := le_max_left _ _
  have hcommonP :
      preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog + 1 ≤ Pmin :=
    le_max_right _ _
  refine ⟨by linarith only [hseed, hseedP],
    (one_le_ceil_exp seed).trans hseedFloor, ?_, hseedFloor, hcommon,
    hchild.trans hcommon, hcost.trans (Nat.cast_le.mpr hcommon),
    fun T hT => (hperiod T hT).trans hcommon,
    fun L hL => (hcompare L hL).trans hcommon⟩
  change ((max ⌈Real.exp seed⌉₊
    (preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max]
  exact max_le ((ceil_exp_le_exp_add_one hseed).trans (Real.exp_le_exp.mpr hseedP))
    (hLexp.trans (Real.exp_le_exp.mpr hcommonP))

theorem preparedRelativeEndpointGoodCutoff_bounds {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    0 ≤ preparedRelativeEndpointGoodLog Ptest ∧
    1 ≤ preparedRelativeEndpointGoodCutoff Ptest ∧
    Real.exp (2 * Ptest) ≤ (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ∧
    (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ≤
      Real.exp (preparedRelativeEndpointGoodLog Ptest) := by
  refine ⟨by unfold preparedRelativeEndpointGoodLog; positivity,
    one_le_ceil_exp _, Nat.le_ceil _, ?_⟩
  exact ceil_exp_le_exp_add_one (by positivity)

theorem preparedRelativeEndpointAmbientLog_bounds
    {modelRequired nativeAmbient gridAmbient : ℝ} (hmodel : 0 ≤ modelRequired) :
    0 ≤ preparedRelativeEndpointAmbientLog modelRequired nativeAmbient gridAmbient ∧
    modelRequired ≤ preparedRelativeEndpointAmbientLog modelRequired nativeAmbient gridAmbient ∧
    nativeAmbient ≤ preparedRelativeEndpointAmbientLog modelRequired nativeAmbient gridAmbient ∧
    gridAmbient ≤ preparedRelativeEndpointAmbientLog modelRequired nativeAmbient gridAmbient :=
  ⟨hmodel.trans (le_max_left _ _), le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem preparedRelativeEndpointScalarKnobs_power_bounds (C : ℕ)
    {B seed periodLog childLog cost comparisonLog Ptest sigmaLog coarseLog
      modelRequired nativeAmbient gridAmbient : ℝ}
    (hB : 0 ≤ B)
    (hseed : seed ∈ Set.Icc 0 ((B + 2) ^ C))
    (hperiod : periodLog ∈ Set.Icc 0 ((B + 2) ^ C))
    (hchild : childLog ∈ Set.Icc 0 ((B + 2) ^ C))
    (hcost : cost ∈ Set.Icc 0 ((B + 2) ^ C))
    (hcompare : comparisonLog ∈ Set.Icc 0 ((B + 2) ^ C))
    (htest : Ptest ∈ Set.Icc 0 ((B + 2) ^ C))
    (hsigma : sigmaLog ∈ Set.Icc 0 ((B + 2) ^ C))
    (hcoarse : coarseLog ∈ Set.Icc 0 ((B + 2) ^ C))
    (hmodel : modelRequired ∈ Set.Icc 0 ((B + 2) ^ C))
    (hnative : nativeAmbient ∈ Set.Icc 0 ((B + 2) ^ C))
    (hgrid : gridAmbient ∈ Set.Icc 0 ((B + 2) ^ C)) :
    let inputPower := C + 2
    preparedRelativeEndpointMinimumLog seed periodLog childLog cost comparisonLog ∈
      Set.Icc 0 ((B + 2) ^ inputPower) ∧
    preparedRelativeEndpointGoodLog Ptest ∈ Set.Icc 0 ((B + 2) ^ inputPower) ∧
    sigmaLog ∈ Set.Icc 0 ((B + 2) ^ inputPower) ∧
    coarseLog ∈ Set.Icc 0 ((B + 2) ^ inputPower) ∧
    preparedRelativeEndpointAmbientLog modelRequired nativeAmbient gridAmbient ∈
      Set.Icc 0 ((B + 2) ^ inputPower) := by
  intro inputPower
  let q : ℝ := (B + 2) ^ C
  have hq : 1 ≤ q := one_le_pow₀ (by linarith only [hB])
  have hpower : 4 * q ≤ (B + 2) ^ inputPower := by
    dsimp only [inputPower]
    rw [pow_add]
    have hbase : 4 ≤ (B + 2) ^ 2 := by nlinarith only [sq_nonneg B, hB]
    nlinarith only [mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hq)]
  have hqpower : q ≤ (B + 2) ^ inputPower := by linarith only [hq, hpower]
  have hF : preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog ≤ q + 1 := by
    unfold preparedSlicedForecastCommonFloorExponent
    exact max_le (by linarith only [hq])
      (max_le (by linarith only [hperiod.2])
        (max_le (by linarith only [hchild.2])
          (max_le (by linarith only [hcost.2]) (by linarith only [hcompare.2]))))
  have hPmin : preparedRelativeEndpointMinimumLog seed periodLog childLog cost comparisonLog ≤ q + 2 := by
    unfold preparedRelativeEndpointMinimumLog
    exact max_le (by linarith only [hseed.2]) (by linarith only [hF])
  have hV : preparedRelativeEndpointGoodLog Ptest ≤ 2 * q + 1 := by
    unfold preparedRelativeEndpointGoodLog
    linarith only [htest.2]
  have hendpoint : preparedRelativeEndpointAmbientLog modelRequired nativeAmbient gridAmbient ≤ q :=
    max_le hmodel.2 (max_le hnative.2 hgrid.2)
  exact ⟨⟨(preparedRelativeEndpointMinimumScale_bounds hseed.1 periodLog childLog cost comparisonLog).1,
      by linarith only [hPmin, hq, hpower]⟩,
    ⟨(preparedRelativeEndpointGoodCutoff_bounds htest.1).1,
      by linarith only [hV, hq, hpower]⟩,
    ⟨hsigma.1, hsigma.2.trans hqpower⟩, ⟨hcoarse.1, hcoarse.2.trans hqpower⟩,
    ⟨(preparedRelativeEndpointAmbientLog_bounds hmodel.1).1, hendpoint.trans hqpower⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedRelativeEndpointSigmaLog_eq (m M Jalloc : ℕ)
    (Ptest Ecompare cost : ℝ) :
    preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m =
    fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) +
        preparedSlicedForecastSourceLog m M Jalloc Ptest + 4) (cost + 1)
      (2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14) m := by
  unfold preparedRelativeEndpointSigmaLog preparedRelativeEndpointCoarseLog
  change fixedPathSlicedPerturbationLog _ _ _
    (2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + Ecompare + 18) _ = _
  congr 1
  ring

theorem preparedComparisonContinuousDimension_le_two
    {X J : Type} {m M nX : ℕ} (prep : RankPreparationFamily X J m)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    {T : ℝ} (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ T) :
    (((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j) : ℕ) : ℝ) ≤ 2 * T := by
  have hI : Fintype.card (Σ j, PreparedSamplerContinuous prep j) ≤ m * M := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => by
        simpa only [PreparedSamplerContinuous, Fintype.card_fin] using
          ((prep j).rank_le_coord_card.trans (hCoord j)))
      _ = _ := by simp
  have hIdim : Fintype.card (Σ j, PreparedSamplerContinuous prep j) ≤ nX + m * M := by omega
  have hIT : (Fintype.card (Σ j, PreparedSamplerContinuous prep j) : ℝ) ≤ T :=
    (Nat.cast_le.mpr hIdim).trans hDmod
  rw [Nat.cast_add]
  linarith only [hDmod, hIT]

theorem preparedRelativeEndpoint_source_bounds
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (M nX Jalloc : ℕ) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (σ : Fin m → ℝ) (ξ : ℝ) (S : ℕ) (N : Fin nX → ℕ)
    {T K seed childLog Pdim cost pRadius gainLog Qstride Ptest Ecompare : ℝ}
    (hK : 0 ≤ K) (hT : 1 ≤ T) (hm : (m : ℝ) ≤ T)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ T)
    (hD : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ T)
    (hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ T)
    (hpcap : preparedSlicedForecastPrimitiveCap ≤ T)
    (hPbad : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ T)
    (hcost : 0 ≤ cost) (hcostOne : cost + 1 ≤ T)
    (hTest : Ptest ∈ Set.Icc 0 T) (hCompare : Ecompare ∈ Set.Icc 0 T)
    (hRadius : pRadius ≤ T) (hTau : gainLog + (nX : ℝ) + 8 ≤ T)
    (hSigmaLog : preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m ≤ K)
    (hCoarseLog : preparedRelativeEndpointCoarseLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare ≤ K)
    (hFloorLog : (T + 10) ^ (2 * m + 20) ≤ K)
    (hσzero : ∀ j, 0 ≤ σ j) (hσK : ∀ j, σ j ≤ Real.exp (-K))
    (hξK : ξ ≤ Real.exp (-K))
    (hS : preparedRelativeEndpointMinimumScale seed 0 childLog cost
      ((T + 10) ^ (2 * m + 20)) ≤ S)
    (hN : ∀ i, Real.exp K ≤ (N i : ℝ)) :
    (∀ j, σ j ≤ 1) ∧ ξ ≤ 1 ∧
    (∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) +
        preparedSlicedForecastSourceLog m M Jalloc Ptest + 4) (cost + 1)
      (2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14) m)) ∧
    ξ ≤ Real.exp (-(2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + (Ecompare + 4) + 14)) ∧
    preparedSlicedForecastCommonFloor 0 childLog cost
      (preparedSlicedForecastComparisonFloorLog m M nX Jalloc
        ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
        Pdim cost pRadius gainLog Qstride Ptest (2 * Ptest) Ecompare) ≤ S ∧
    (∀ i, Real.exp (forecastJointGridAmbientLog
      ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
      (preparedSlicedForecastGridLog m M nX Jalloc Pdim cost gainLog Qstride Ptest)
      (Ecompare + 4) (2 * Ptest) (gainLog + (nX : ℝ) + 8)) ≤ (N i : ℝ)) := by
  have hOne : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK)
  have hd := preparedComparisonContinuousDimension_le_two prep hCoord hDmod
  have hfloor := preparedSlicedForecastComparisonFloorLog_le_power m M nX Jalloc
    ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
    hT hm hDmod hd hD hP hpcap hPbad hcost hcostOne hTest.1 hTest.2
    hCompare.1 hCompare.2 hRadius
  have hgrid := preparedSlicedForecastJointGridAmbientLog_le_power m M nX Jalloc
    ((nX + m * M) + Fintype.card (Σ j, PreparedSamplerContinuous prep j))
    hT hm hDmod hd hD hP hpcap hPbad hcost hcostOne hTest.1 hTest.2
    hCompare.1 hCompare.2 hTau
  refine ⟨fun j => (hσK j).trans hOne, hξK.trans hOne, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [abs_of_nonneg (hσzero j)]
    apply (hσK j).trans
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rwa [← preparedRelativeEndpointSigmaLog_eq]
  · apply hξK.trans
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    change 2 * preparedSlicedForecastSourceLog m M Jalloc Ptest + Ecompare + 18 ≤ K at hCoarseLog
    linarith only [hCoarseLog]
  · exact (preparedSlicedForecastCommonFloor_mono_comparison 0 childLog cost hfloor).trans
      ((le_max_right _ _).trans hS)
  · intro i
    exact (Real.exp_le_exp.mpr (hgrid.trans hFloorLog)).trans (hN i)

end Erdos3.VectorPolynomial

end

end OAI
