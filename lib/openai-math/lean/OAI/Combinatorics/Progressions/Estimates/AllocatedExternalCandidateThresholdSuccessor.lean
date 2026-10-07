import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrimitivePhysicalBudget
import OAI.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_floor_le_exp {densityCost budgetLog : ℝ}
    (hbudgetLog : 0 ≤ budgetLog) :
    Real.exp densityCost *
        max 2 (2 * Real.exp budgetLog * max 1 (Real.exp budgetLog)) ≤
      Real.exp (densityCost + 2 * budgetLog + 2) := by
  have he : 1 ≤ Real.exp budgetLog := Real.one_le_exp_iff.mpr hbudgetLog
  have he2 : 2 ≤ Real.exp (2 : ℝ) := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpair : 2 ≤ 2 * Real.exp budgetLog * Real.exp budgetLog := by
    nlinarith [sq_nonneg (Real.exp budgetLog - 1)]
  rw [max_eq_right he, max_eq_right hpair]
  calc
    _ = 2 * Real.exp (densityCost + 2 * budgetLog) := by
      rw [show densityCost + 2 * budgetLog = densityCost + budgetLog + budgetLog by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ Real.exp (2 : ℝ) * Real.exp (densityCost + 2 * budgetLog) :=
      mul_le_mul_of_nonneg_right he2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem finiteFreezing_floor_le_recursive {p densityCost budgetLog : ℝ}
    (hp : 0 ≤ p) {C : ℕ}
    (hdensity : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C) :
    Real.exp densityCost *
        max 2 (2 * Real.exp budgetLog * max 1 (Real.exp budgetLog)) ≤
      Real.exp (finiteFreezingRecursiveParameter C p) := by
  apply (finiteFreezing_floor_le_exp hbudgetLog0).trans
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ (p + C) ^ C := by positivity
  unfold finiteFreezingRecursiveParameter
  linarith

theorem finiteFreezing_floor_of_recursive_side {p densityCost budgetLog side : ℝ}
    (hp : 0 ≤ p) {C : ℕ}
    (hdensity : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hside : Real.exp (finiteFreezingRecursiveParameter C p) ≤ side) :
    Real.exp densityCost *
      max 2 (2 * Real.exp budgetLog * max 1 (Real.exp budgetLog)) ≤ side :=
  (finiteFreezing_floor_le_recursive hp hdensity hbudgetLog0 hbudgetLog).trans hside

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration RationalFilteredNilmanifold

noncomputable def candidatePrimitiveFreezingCutoff (s a : ℕ) (p : ℝ) : ℝ :=
  p + 2 * (p + nativeMarkedFreezingExponent (s + 1) a) ^
    nativeMarkedFreezingExponent (s + 1) a + 2

theorem candidatePrimitiveFreezingCutoff_ge_input (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ candidatePrimitiveFreezingCutoff s a p := by
  unfold candidatePrimitiveFreezingCutoff
  have : 0 ≤ (p + nativeMarkedFreezingExponent (s + 1) a) ^
      nativeMarkedFreezingExponent (s + 1) a := by positivity
  linarith

theorem candidatePrimitiveFreezingCutoff_le_geometry (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p ≤
      candidatePrimitivePhysicalGeometryParameter s a p := by
  let Cfree := nativeMarkedFreezingExponent (s + 1) a
  let outerExponent := candidateFreezingOuterExponent s a
  let B := frozenMarkedPhysicalExponent (s + 1)
  let R := allocatedRightDictionaryExponent (s + 1)
  let outer := candidateCoveredOuterParameter outerExponent p
  let right := candidateCoveredRightParameter outerExponent B p
  let dict := candidateCoveredDictionaryParameter outerExponent B R p
  have houter : nativeMarkedFreezingPhysicalParameter p Cfree ≤ outer :=
    candidatePrimitivePhysicalOuterParameter_bound s a hp
  have houter0 : 0 ≤ outer := by dsimp [outer, candidateCoveredOuterParameter]; positivity
  have hdict0 : 0 ≤ dict := by
    dsimp [dict, candidateCoveredDictionaryParameter, candidateCoveredRightParameter,
      candidateCoveredOuterParameter]
    positivity
  have hB : 2 ≤ B := frozenMarkedPhysicalExponent_ge_two (s + 1)
  have hright : outer ≤ right := by
    apply (le_power_budget houter0 (by omega : 1 ≤ B)).trans
    dsimp [right, candidateCoveredRightParameter]
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add le_rfl (by exact_mod_cast hB : (2 : ℝ) ≤ B)) B
  have hlarge : 1 ≤ (p + 3) ^ 36 := one_le_pow₀ (by linarith)
  have hblog : (p + Cfree) ^ Cfree + 1 ≤ outer := by
    dsimp [nativeMarkedFreezingPhysicalParameter] at houter
    linarith
  change p + 2 * (p + Cfree) ^ Cfree + 2 ≤ p + outer + right + dict + 1
  linarith

theorem candidatePrimitiveFreezingCutoff_le_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p ≤
      (p + candidatePrimitivePhysicalBudgetExponent s a) ^
        candidatePrimitivePhysicalBudgetExponent s a :=
  (candidatePrimitiveFreezingCutoff_le_geometry s a hp).trans
    (candidatePrimitivePhysicalScalarBounds s a hp).geometry_budget

theorem candidatePrimitiveFreezingCutoff_floor (s a : ℕ) {p densityCost side : ℝ}
    (hp : 0 ≤ p) (hdensity : densityCost ≤ p)
    (hside : Real.exp (candidatePrimitiveFreezingCutoff s a p) ≤ side) :
    Real.exp densityCost * max 2
      (2 * Real.exp ((p + nativeMarkedFreezingExponent (s + 1) a) ^
          nativeMarkedFreezingExponent (s + 1) a) *
        max 1 (Real.exp ((p + nativeMarkedFreezingExponent (s + 1) a) ^
          nativeMarkedFreezingExponent (s + 1) a))) ≤ side := by
  apply (finiteFreezing_floor_le_exp (by positivity)).trans
  apply le_trans (Real.exp_le_exp.mpr ?_) hside
  unfold candidatePrimitiveFreezingCutoff
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {e : ℕ}
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem conclusion_of_primitive_nativeReset_degreeRule
    {densityCost p massLog : ℝ}
    (a : ℕ) (hp0 : 0 ≤ p)
    (hDNative : D.GeometryComplexityLE p)
    (hRetainedCount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ p)
    (hMarkedDimension : (nMarkedBasis : ℝ) ≤ p)
    (hSectionMapHeight : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hdenominatorPos : 0 < denominator)
    (hdenominatorBound : (denominator : ℝ) ≤ Real.exp p)
    (hSlowBound : slow ≤ Real.exp ((p + 2) ^ a))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hside : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp (finiteFreezingRecursiveParameter
        (candidatePrimitivePhysicalBudgetExponent s a) p) ≤ (A.sides i.val : ℝ))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ p) (hdensityInput : densityCost ≤ p)
    (hmassLog : massLog ≤ p) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0)
    (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hmarkedPhysicalLeft : ∀ x ∈ integerBox N, ∀ i,
      |(c.baseChange ℝ).repr
        (Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x) reset.leftMark).coord i| ≤ Real.exp p)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE p)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ p)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ p)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s a) p) outputCost) :
    Nonempty (P₀.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let C := candidatePrimitivePhysicalBudgetExponent s a
  let pGeo := candidatePrimitivePhysicalGeometryParameter s a p
  let Cfree := RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a
  have hC : 2 ≤ C := candidatePrimitivePhysicalBudgetExponent_ge_two s a
  have bounds := candidatePrimitivePhysicalScalarBounds s a hp0
  have hpBudget : p ≤ (p + C) ^ C := candidatePrimitivePhysical_input_budget s a hp0
  have hfreezeBudget : (p + Cfree) ^ Cfree ≤ (p + C) ^ C :=
    candidatePrimitivePhysical_freezing_budget s a hp0
  have hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * Real.exp ((p + Cfree) ^ Cfree) *
        max 1 (Real.exp ((p + Cfree) ^ Cfree))) ≤ (A.sides i.val : ℝ) := by
    intro i
    exact finiteFreezing_floor_of_recursive_side hp0 (hdensityInput.trans hpBudget)
      (by positivity) hfreezeBudget (hside i)
  have hpOuter := (RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter_bounds
    hp0 Cfree).1
  have hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (oc i).val y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨count, hcount, centers, hcenters⟩ := hOriginalNet η hη hη1
    refine ⟨count, hcount.trans (Real.exp_le_exp.mpr ?_), centers, hcenters⟩
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hη1)
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add (add_le_add (show p ≤ pGeo from bounds.input_geometry)
        (le_refl (Real.log (1 / η)))) (le_refl (e : ℝ))) e
  exact P₀.conclusion_of_generatedFreezing_nativeReset_degreeRule Fmark φ hφ keep hkeep W
    c ν hF factors reset hσ1 H hH hchart hsmall hp a C hp0 hC
    hDNative hRetainedCount hMarkedDimension hSectionMapHeight
    hdenominatorPos hdenominatorBound hSlowBound hslowMark hgrid hdensity hfloor
    hweight hscoreInput (hcostInput.trans hpBudget) (hdensityInput.trans hpBudget)
    hfreezeBudget (hmassLog.trans hpBudget) hmassInput dw hdb hW hsurj hξ1 ℓ
    bounds.geometry_one bounds.input_geometry bounds.geometry_recursive bounds.covered_recursive hℓ
    (fun x hx i => (hmarkedPhysicalLeft x hx i).trans (Real.exp_le_exp.mpr hpOuter))
    bounds.physical_geometry bounds.right_geometry hOriginalLip hpositive
    (hFGeo.mono Fmark bounds.input_geometry) generators hspan
    (hgeneratorCount.trans bounds.input_geometry)
    (fun i j => (hmarkedBasis i j).trans bounds.input_geometry)
    (fun i j => (hmarkHeight i j).trans bounds.input_geometry)
    (fun i j => (hgeneratorHeight i j).trans bounds.input_geometry)
    htopKernel hnet outputCost lowerIH

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration RationalFilteredNilmanifold

theorem candidatePrimitiveFreezingCutoff_add_two_le_geometry (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p + 2 ≤
      candidatePrimitivePhysicalGeometryParameter s a p := by
  let Cfree := nativeMarkedFreezingExponent (s + 1) a
  let outerExponent := candidateFreezingOuterExponent s a
  let B := frozenMarkedPhysicalExponent (s + 1)
  let R := allocatedRightDictionaryExponent (s + 1)
  let outer := candidateCoveredOuterParameter outerExponent p
  let right := candidateCoveredRightParameter outerExponent B p
  let dict := candidateCoveredDictionaryParameter outerExponent B R p
  have houter : nativeMarkedFreezingPhysicalParameter p Cfree ≤ outer :=
    candidatePrimitivePhysicalOuterParameter_bound s a hp
  have houter0 : 0 ≤ outer := by dsimp [outer, candidateCoveredOuterParameter]; positivity
  have hdict0 : 0 ≤ dict := by
    dsimp [dict, candidateCoveredDictionaryParameter, candidateCoveredRightParameter,
      candidateCoveredOuterParameter]
    positivity
  have hB : 2 ≤ B := frozenMarkedPhysicalExponent_ge_two (s + 1)
  have hright : outer ≤ right := by
    apply (le_power_budget houter0 (by omega : 1 ≤ B)).trans
    dsimp [right, candidateCoveredRightParameter]
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add le_rfl (by exact_mod_cast hB : (2 : ℝ) ≤ B)) B
  have hlarge : 3 ≤ (p + 3) ^ 36 := by
    have hpow : p + 3 ≤ (p + 3) ^ 36 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 3)
        (by norm_num : (1 : ℕ) ≤ 36)
    linarith
  have hblog : (p + Cfree) ^ Cfree + 3 ≤ outer := by
    dsimp [nativeMarkedFreezingPhysicalParameter] at houter
    linarith
  change p + 2 * (p + Cfree) ^ Cfree + 2 + 2 ≤ p + outer + right + dict + 1
  linarith

theorem candidatePrimitiveFreezingCutoff_add_two_le_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p + 2 ≤
      (p + candidatePrimitivePhysicalBudgetExponent s a) ^
        candidatePrimitivePhysicalBudgetExponent s a :=
  (candidatePrimitiveFreezingCutoff_add_two_le_geometry s a hp).trans
    (candidatePrimitivePhysicalScalarBounds s a hp).geometry_budget

theorem candidatePrimitiveFreezingCutoff_integer_cost (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidateSideCutoffCost (Real.exp (candidatePrimitiveFreezingCutoff s a p)) ≤
      candidatePrimitiveFreezingCutoff s a p + 2 :=
  candidateSideCutoffCost_exp_bound
    (hp.trans (candidatePrimitiveFreezingCutoff_ge_input s a hp))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {e : ℕ}
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem conclusion_of_threshold_nativeReset_degreeRule
    {densityCost p massLog : ℝ}
    (a : ℕ) (hp0 : 0 ≤ p)
    (hDNative : D.GeometryComplexityLE p)
    (hRetainedCount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ p)
    (hMarkedDimension : (nMarkedBasis : ℝ) ≤ p)
    (hSectionMapHeight : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hdenominatorPos : 0 < denominator)
    (hdenominatorBound : (denominator : ℝ) ≤ Real.exp p)
    (hSlowBound : slow ≤ Real.exp ((p + 2) ^ a))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hside : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp (candidatePrimitiveFreezingCutoff s a p) ≤ (A.sides i.val : ℝ))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ candidatePrimitiveFreezingCutoff s a p) (hdensityInput : densityCost ≤ p)
    (hmassLog : massLog ≤ p) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0)
    (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hmarkedPhysicalLeft : ∀ x ∈ integerBox N, ∀ i,
      |(c.baseChange ℝ).repr
        (Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x) reset.leftMark).coord i| ≤ Real.exp p)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE p)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ p)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ p)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s a) p) outputCost) :
    Nonempty (P₀.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let C := candidatePrimitivePhysicalBudgetExponent s a
  let pGeo := candidatePrimitivePhysicalGeometryParameter s a p
  let Cfree := RationalFilteredNilmanifold.nativeMarkedFreezingExponent (s + 1) a
  have hC : 2 ≤ C := candidatePrimitivePhysicalBudgetExponent_ge_two s a
  have bounds := candidatePrimitivePhysicalScalarBounds s a hp0
  have hpBudget : p ≤ (p + C) ^ C := candidatePrimitivePhysical_input_budget s a hp0
  have hfreezeBudget : (p + Cfree) ^ Cfree ≤ (p + C) ^ C :=
    candidatePrimitivePhysical_freezing_budget s a hp0
  have hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * Real.exp ((p + Cfree) ^ Cfree) *
        max 1 (Real.exp ((p + Cfree) ^ Cfree))) ≤ (A.sides i.val : ℝ) := by
    intro i
    exact candidatePrimitiveFreezingCutoff_floor s a hp0 hdensityInput (hside i)
  have hpOuter := (RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter_bounds
    hp0 Cfree).1
  have hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (oc i).val y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨count, hcount, centers, hcenters⟩ := hOriginalNet η hη hη1
    refine ⟨count, hcount.trans (Real.exp_le_exp.mpr ?_), centers, hcenters⟩
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hη1)
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add (add_le_add (show p ≤ pGeo from bounds.input_geometry)
        (le_refl (Real.log (1 / η)))) (le_refl (e : ℝ))) e
  exact P₀.conclusion_of_generatedFreezing_nativeReset_degreeRule Fmark φ hφ keep hkeep W
    c ν hF factors reset hσ1 H hH hchart hsmall hp a C hp0 hC
    hDNative hRetainedCount hMarkedDimension hSectionMapHeight
    hdenominatorPos hdenominatorBound hSlowBound hslowMark hgrid hdensity hfloor
    hweight hscoreInput
    (hcostInput.trans (candidatePrimitiveFreezingCutoff_le_budget s a hp0))
    (hdensityInput.trans hpBudget)
    hfreezeBudget (hmassLog.trans hpBudget) hmassInput dw hdb hW hsurj hξ1 ℓ
    bounds.geometry_one bounds.input_geometry bounds.geometry_recursive bounds.covered_recursive hℓ
    (fun x hx i => (hmarkedPhysicalLeft x hx i).trans (Real.exp_le_exp.mpr hpOuter))
    bounds.physical_geometry bounds.right_geometry hOriginalLip hpositive
    (hFGeo.mono Fmark bounds.input_geometry) generators hspan
    (hgeneratorCount.trans bounds.input_geometry)
    (fun i j => (hmarkedBasis i j).trans bounds.input_geometry)
    (fun i j => (hmarkHeight i j).trans bounds.input_geometry)
    (fun i j => (hgeneratorHeight i j).trans bounds.input_geometry)
    htopKernel hnet outputCost lowerIH

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
