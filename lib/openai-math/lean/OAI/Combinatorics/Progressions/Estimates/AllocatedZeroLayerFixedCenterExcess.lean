import OAI.Combinatorics.Progressions.Geometry.PreparedFullChartNativeDetection
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredForecastEarlyWidth

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

include A in
omit [∀ layer, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J layer)) (euclideanSubspace (U layer)))] in
theorem integerBox_nonempty : (integerBox N).Nonempty := by
  refine ⟨0, (mem_integerBox N _).mpr ?_⟩
  intro x
  change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < (N x : ℤ)
  exact ⟨le_rfl, by exact_mod_cast A.size_pos x⟩

def NativeDetection (degree : ℕ) (pSlice pTest pNative α : ℝ) : Prop :=
  ∀ {Tests : A.Path → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset A.Site)
    (origin : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < step z j) →
    (∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j)) →
    (∀ z j, IsDenseCommonStrideBox A.sides pSlice ((slices z j).image Subtype.val)) →
    (∀ z j, (Vdetect z j).ComplexityLE pTest) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    SampledSliceNativeDetection J N A.integerBox_nonempty poly A.law A.physical slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))
      degree pNative α

theorem NativeDetection.mono_tests
    {degree : ℕ} {pSlice pTest pNative α pSlice' pTest' α' : ℝ}
    (h : A.NativeDetection degree pSlice pTest pNative α)
    (hs : pSlice' ≤ pSlice) (ht : pTest' ≤ pTest) (ha : α ≤ α') :
    A.NativeDetection degree pSlice' pTest' pNative α' := by
  intro Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm signal hsignal hsupp hlarge
  exact h Ddetect Vdetect slices origin step length hstep hshape
    (fun z j => (hdense z j).mono hs)
    (fun z j => (hcomplex z j).mono ht) hnorm signal hsignal hsupp (ha.trans hlarge)

def PolynomialGeometry (rankThreshold : ℝ) : Prop :=
  (∀ j, DegreeLE (fun _ : X => 1) (j.val + 1) (poly j)) ∧
  ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) rankThreshold (U j) (poly j)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local instance : Nonempty A.Site := A.site_nonempty

theorem exists_fixedCenter_forecast_model
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Tests : A.Path → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) 0 (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset A.Site)
    (origin : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hshape : ∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j))
    (hDense : ∀ z j, IsDenseCommonStrideBox A.sides pSlice ((slices z j).image Subtype.val))
    (hcomplex : ∀ z j, (Vdetect z j).ComplexityLE pTest)
    (hcap : ∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let tests : ∀ z, Tests z → A.Site → ℂ := fun z j t =>
      star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val))
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin) slices tests model.residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro tests commonBudget Qmodel native
  let : ∀ x, NeZero (N x) := fun x => ⟨(A.size_pos x).ne'⟩
  have hsize := preparedCenteredForecast_slice_family_bounds B U b S slices hDense
  have htests (z) (j) (t : A.Site) : ‖tests z j t‖ ≤ 1 :=
    preparedCenteredForecast_niltest_star_eval_bound (Vdetect z j) (hcap z j)
      (commonStrideIndex (origin z j) (step z j) t.val)
  have hdetect := hdirect Ddetect Vdetect slices origin step length
    hstep hshape hDense hcomplex hcap
  obtain ⟨nterms, hn, models, coefficient, residual, hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩ :=
    exists_fixedLaw_centered_forecast_twist_model 0 N poly localBudget Pnative hbudget hNative
      A.law (A.physicalBox hξone hmargin) A.physical (fun _ _ => rfl)
      slices tests (fun f => (data f).target) hu hp (le_max_left 0 massLog)
      (Real.exp_nonneg _) hC (Real.exp_nonneg _) (Real.exp_le_exp.mpr hSliceLog)
      hCp (Real.exp_le_exp.mpr hCap) hPrecision hsize.2 htests (fun f => (data f).cap)
      hdetect (fun f => (data f).Term) (fun f => (data f).coefficient)
      (fun f => (data f).centerConstant) (fun f => (data f).twists)
      (fun f => (data f).mass.trans (Real.exp_le_exp.mpr (le_max_right 0 massLog)))
      (fun f v => ((data f).approximation v).trans (Real.exp_le_exp.mpr (neg_le_neg hAccuracy)))
      hexcess le_rfl input hinput
  exact ⟨⟨nterms, hn, models, coefficient, residual⟩,
    hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem positiveProjectionAccuracy_le_of_le {p q : ℝ} (hpq : p ≤ q) :
    positiveProjectionAccuracy q ≤ positiveProjectionAccuracy p := by
  unfold positiveProjectionAccuracy
  apply Real.exp_le_exp.mpr
  linarith only [hpq]

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local instance fixedCenterEndpointSiteNonempty : Nonempty A.Site := A.site_nonempty

theorem NativeDetection.forecast_of_exp_threshold
    {degree : ℕ} {u p pSlice pTest pNative C capLog : ℝ}
    (hdirect : A.NativeDetection degree pSlice pTest pNative
      (Real.exp (-(2 * u + 4 * p + 8))))
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p) :
    A.NativeDetection degree pSlice pTest pNative
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C
        (Real.exp capLog)) := by
  have hthreshold := (forecastAugmentedUnitThreshold_bounds hu hp (Real.exp_nonneg _)
    (zero_le_one.trans hC) (Real.exp_le_exp.mpr hSliceLog) hCp
    (Real.exp_le_exp.mpr hCap)).2.2
  intro Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm signal hsignal hsupp hlarge
  exact hdirect Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm signal hsignal hsupp (hthreshold.trans hlarge)

theorem fixedCenter_excess_max_one_of_precision
    (hξsource hξtarget : ξ ≤ 1)
    (hmarginSource hmarginTarget : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hbox : (integerBox N).Nonempty) {rawCap E precision : ℝ}
    (hPrecision : precision ≤ E)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (A.law.siteLaw (A.physicalBox hξsource hmarginSource)) rawCap ≤
        6 * positiveProjectionAccuracy E) :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) (max 1 rawCap) ≤
        6 * positiveProjectionAccuracy precision := by
  exact ((FiniteProbabilityWeights.excessMass_max_one_le
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty)
    (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) rawCap).trans hexcess).trans
      (mul_le_mul_of_nonneg_left (positiveProjectionAccuracy_le_of_le hPrecision) (by norm_num))

theorem fixedCenter_forecast_source_bounds
    (hξsource hξtarget : ξ ≤ 1)
    (hmarginSource hmarginTarget : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hbox : (integerBox N).Nonempty)
    {degree : ℕ} {u p pSlice pTest pNative rawCap capLog E precision : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hRawCap : rawCap ≤ Real.exp p) (hCap : capLog ≤ p)
    (hPrecision : precision ≤ E)
    (hdirect : A.NativeDetection degree pSlice pTest pNative
      (Real.exp (-(2 * u + 4 * p + 8))))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (A.law.siteLaw (A.physicalBox hξsource hmarginSource)) rawCap ≤
        6 * positiveProjectionAccuracy E) :
    1 ≤ max 1 rawCap ∧ max 1 rawCap ≤ Real.exp p ∧
      A.NativeDetection degree pSlice pTest pNative
        (forecastAugmentedUnitThreshold u p
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 rawCap) (Real.exp capLog)) ∧
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) (max 1 rawCap) ≤
          6 * positiveProjectionAccuracy precision := by
  have hcap := marginalCap_max_one_exp_bound hp hRawCap
  exact ⟨hcap.1, hcap.2,
    NativeDetection.forecast_of_exp_threshold A hdirect hu hp hSliceLog hcap.1 hcap.2 hCap,
    A.fixedCenter_excess_max_one_of_precision hξsource hξtarget hmarginSource hmarginTarget
      hbox hPrecision hexcess⟩

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem fixedCenter_excess_zero_layers
    (hξ : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hloss : (∑ x, 2 * (spatialTrimMargin τ N x : ℝ) / N x) ≤ 1 / 2) :
    letI : Nonempty A.Site := A.site_nonempty
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ hmargin)) 2 = 0 := by
  let : Nonempty A.Site := A.site_nonempty
  let : Nonempty A.bases := A.bases_nonempty.to_subtype
  let : Nonempty (integerBox N) := A.integerBox_nonempty.to_subtype
  apply le_antisymm ?_ (FiniteProbabilityWeights.excessMass_nonneg _ _ _)
  apply FiniteProbabilityWeights.siteLaw_excessMass_le_of_test_bound
  intro φ hφ site
  rw [A.law_zero_layers, selectedJointReference, FiniteProbabilityWeights.mean_prod,
    FiniteProbabilityWeights.mean_comm]
  have hcard : (Fintype.card (integerBox N) : ℝ) / Fintype.card A.bases ≤ 2 := by
    simpa only [Fintype.card_coe] using
      trimmedIntegerBox_card_ratio_le_two N _ A.trimMargin_proper hloss
  have hinj (noise : rectangularWeightIndices 0 A.widths 1) :
      Function.Injective (fun a : A.bases => A.physicalBox hξ hmargin (a, noise) site) := by
    intro a a' heq
    apply Subtype.ext
    have hv := congrArg Subtype.val heq
    change a.val + integerPhysicalSite site.val noise.val =
      a'.val + integerPhysicalSite site.val noise.val at hv
    exact add_right_cancel hv
  have hbound (noise : rectangularWeightIndices 0 A.widths 1) :
      (FiniteProbabilityWeights.uniformFinset A.bases A.bases_nonempty).mean
        (fun a => φ (A.physicalBox hξ hmargin (a, noise) site)) ≤
      2 * (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).mean φ := by
    exact (FiniteProbabilityWeights.uniform_injective_mean_le _ (hinj noise) φ
      (fun x => (hφ x).1)).trans
        (mul_le_mul_of_nonneg_right hcard
          ((FiniteProbabilityWeights.uniformFinset (integerBox N)
            A.integerBox_nonempty).mean_nonneg (fun x => (hφ x).1)))
  simpa only [FiniteProbabilityWeights.mean_const, add_zero] using
    (selectedResidueFiniteLaw stride cells A.widths A.widths_pos A.smooth_mass_pos).mean_mono hbound

theorem fixedCenter_excess_zero_layers_of_spatial_cutoff
    (hξ : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ x, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N x : ℝ)) :
    letI : Nonempty A.Site := A.site_nonempty
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ hmargin)) 2 = 0 := by
  apply A.fixedCenter_excess_zero_layers hξ hmargin
  rw [htrim] at hN ⊢
  obtain ⟨_, _, _, _, _, _, hloss⟩ :=
    unconditionedSpatialWidthBudget (K := LayerSamplerVariables G I n B)
      (allocatedExternalCandidateRootBudget_nonneg B U b S) hsurplus hsurplus1 N hN
  linarith

theorem fixedCenter_excess_zero_layers_le
    (hξ : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hloss : (∑ x, 2 * (spatialTrimMargin τ N x : ℝ) / N x) ≤ 1 / 2)
    (accuracy : ℝ) :
    letI : Nonempty A.Site := A.site_nonempty
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ hmargin)) 2 ≤
        6 * positiveProjectionAccuracy accuracy := by
  rw [A.fixedCenter_excess_zero_layers hξ hmargin hloss]
  exact mul_nonneg (by norm_num) (Real.exp_nonneg _)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
