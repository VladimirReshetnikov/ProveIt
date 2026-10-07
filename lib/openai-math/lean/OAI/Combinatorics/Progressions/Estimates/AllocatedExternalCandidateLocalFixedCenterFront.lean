import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleUniversalMaskProductiveGood
import OAI.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation
import OAI.Combinatorics.Progressions.Polynomial.AllocatedExternalCandidateFixedCenterDegreeModel
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateFixedLawSpatialFamily
import OAI.Combinatorics.Progressions.Probability.FiniteProbabilityUniformResidualGood

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

local instance fixedCenterUniversalSiteNonempty : Nonempty A.Site := A.site_nonempty

theorem exists_fixedCenter_universal_forecast_model (degree : ℕ)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceNonneg : 0 ≤ pSlice) (hTestBudget : 2 ≤ pTest)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection degree pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let Packet := UniversalLocalMajorSliceTest A.sides degree pSlice pTest
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin)
        (fun _ (packet : Packet) => packet.slice.subtypeSites)
        (fun _ (packet : Packet) site => packet.weight site.val) model.residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro Packet commonBudget Qmodel native
  have hSides (i : LayerSamplerVariables G I n B) : 0 < A.sides i := by
    cases i with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U b S j
  let : Nonempty Packet := UniversalLocalMajorSliceTest.nonempty A.sides hSides
    degree pSlice pTest hSliceNonneg hTestBudget
  have hmodel := A.exists_fixedCenter_degree_forecast_model degree hξone hmargin
    hu hp hbudget hNative hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
    (Tests := fun _ => Packet) (Ldetect := fun _ packet => packet.nativeModel.L)
    (dims := fun _ packet => packet.nativeModel.dim)
    (fun _ packet => packet.nativeModel.model) (fun _ packet => packet.nativeModel.test)
    (fun _ packet => packet.slice.subtypeSites)
    (fun _ packet i => (packet.slice.start i : ℤ))
    (fun _ packet => packet.stride) (fun _ packet => packet.slice.length)
    (fun _ packet => packet.stride_pos)
    (fun _ packet => packet.slice.subtypeSites_image_val.trans packet.slice.integerPoints_eq_commonStrideBox)
    (fun _ packet => packet.slice.subtypeSites_dense packet.dense)
    (fun _ packet => packet.nativeModel.complexity)
    (fun _ packet => by exact_mod_cast packet.nativeModel.norm)
    data input hinput
  simpa only [UniversalLocalMajorSliceTest.weight_eq_native_eval] using hmodel

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

local instance fixedCenterMaskSiteNonempty : Nonempty A.Site := A.site_nonempty

theorem exists_fixedCenter_mask_models (degree : ℕ)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceNonneg : 0 ≤ pSlice) (hTestBudget : 2 ≤ pTest)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection degree pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    {Freq Bin Y : Type*}
    (F : Freq → integerBox N → Y → ℂ) (centers : Freq → Bin → Y → ℂ)
    {ε : ℝ} (hnet : ∀ f x, ∃ i, ∀ y, ‖F f x y - centers f i y‖ ≤ ε)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let Packet := UniversalLocalMajorSliceTest A.sides degree pSlice pTest
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ models : Freq × Bin → CenteredForecastModel (integerBox N), ∀ branch,
      (∀ i, (models branch).models i ∈ native) ∧
      externalNetMaskFamily F centers hnet input branch =
        (∑ i, (models branch).coefficient i • (models branch).models i) +
          (models branch).residual ∧
      (∑ i, |(models branch).coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin)
        (fun _ (packet : Packet) => packet.slice.subtypeSites)
        (fun _ (packet : Packet) site => packet.weight site.val) (models branch).residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        (models branch).residual (data f).target‖ ≤ Real.exp (-u)) ∧
      ((models branch).nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro Packet commonBudget Qmodel native
  have hmodel := fun branch : Freq × Bin =>
    A.exists_fixedCenter_universal_forecast_model degree hξone hmargin
      hu hp hbudget hNative hSliceNonneg hTestBudget hSliceLog hC hCp hCap hAccuracy
      hPrecision hdirect hexcess data (externalNetMaskFamily F centers hnet input branch)
      (externalNetMaskFamily_norm_le F centers hnet input (Real.exp_nonneg p) hinput branch)
  choose models hmodels using hmodel
  exact ⟨models, hmodels⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

local instance fixedCenterUniformSiteNonempty : Nonempty A.Site := A.site_nonempty

theorem exists_fixedCenter_uniform_forecast_model (degree : ℕ)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceNonneg : 0 ≤ pSlice) (hTestBudget : 2 ≤ pTest)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection degree pSlice pTest localBudget
      (Real.exp (-(2 * u + 4 * p + 8))))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let Packet := UniversalLocalMajorSliceTest A.sides degree pSlice pTest
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin)
        (fun _ (packet : Packet) => packet.slice.subtypeSites)
        (fun _ (packet : Packet) site => packet.weight site.val) model.residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  have hthreshold := (forecastAugmentedUnitThreshold_bounds hu hp (Real.exp_nonneg _)
    (zero_le_one.trans hC) (Real.exp_le_exp.mpr hSliceLog) hCp
    (Real.exp_le_exp.mpr hCap)).2.2
  exact A.exists_fixedCenter_universal_forecast_model degree hξone hmargin
    hu hp hbudget hNative hSliceNonneg hTestBudget hSliceLog hC hCp hCap
    hAccuracy hPrecision (NativeDetection.mono_tests A hdirect le_rfl le_rfl hthreshold) hexcess data input hinput

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

omit [∀ j, Fintype (J j)] in

theorem contracted_member_net {Bin : Type} (representative : Bin → integerBox N)
    {ε : ℝ}
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤ ε) :
    ∀ f (x : integerBox N), ∃ i, ∀ y,
      ‖(early.U f x.val).observable y - (early.U f (representative i).val).observable y‖ ≤ ε := by
  intro f x
  obtain ⟨i, hi⟩ := hnet x
  exact ⟨i, early.contractive f x.val (representative i).val ε hi⟩

theorem mass_after_native_selection
    {retained : Finset A.Path} {selectionLog : ℝ}
    (hmass : Real.exp (-selectionLog) * A.law.mass selected.retained ≤ A.law.mass retained) :
    Real.exp (-(q + selectionLog)) * A.law.mass P.productive ≤ A.law.mass retained := by
  calc
    _ = Real.exp (-selectionLog) * (A.law.mass P.productive * Real.exp (-q)) := by
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ Real.exp (-selectionLog) * A.law.mass selected.retained :=
      mul_le_mul_of_nonneg_left selected.mass (Real.exp_nonneg _)
    _ ≤ A.law.mass retained := hmass

theorem exists_spatialNativeFamily
    {Bin : Type} [Fintype Bin] [Nonempty Bin]
    (representative : Bin → integerBox N)
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤
        Real.exp (-(p + q + 2)))
    (models : (early.Freq × Bin) → CenteredForecastModel (integerBox N))
    {pNative coefficientLog termLog binLog dimensionLog Eres sliceBudget testBudget : ℝ}
    (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    {Y Forecast : Type} [MeasurableSpace Y]
    (jointLaw : Measure Y) (referenceLaw : FiniteProbabilityWeights (integerBox N))
    (forecast : Forecast → integerBox N → ℂ)
    (localSeminorm : (integerBox N → ℂ) → ℝ)
    (selectedLocal : (integerBox N → ℂ) → (Y → ℂ) → Prop)
    (residualBound : ℝ)
    (hmodels : ∀ branch, CenteredForecastModelBounds jointLaw
      (twistedNativeSampleFunctions (fun _ : X => 1) s pNative
        (fun x : integerBox N => x.val)
        (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
          (x : integerBox N) => twist.eval N poly x.val))
      referenceLaw forecast localSeminorm selectedLocal
      (externalNetMaskFamily (fun f (x : integerBox N) => (early.U f x.val).observable)
        (fun f i => (early.U f (representative i).val).observable)
        (contracted_member_net (early := early) representative hnet) (fun x => weight x.val) branch)
      (Real.exp coefficientLog) residualBound (Real.exp termLog) (models branch))
    (hq : 0 ≤ q) (hcoefficient : 0 ≤ coefficientLog)
    (hterm : 0 ≤ termLog) (hbin : 0 ≤ binLog)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hdim : (finrank ℚ top : ℝ) ≤ dimensionLog)
    (hξ1 : ξ ≤ 1)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hcost0 : 0 ≤ cost) (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : q ≤ testBudget)
    (hUniform : ∀ a ∈ P.productive, ∀ f i,
      ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
        ‖𝔼 site ∈ packet.slice.subtypeSites,
          (models (f, i)).residual (A.boxedPhysical hξ1 a site) *
            packet.weight site.val‖ ≤ Real.exp (-Eres))
    (hresBudget : q + q + binLog + 4 ≤ Eres)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {pFamily : ℝ} (hpFamily : 0 ≤ pFamily)
    (hcost : cost ≤ pFamily) (hlocal : q ≤ pFamily) (hnative : pNative ≤ pFamily)
    (hperiod : periodCap * coverCap ≤ Real.exp pFamily)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ pFamily) :
    ∃ (retained : Finset A.Path), retained ⊆ selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(dimensionLog * (binLog + termLog))) * A.law.mass selected.retained ≤
        A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot selected.code) D Fmark φ marked keep cost pFamily q pNative
          (q + binLog + coefficientLog + 4) periodCap coverCap Lip,
        F.sourceChart = P.precenterChart hpos ∧
        (∀ a, HEq (F.sourceCandidate a) (P.precenterCandidate hpos a)) ∧
        F.η = (fun k => early.eta (kernelProjectionSelectedPivot selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤
          (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight) := by
  have hU : ∀ f (i : integerBox N), (early.U f i.val).ComplexityLE q := fun f i => (early.U_bounds f i.val).1
  have hnetU := contracted_member_net (early := early) representative hnet
  have hmodelError := precenter_native_selection_model_error_budget p q
  have hres := precenter_native_selection_residual_budget (rFreq := q) (pLocal := q) hcard hresBudget
  have hcorr := precenter_native_selection_correlation_budget (rFreq := q)
    (c := coefficientLog) hcard
  obtain ⟨retained, hsub, hmassPos, hmass, F, hFC, hFcandidate, hFeta, hFcorr⟩ :=
    A.exists_precenter_spatial_native_family D (P.precenterChart hpos) (P.precenterCandidate hpos)
      hξ1 (fun f x => early.U f x.val) representative early.eta hU hnetU
      (fun x => weight x.val) models periodCap coverCap Lip jointLaw referenceLaw forecast
      localSeminorm selectedLocal hmodels (Real.exp_pos _) (Real.one_le_exp_iff.mpr hterm)
      selected.code A.law selected.retained selected.positive_mass (Real.exp_nonneg _)
      (Real.exp_pos _) hmodelError (fun x => hweight x.val x.property)
      hcost0 (fun a _ i => P.precenterChart_frozen hpos a i) hSliceBudget hTestBudget
      (by
        intro a ha f i packet
        rw [P.precenterChart_path hpos a (selected.subset ha)]
        exact hUniform a (selected.subset ha) f i packet)
      hres (fun a ha i f hif => (selected.pivots a ha i f hif).le) hcorr keep
      (P.precenterChart_keep hpos keep hkeep) hpoly hτ1 hσ1 Cgeo hCgeo hchart hsmall
      hpFamily hq (by positivity) hcost hlocal hnative hperiod hvariation
      (fun f i => (early.eta_height f i).trans hlocal) (fun f x => early.vertical f x.val) hK
  refine ⟨retained, hsub, hmassPos, ?_, F, hFC, hFcandidate, hFeta, hFcorr, ?_, ?_, ?_⟩
  · exact (precenter_native_selection_mass_budget (finrank ℚ top) hbin hterm hdim hcard
      (A.law.mass_nonneg selected.retained)).trans hmass
  · intro a ha
    rw [hFC]
    exact P.precenterChart_path hpos a (selected.subset (hsub ha))
  · intro a
    rw [hFC]
    exact P.precenterChart_center hpos a
  · intro a ha
    have hs := selected.scores a (hsub ha)
    have hchartEq := congrFun hFC a
    have heq : (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight =
        (P.precenterCandidate hpos a).score (fun x => (selected.tests x).observable) weight := by
      exact AllocatedExternalLocalCandidate.score_of_heq hchartEq (hFcandidate a) _ _
    exact hs.trans_eq heq.symm

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

theorem fixedCenter_residual_budget
    {Bin : Type} [Fintype Bin] {binLog massLog Eres u : ℝ}
    (hmass : Real.exp (-massLog) ≤ A.law.mass P.productive)
    (hbin : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hu : (q + binLog) + Eres + (massLog + q) + 2 ≤ u) :
    (Fintype.card (early.Freq × Bin) : ℝ) * Real.exp (-u) ≤
      Real.exp (-Eres) * A.law.mass selected.retained / 2 := by
  have hselected : Real.exp (-(massLog + q)) ≤ A.law.mass selected.retained := by
    calc
      _ = Real.exp (-massLog) * Real.exp (-q) := by rw [neg_add, Real.exp_add]
      _ ≤ A.law.mass P.productive * Real.exp (-q) :=
        mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
      _ ≤ _ := selected.mass
  have hcard : (Fintype.card (early.Freq × Bin) : ℝ) ≤ Real.exp (q + binLog) := by
    rw [Fintype.card_prod, Nat.cast_mul, Real.exp_add]
    exact mul_le_mul early.card_bound hbin (Nat.cast_nonneg _) (Real.exp_nonneg _)
  exact FiniteProbabilityWeights.uniformResidualGood_exp_budget hselected hcard hu

theorem fixedCenter_mass_after_native_selection
    {retained : Finset A.Path} {selectionLog : ℝ}
    (hmass : Real.exp (-selectionLog) * (A.law.mass selected.retained / 2) ≤
      A.law.mass retained) :
    Real.exp (-(q + selectionLog + 2)) * A.law.mass P.productive ≤ A.law.mass retained := by
  have hhalf : Real.exp (-(selectionLog + 2)) ≤ Real.exp (-selectionLog) / 2 := by
    simpa using precenter_native_selection_model_error_budget 0 selectionLog
  have h := selected.mass_after_native_selection (selectionLog := selectionLog + 2) (by
    calc
      _ ≤ (Real.exp (-selectionLog) / 2) * A.law.mass selected.retained :=
        mul_le_mul_of_nonneg_right hhalf (A.law.mass_nonneg _)
      _ = Real.exp (-selectionLog) * (A.law.mass selected.retained / 2) := by ring
      _ ≤ _ := hmass)
  simpa only [add_assoc] using h

theorem exists_fixedCenter_spatialNativeFamily
    {Bin : Type} [Fintype Bin] [Nonempty Bin]
    (representative : Bin → integerBox N)
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤
        Real.exp (-(p + q + 2)))
    (models : (early.Freq × Bin) → CenteredForecastModel (integerBox N))
    {pNative coefficientLog termLog binLog dimensionLog Eres sliceBudget testBudget : ℝ}
    (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    (hnativeModels : ∀ branch i, (models branch).models i ∈
      twistedNativeSampleFunctions (fun _ : X => 1) s pNative
        (fun x : integerBox N => x.val)
        (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
          (x : integerBox N) => twist.eval N poly x.val))
    (hmodel : ∀ branch, externalNetMaskFamily
        (fun f (x : integerBox N) => (early.U f x.val).observable)
        (fun f i => (early.U f (representative i).val).observable)
        (contracted_member_net (early := early) representative hnet) (fun x => weight x.val) branch =
      (∑ i, (models branch).coefficient i • (models branch).models i) + (models branch).residual)
    (hcoefficientModels : ∀ branch,
      (∑ i, |(models branch).coefficient i|) ≤ Real.exp coefficientLog)
    (hterms : ∀ branch, ((models branch).nterms : ℝ) ≤ Real.exp termLog)
    (hq : 0 ≤ q) (hcoefficient : 0 ≤ coefficientLog)
    (hterm : 0 ≤ termLog) (hbin : 0 ≤ binLog)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hdim : (finrank ℚ top : ℝ) ≤ dimensionLog)
    (hξ1 : ξ ≤ 1)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hcost0 : 0 ≤ cost) (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : q ≤ testBudget)
    {u : ℝ}
    (hlocalResidual : ∀ branch, sampledSliceSeminorm A.law (A.boxedPhysical hξ1)
      (fun _ (packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget) =>
        packet.slice.subtypeSites)
      (fun _ packet site => packet.weight site.val) (models branch).residual ≤ Real.exp (-u))
    (hMarkovBudget : (Fintype.card (early.Freq × Bin) : ℝ) * Real.exp (-u) ≤
      Real.exp (-Eres) * A.law.mass selected.retained / 2)
    (hresBudget : q + q + binLog + 4 ≤ Eres)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {pFamily : ℝ} (hpFamily : 0 ≤ pFamily)
    (hcost : cost ≤ pFamily) (hlocal : q ≤ pFamily) (hnative : pNative ≤ pFamily)
    (hperiod : periodCap * coverCap ≤ Real.exp pFamily)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ pFamily) :
    ∃ (retained : Finset A.Path), retained ⊆ selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(dimensionLog * (binLog + termLog))) * (A.law.mass selected.retained / 2) ≤
        A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot selected.code) D Fmark φ marked keep cost pFamily q pNative
          (q + binLog + coefficientLog + 4) periodCap coverCap Lip,
        F.sourceChart = P.precenterChart hpos ∧
        (∀ a, HEq (F.sourceCandidate a) (P.precenterCandidate hpos a)) ∧
        F.η = (fun k => early.eta (kernelProjectionSelectedPivot selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤
          (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight) := by
  let : Nonempty A.Site := A.site_nonempty
  let slices := fun (_ : A.Path)
    (packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget) => packet.slice.subtypeSites
  let tests := fun (_ : A.Path)
    (packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget) (site : A.Site) =>
      packet.weight site.val
  have hDense : ∀ a packet, IsDenseCommonStrideBox A.sides sliceBudget
      ((slices a packet).image Subtype.val) := fun _ packet => packet.slice.subtypeSites_dense packet.dense
  have hsize := preparedCenteredForecast_slice_family_bounds B U b S slices hDense
  obtain ⟨good, hgoodSub, hgoodMass, hgoodPos, hgood⟩ :=
    A.law.exists_uniformSliceResidualGood selected.retained (A.boxedPhysical hξ1) slices tests
      (fun branch => (models branch).residual) hsize.1 hsize.2
      (fun _ packet site => packet.weight_norm site.val) hlocalResidual selected.positive_mass
      (Real.exp_pos (-Eres)) hMarkovBudget
  have hU : ∀ f (i : integerBox N), (early.U f i.val).ComplexityLE q := fun f i => (early.U_bounds f i.val).1
  have hnetU := contracted_member_net (early := early) representative hnet
  have hmodelError := precenter_native_selection_model_error_budget p q
  have hres := precenter_native_selection_residual_budget (rFreq := q) (pLocal := q) hcard hresBudget
  have hcorr := precenter_native_selection_correlation_budget (rFreq := q)
    (c := coefficientLog) hcard
  obtain ⟨retained, hsub, hmassPos, hmass, F, hFC, hFcandidate, hFeta, hFcorr⟩ :=
    A.exists_fixedLaw_spatial_native_family D (P.precenterChart hpos) (P.precenterCandidate hpos)
      hξ1 (fun f x => early.U f x.val) representative early.eta hU hnetU
      (fun x => weight x.val) models periodCap coverCap Lip hnativeModels hmodel hcoefficientModels hterms (Real.exp_pos _) (Real.one_le_exp_iff.mpr hterm)
      selected.code A.law good hgoodPos (Real.exp_nonneg _)
      (Real.exp_pos _) hmodelError (fun x => hweight x.val x.property)
      hcost0 (fun a _ i => P.precenterChart_frozen hpos a i) hSliceBudget hTestBudget
      (by
        intro a ha f i packet
        rw [P.precenterChart_path hpos a (selected.subset (hgoodSub ha))]
        exact hgood a ha (f, i) packet)
      hres (fun a ha i f hif => (selected.pivots a (hgoodSub ha) i f hif).le) hcorr keep
      (P.precenterChart_keep hpos keep hkeep) hpoly hτ1 hσ1 Cgeo hCgeo hchart hsmall
      hpFamily hq (by positivity) hcost hlocal hnative hperiod hvariation
      (fun f i => (early.eta_height f i).trans hlocal) (fun f x => early.vertical f x.val) hK
  refine ⟨retained, fun a ha => hgoodSub (hsub ha), hmassPos, ?_, F, hFC, hFcandidate, hFeta, hFcorr, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hgoodMass (Real.exp_nonneg _)).trans
      ((precenter_native_selection_mass_budget (finrank ℚ top) hbin hterm hdim hcard
        (A.law.mass_nonneg good)).trans hmass)
  · intro a ha
    rw [hFC]
    exact P.precenterChart_path hpos a (selected.subset (hgoodSub (hsub ha)))
  · intro a
    rw [hFC]
    exact P.precenterChart_center hpos a
  · intro a ha
    have hs := selected.scores a (hgoodSub (hsub ha))
    have hchartEq := congrFun hFC a
    have heq : (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight =
        (P.precenterCandidate hpos a).score (fun x => (selected.tests x).observable) weight := by
      exact AllocatedExternalLocalCandidate.score_of_heq hchartEq (hFcandidate a) _ _
    exact hs.trans_eq heq.symm

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

local instance actualFixedCenterFrontSiteNonempty : Nonempty A.Site := A.site_nonempty

theorem exists_actualFixedCenter_spatialNativeFamily
    {Bin : Type} [Fintype Bin] [Nonempty Bin]
    (representative : Bin → integerBox N)
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤
        Real.exp (-(p + q + 2)))
    {u pModel sliceBudget testBudget localBudget forecastNative forecastMassLog capLog
      Edata projectionPrecision marginalCap binLog dimensionLog Eres sourceMassLog : ℝ}
    (hξ1 : ξ ≤ 1)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hinputBudget : p ≤ pModel)
    (hlocalBudget : 0 ≤ localBudget) (hforecastNative : 0 ≤ forecastNative)
    (hSliceNonneg : 0 ≤ sliceBudget) (hTestNontrivial : 2 ≤ testBudget)
    (hSliceLog : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
    (hMarginalCap : 1 ≤ marginalCap) (hMarginalBound : marginalCap ≤ Real.exp pModel)
    (hCap : capLog ≤ pModel)
    (hAccuracy : 2 * u + 4 * pModel + 12 ≤ Edata)
    (hPrecision : u + 2 * pModel + max (max localBudget (3 * forecastNative + 3))
      (2 * u + 4 * pModel + max 0 forecastMassLog + 20) + 32 ≤ projectionPrecision)
    (hdirect : A.NativeDetection s sliceBudget testBudget localBudget
      (Real.exp (-(2 * u + 4 * pModel + 8))))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ1 (fun x => (A.trimMargin_proper x).le))) marginalCap ≤
        6 * positiveProjectionAccuracy projectionPrecision)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly forecastNative forecastMassLog capLog Edata)
    (hq : 0 ≤ q) (hbin : 0 ≤ binLog)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hdim : (finrank ℚ top : ℝ) ≤ dimensionLog)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hcost0 : 0 ≤ cost) (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : q ≤ testBudget)
    (hsourceMass : Real.exp (-sourceMassLog) ≤ A.law.mass P.productive)
    (hMarkovPrecision : (q + binLog) + Eres + (sourceMassLog + q) + 2 ≤ u)
    (hresBudget : q + q + binLog + 4 ≤ Eres)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {pFamily : ℝ} (hpFamily : 0 ≤ pFamily)
    (hcost : cost ≤ pFamily) (hlocal : q ≤ pFamily)
    (hperiod : 2 * max localBudget (3 * forecastNative + 3) ≤ pFamily)
    (hvariation : Real.exp (max localBudget (3 * forecastNative + 3)) *
      (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ pFamily) :
    let commonBudget := max localBudget (3 * forecastNative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * pModel + max 0 forecastMassLog + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * u + 4 * pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(dimensionLog * (binLog + termLog))) * (A.law.mass selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(q + dimensionLog * (binLog + termLog) + 2)) * A.law.mass P.productive ≤
        A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot selected.code) D Fmark φ marked keep cost pFamily q commonBudget
          (q + binLog + coefficientLog + 4) (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = P.precenterChart hpos ∧
        (∀ a, HEq (F.sourceCandidate a) (P.precenterCandidate hpos a)) ∧
        F.η = (fun k => early.eta (kernelProjectionSelectedPivot selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤
          (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight) := by
  intro commonBudget Qmodel coefficientLog termLog
  have hcommon : 0 ≤ commonBudget := hlocalBudget.trans (le_max_left _ _)
  have hQ : 0 ≤ Qmodel := hcommon.trans (le_max_left _ _)
  have hnative : commonBudget ≤ pFamily := by
    have := hperiod
    change 2 * commonBudget ≤ pFamily at this
    linarith only [this, hcommon]
  have hperiod' : Real.exp commonBudget * Real.exp commonBudget ≤ Real.exp pFamily := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hperiod]
  have hweightModel (x : integerBox N) : ‖weight x.val‖ ≤ Real.exp pModel :=
    (hweight x.val x.property).trans (Real.exp_le_exp.mpr hinputBudget)
  have hthreshold := (forecastAugmentedUnitThreshold_bounds hu hpModel (Real.exp_nonneg _)
    (zero_le_one.trans hMarginalCap) (Real.exp_le_exp.mpr hSliceLog) hMarginalBound
    (Real.exp_le_exp.mpr hCap)).2.2
  have hdirect' : A.NativeDetection s sliceBudget testBudget localBudget
      (forecastAugmentedUnitThreshold u pModel
        (Real.exp (sliceBudget * Fintype.card (LayerSamplerVariables G I n B)))
        marginalCap (Real.exp capLog)) :=
    AllocatedExternalCandidateSampler.NativeDetection.mono_tests
      A hdirect le_rfl le_rfl hthreshold
  obtain ⟨models, hmodels⟩ := A.exists_fixedCenter_mask_models s hξ1
    (fun x => (A.trimMargin_proper x).le) hu hpModel hlocalBudget hforecastNative
    hSliceNonneg hTestNontrivial hSliceLog hMarginalCap hMarginalBound hCap hAccuracy
    hPrecision hdirect' hexcess data (fun f (x : integerBox N) => (early.U f x.val).observable)
    (fun f i => (early.U f (representative i).val).observable)
    (contracted_member_net (early := early) representative hnet) (fun x => weight x.val) hweightModel
  obtain ⟨retained, hsub, hpos', hmass, F, hFC, hFcandidate, hFeta, hcorr, hpath, hcenter, hscore⟩ :=
    selected.exists_fixedCenter_spatialNativeFamily representative hnet models
      (Real.exp commonBudget) (Real.exp commonBudget) ⟨Real.exp commonBudget, Real.exp_nonneg _⟩
      (fun branch => (hmodels branch).1) (fun branch => (hmodels branch).2.1)
      (fun branch => (hmodels branch).2.2.1) (fun branch => (hmodels branch).2.2.2.2.2)
      hq (by positivity) (by positivity)
      hbin hcard hdim hξ1 hweight hcost0 hSliceBudget hTestBudget
      (fun branch => (hmodels branch).2.2.2.1)
      (selected.fixedCenter_residual_budget hsourceMass hcard hMarkovPrecision) hresBudget
      keep hkeep hpoly hτ1 hσ1 Cgeo hCgeo hchart hsmall hpFamily hcost hlocal hnative
      hperiod' hvariation hK
  exact ⟨retained, hsub, hpos', hmass, selected.fixedCenter_mass_after_native_selection hmass,
    F, hFC, hFcandidate, hFeta, hcorr, hpath, hcenter, hscore⟩

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

local instance localFixedCenterFrontSiteNonempty : Nonempty A.Site := A.site_nonempty

theorem exists_localFixedCenter_spatialNativeFamily
    {Bin : Type} [Fintype Bin] [Nonempty Bin]
    (representative : Bin → integerBox N)
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤
        Real.exp (-(p + q + 2)))
    {u pModel sliceBudget testBudget localBudget projectionPrecision marginalCap binLog dimensionLog Eres sourceMassLog : ℝ}
    (hξ1 : ξ ≤ 1)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hinputBudget : p ≤ pModel)
    (hlocalBudget : 0 ≤ localBudget)
    (hSliceNonneg : 0 ≤ sliceBudget) (hTestNontrivial : 2 ≤ testBudget)
    (hSliceLog : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
    (hMarginalCap : 1 ≤ marginalCap) (hMarginalBound : marginalCap ≤ Real.exp pModel)
    (hPrecision : u + 2 * pModel + max (max localBudget 3)
      (2 * u + 4 * pModel + 20) + 32 ≤ projectionPrecision)
    (hdirect : A.NativeDetection s sliceBudget testBudget localBudget
      (Real.exp (-(2 * u + 4 * pModel + 8))))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ1 (fun x => (A.trimMargin_proper x).le))) marginalCap ≤
        6 * positiveProjectionAccuracy projectionPrecision)
    (hq : 0 ≤ q) (hbin : 0 ≤ binLog)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hdim : (finrank ℚ top : ℝ) ≤ dimensionLog)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hcost0 : 0 ≤ cost) (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : q ≤ testBudget)
    (hsourceMass : Real.exp (-sourceMassLog) ≤ A.law.mass P.productive)
    (hMarkovPrecision : (q + binLog) + Eres + (sourceMassLog + q) + 2 ≤ u)
    (hresBudget : q + q + binLog + 4 ≤ Eres)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {pFamily : ℝ} (hpFamily : 0 ≤ pFamily)
    (hcost : cost ≤ pFamily) (hlocal : q ≤ pFamily)
    (hperiod : 2 * max localBudget 3 ≤ pFamily)
    (hvariation : Real.exp (max localBudget 3) *
      (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ pFamily) :
    let commonBudget := max localBudget 3
    let Qmodel := max commonBudget (2 * u + 4 * pModel + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * u + 4 * pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(dimensionLog * (binLog + termLog))) * (A.law.mass selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(q + dimensionLog * (binLog + termLog) + 2)) * A.law.mass P.productive ≤
        A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot selected.code) D Fmark φ marked keep cost pFamily q commonBudget
          (q + binLog + coefficientLog + 4) (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = P.precenterChart hpos ∧
        (∀ a, HEq (F.sourceCandidate a) (P.precenterCandidate hpos a)) ∧
        F.η = (fun k => early.eta (kernelProjectionSelectedPivot selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤
          (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight) := by
  let data : PUnit → ActualForecastData N poly 0 0 0 (2 * u + 4 * pModel + 12) :=
    fun _ => ActualForecastData.zero N poly 0 0 0 (2 * u + 4 * pModel + 12)
  have hprecision' : u + 2 * pModel + max (max localBudget (3 * (0 : ℝ) + 3))
      (2 * u + 4 * pModel + max 0 0 + 20) + 32 ≤ projectionPrecision := by
    simpa only [mul_zero, zero_add, max_self, add_zero] using hPrecision
  have hperiod' : 2 * max localBudget (3 * (0 : ℝ) + 3) ≤ pFamily := by
    simpa only [mul_zero, zero_add] using hperiod
  have hvariation' : Real.exp (max localBudget (3 * (0 : ℝ) + 3)) *
      (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily := by
    simpa only [mul_zero, zero_add] using hvariation
  have result := selected.exists_actualFixedCenter_spatialNativeFamily representative hnet hξ1
      hu hpModel hinputBudget hlocalBudget (le_refl 0) hSliceNonneg hTestNontrivial hSliceLog
      hMarginalCap hMarginalBound hpModel le_rfl hprecision' hdirect hexcess data hq hbin
      hcard hdim hweight hcost0 hSliceBudget hTestBudget hsourceMass hMarkovPrecision hresBudget
      keep hkeep hpoly hτ1 hσ1 Cgeo hCgeo hchart hsmall hpFamily hcost hlocal hperiod'
      hvariation' hK
  rw [show (3 : ℝ) * 0 + 3 = 3 by ring] at result
  rw [show max (0 : ℝ) 0 = 0 from max_self 0, add_zero] at result
  exact result

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
