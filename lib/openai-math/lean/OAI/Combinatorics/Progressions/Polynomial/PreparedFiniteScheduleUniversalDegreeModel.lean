import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredStagedModelProductiveGood
import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardDegreeModelAttachment
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section ActualData

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
variable {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hbox : (integerBox N).Nonempty)
variable (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
variable (hweight : ∀ z, Measurable (fun center => (law center).weight z))
local notation "Sites" => integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))

theorem preparedFiniteScheduleDegreeModelsAtLaw_actualData
    (physical : Path → integerBox (Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S)) → integerBox N)
    (degree : ℕ) (u p cap sliceLog testLog budget E : ℝ)
    (hModel : PreparedFiniteScheduleDegreeModelsAtLaw B U b S N Pdetect μ poly hbox law hweight
      physical degree u p cap sliceLog testLog budget E)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset Sites)
    (cdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (stepdetect : ∀ z, Tests z → ℕ)
    (Hdetect : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < stepdetect z j)
    (hSlices : ∀ z j, (slices z j).image Subtype.val =
      commonStrideBox (cdetect z j) (stepdetect z j) (Hdetect z j))
    (hDense : ∀ z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) sliceLog
      ((slices z j).image Subtype.val))
    (hnum : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    (hcomplex : ∀ z j, (Vdetect z j).ComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog))
    (hcap : ∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1)
    {Forecast : Type} [Nonempty Forecast] {Pnative massLog capLog Edata : ℝ}
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (hNative : 0 ≤ Pnative)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hCap : Real.exp capLog ≤ cap)
    (hPrecision : actualForecastDataModelRequired budget Pnative massLog u p ≤ E)
    {Branch : Type} [Fintype Branch]
    (input : Branch → integerBox N → ℂ)
    (hinput : ∀ branch v, ‖input branch v‖ ≤ Real.exp p) :
    let tests : ∀ z, Tests z → Sites → ℂ := fun z j t => star ((Vdetect z j).eval
      (commonStrideIndex (cdetect z j) (stepdetect z j) t.val))
    let commonBudget := max budget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : Fin nX → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : (integerBox N → ℂ) → ℝ := sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests
    let selectedLocal : (integerBox N → ℂ) →
      (CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) → Prop :=
      fun (err : integerBox N → ℂ)
      (errLocal : CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) =>
      ∀ center z, ∃ j, errLocal (center, z) =
        𝔼 t ∈ slices z j, err (physical z t) * tests z j t
    ∃ models : Branch → CenteredForecastModel (integerBox N),
      ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        native (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) (fun f => (data f).target)
        localSeminorm selectedLocal (input branch) (Real.exp (Qmodel + 2))
        (Real.exp (-u)) (Real.exp (2 * Qmodel + 2 * u + 4 * p + 34)) (models branch) :=
  hModel Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hSlices hDense hnum hcomplex hcap (fun f => (data f).target)
    hNative (le_max_left _ _) hPrecision
    (fun f => (data f).Term) (fun f => (data f).coefficient)
    (fun f => (data f).centerConstant) (fun f => (data f).twists)
    (fun f => (data f).mass.trans (Real.exp_le_exp.mpr (le_max_right _ _)))
    (fun f v => ((data f).approximation v).trans
      (Real.exp_le_exp.mpr (neg_le_neg hAccuracy)))
    (fun f v => ((data f).cap v).trans hCap) input hinput

end ActualData

theorem exists_preparedFiniteScheduleActualDegreeModelFamily
    {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ]
    {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hbox : (integerBox N).Nonempty)
    (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Path → integerBox (Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S)) → integerBox N)
    {Stage : Type} {Branch : Stage → Type} [∀ k, Fintype (Branch k)]
    (degree : Stage → ℕ) (u p cap sliceLog testLog budget E : Stage → ℝ)
    (hModel : ∀ k, PreparedFiniteScheduleDegreeModelsAtLaw B U b S N Pdetect μ poly hbox law hweight
      physical (degree k) (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k))
    {Tests : Stage → Path → Type} [∀ k z, Nonempty (Tests k z)]
    {Ldetect : ∀ k z, Tests k z → Type} [∀ k z j, LieRing (Ldetect k z j)]
    [∀ k z j, LieAlgebra ℚ (Ldetect k z j)] {dims : ∀ k z, Tests k z → ℕ}
    [∀ k z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, T2Space (ℝ ⊗[ℚ] Ldetect k z j)]
    (Ddetect : ∀ k z j, RationalFilteredNilmanifold (Ldetect k z j) (degree k) (dims k z j))
    (Vdetect : ∀ k z j, (Ddetect k z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ k z, Tests k z → Finset (integerBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))))
    (cdetect : ∀ k z, Tests k z → LayerSamplerVariables G I n B → ℤ)
    (stepdetect : ∀ k z, Tests k z → ℕ)
    (Hdetect : ∀ k z, Tests k z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ k z j, 0 < stepdetect k z j)
    (hSlices : ∀ k z j, (slices k z j).image Subtype.val =
      commonStrideBox (cdetect k z j) (stepdetect k z j) (Hdetect k z j))
    (hDense : ∀ k z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) (sliceLog k)
      ((slices k z j).image Subtype.val))
    (hnum : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hcomplex : ∀ k z j, (Vdetect k z j).ComplexityLE
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k)))
    (hcap : ∀ k z j, ((Vdetect k z j).normBound : ℝ) ≤ 1)
    {Forecast : Stage → Type} [∀ k, Nonempty (Forecast k)]
    (Pnative massLog capLog Edata : Stage → ℝ)
    (data : ∀ k, Forecast k → ActualForecastData N poly (Pnative k) (massLog k) (capLog k) (Edata k))
    (hNative : ∀ k, 0 ≤ Pnative k)
    (hAccuracy : ∀ k, 2 * u k + 4 * p k + 12 ≤ Edata k)
    (hCap : ∀ k, Real.exp (capLog k) ≤ cap k)
    (hPrecision : ∀ k, actualForecastDataModelRequired (budget k) (Pnative k) (massLog k)
      (u k) (p k) ≤ E k)
    (input : ∀ k, Branch k → integerBox N → ℂ)
    (hinput : ∀ k branch v, ‖input k branch v‖ ≤ Real.exp (p k)) :
    let tests : ∀ k z, Tests k z → integerBox
        (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) → ℂ :=
      fun k z j t => star ((Vdetect k z j).eval
        (commonStrideIndex (cdetect k z j) (stepdetect k z j) t.val))
    let commonBudget := fun k => max (budget k) (3 * Pnative k + 3)
    let Qmodel := fun k => max (commonBudget k) (2 * u k + 4 * p k + max 0 (massLog k) + 20)
    let native := fun k => twistedNativeSampleFunctions (1 : Fin nX → ℕ) (degree k) (commonBudget k)
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp (commonBudget k)) (Real.exp (commonBudget k))
        ⟨Real.exp (commonBudget k), Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : Stage → (integerBox N → ℂ) → ℝ := fun k =>
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical (slices k) (tests k)
    let selectedLocal : Stage → (integerBox N → ℂ) →
        (CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) → Prop :=
      fun k err errLocal => ∀ center z, ∃ j, errLocal (center, z) =
        𝔼 t ∈ slices k z j, err (physical z t) * tests k z j t
    ∃ models : ∀ k, Branch k → CenteredForecastModel (integerBox N),
      (∀ k branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
        (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
        (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
        (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models k branch)) ∧
      (∀ k branch, sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
        physical (slices k) (tests k) (models k branch).residual ≤ Real.exp (-u k)) := by
  classical
  intro tests commonBudget Qmodel native localSeminorm selectedLocal
  have hstage (k : Stage) :
      ∃ models : Branch k → CenteredForecastModel (integerBox N),
        ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
          (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
          (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
          (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
          (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models branch) := by
    exact preparedFiniteScheduleDegreeModelsAtLaw_actualData
      (B := B) (U := U) (b := b) (S := S)
      N Pdetect μ poly hbox law hweight physical
      (degree k) (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k) (hModel k)
      (Ddetect k) (Vdetect k) (slices k) (cdetect k) (stepdetect k) (Hdetect k)
      (hstep k) (hSlices k) (hDense k) (hnum k) (hcomplex k) (hcap k)
      (data k) (hNative k) (hAccuracy k) (hCap k) (hPrecision k) (input k) (hinput k)
  choose models hmodels using hstage
  exact ⟨models, hmodels, fun k branch => (hmodels k branch).2.2.2.1⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable section

attribute [local irreducible] preparedSamplerTransverse preparedCommonBlockCount RankPreparationLayer.rank
attribute [local irreducible] PreparedFiniteScheduleDegreeModelsAtLaw integerBox allocatedPrincipalSides

variable
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    (bW : ∀ j, Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))

local instance (j : Fin m) : DecidableEq (PreparedSamplerContinuous prep j) := Classical.decEq _
local instance (a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)) :
    DecidableEq (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)) a) :=
  Classical.decEq _

variable
    (Pdetect : Polynomial ℕ) (hbox : (integerBox N).Nonempty)
    (physical : (bases × rectangularWeightIndices 0 width 1) → integerBox (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value)
      (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) → integerBox N)
variable
    {Stage : Type} [Fintype Stage] {Branch : Stage → Type} [∀ k, Fintype (Branch k)]
    (degree : Stage → ℕ) (u p cap sliceLog testLog budget E : Stage → ℝ)
variable
    (hModel : ∀ k : Stage, PreparedFiniteScheduleDegreeModelsAtLaw
      (m := m) (nX := nX) (R := R) (σ := σ)
      (Path := bases × rectangularWeightIndices 0 width 1) (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N Pdetect μ poly hbox law hweight
      physical (degree k) (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k))
variable
    {Tests : Stage → (bases × rectangularWeightIndices 0 width 1) → Type} [∀ k z, Nonempty (Tests k z)]
    {Ldetect : ∀ k z, Tests k z → Type} [∀ k z j, LieRing (Ldetect k z j)]
    [∀ k z j, LieAlgebra ℚ (Ldetect k z j)] {dims : ∀ k z, Tests k z → ℕ}
    [∀ k z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect k z j)]
    [∀ k z j, T2Space (ℝ ⊗[ℚ] Ldetect k z j)]
variable
    (Ddetect : ∀ k z j, RationalFilteredNilmanifold (Ldetect k z j) (degree k) (dims k z j))
    (Vdetect : ∀ k z j, (Ddetect k z j).Niltest (fun _ : LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) => 1))
variable
    (slices : ∀ k z, Tests k z → Finset (integerBox
      (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value) (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S))))
    (cdetect : ∀ k z, Tests k z → LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (stepdetect : ∀ k z, Tests k z → ℕ)
    (Hdetect : ∀ k z, Tests k z → LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℕ)
variable
    (hstep : ∀ k z j, 0 < stepdetect k z j)
    (hSlices : ∀ k z j, (slices k z j).image Subtype.val =
      commonStrideBox (cdetect k z j) (stepdetect k z j) (Hdetect k z j))
    (hDense : ∀ k z j, IsDenseCommonStrideBox
      (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value) (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) (sliceLog k)
      ((slices k z j).image Subtype.val))
variable
    (hnum : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hcomplex : ∀ k z j, (Vdetect k z j).ComplexityLE
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k)))
    (hcap : ∀ k z j, ((Vdetect k z j).normBound : ℝ) ≤ 1)
variable
    {Forecast : Stage → Type} [∀ k, Nonempty (Forecast k)]
    (Pnative massLog capLog Edata : Stage → ℝ)
    (data : ∀ k, Forecast k → ActualForecastData N poly (Pnative k) (massLog k) (capLog k) (Edata k))
variable
    (hNative : ∀ k, 0 ≤ Pnative k)
    (hAccuracy : ∀ k, 2 * u k + 4 * p k + 12 ≤ Edata k)
    (hCap : ∀ k, Real.exp (capLog k) ≤ cap k)
    (hPrecision : ∀ k, actualForecastDataModelRequired (budget k) (Pnative k) (massLog k)
      (u k) (p k) ≤ E k)
variable
    (input : ∀ k, Branch k → integerBox N → ℂ)
    (hinput : ∀ k branch v, ‖input k branch v‖ ≤ Real.exp (p k))
variable
    (Bbranch Eres : Stage → ℝ) (stageLog : ℝ)
    (hBranch : ∀ k, (Fintype.card (Branch k) : ℝ) ≤ Real.exp (Bbranch k))
    (hStageCount : (Fintype.card Stage : ℝ) + 1 ≤ Real.exp stageLog)
    (hErrorBudget : ∀ k, Bbranch k + gainLog + Eres k + stageLog + 6 ≤ u k)

include hgood hproductive htest hgain hmean hModel hstep hSlices hDense hnum hcomplex hcap
  hNative hAccuracy hCap hPrecision hinput hBranch hStageCount hErrorBudget in

theorem exists_preparedFiniteScheduleActualDegreeProductiveGood :
    let tests : ∀ k z, Tests k z → integerBox
        (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value) (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) → ℂ :=
      fun k z j t => star ((Vdetect k z j).eval
        (commonStrideIndex (cdetect k z j) (stepdetect k z j) t.val))
    let commonBudget := fun k => max (budget k) (3 * Pnative k + 3)
    let Qmodel := fun k => max (commonBudget k) (2 * u k + 4 * p k + max 0 (massLog k) + 20)
    let native := fun k => twistedNativeSampleFunctions (1 : Fin nX → ℕ) (degree k) (commonBudget k)
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, (fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)
        (Real.exp (commonBudget k)) (Real.exp (commonBudget k))
        ⟨Real.exp (commonBudget k), Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : Stage → (integerBox N → ℂ) → ℝ := fun k =>
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical (slices k) (tests k)
    let selectedLocal : Stage → (integerBox N → ℂ) →
        (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1) → ℂ) → Prop :=
      fun k err errLocal => ∀ center z, ∃ j, errLocal (center, z) =
        𝔼 t ∈ slices k z j, err (physical z t) * tests k z j t
    ∃ models : ∀ k, Branch k → CenteredForecastModel (integerBox N),
      (∀ k branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
        (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
        (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
        (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models k branch)) ∧
      PreparedCenteredStagedModelProductiveGoodConclusion (m := m) (nX := nX) (M := M)
        prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
        physical slices tests models Eres := by
  classical
  intro tests commonBudget Qmodel native localSeminorm selectedLocal
  obtain ⟨models, hmodels, hlocal⟩ := exists_preparedFiniteScheduleActualDegreeModelFamily
    (m := m) (nX := nX) (R := R) (σ := σ)
    (Path := bases × rectangularWeightIndices 0 width 1)
    (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
    (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N Pdetect μ poly hbox law hweight physical
    degree u p cap sliceLog testLog budget E hModel
    Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hSlices hDense hnum hcomplex hcap
    Pnative massLog capLog Edata data hNative hAccuracy hCap hPrecision input hinput
  refine ⟨models, hmodels, ?_⟩
  let sides := Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value) (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)
  let Sites := integerBox sides
  let : Nonempty Sites := by
    have hpos (k : LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : 0 < sides k := by
      cases k with
      | inl g => exact S.positive
      | inr a => exact allocatedPrincipalSides_pos (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S a
    let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
    exact (integerBox_nonempty sides).to_subtype
  have hsliceBounds (k) := preparedCenteredForecast_slice_family_bounds (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
    (slices k) (hDense k)
  have htests (k) (z) (j) (t : Sites) : ‖tests k z j t‖ ≤ 1 :=
    preparedCenteredForecast_niltest_star_eval_bound (Vdetect k z j) (hcap k z j)
      (commonStrideIndex (cdetect k z j) (stepdetect k z j) t.val)
  exact preparedCenteredStagedModelProductiveGood (m := m) (nX := nX) (M := M)
    prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
    hweight hgood hproductive htest hgain hmean physical slices tests
    (fun k => (hsliceBounds k).1) (fun k => (hsliceBounds k).2) htests
    models u Bbranch Eres hlocal hBranch hStageCount hErrorBudget

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
variable {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hbox : (integerBox N).Nonempty)
variable (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
variable (hweight : ∀ z, Measurable (fun center => (law center).weight z))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "Sites" => integerBox sides

theorem preparedFiniteScheduleDegreeModelsAtLaw_universal_actualData
    (physical : Path → Sites → integerBox N)
    (degree : ℕ) (u p cap sliceLog testLog budget E : ℝ)
    (hModel : PreparedFiniteScheduleDegreeModelsAtLaw B U b S N Pdetect μ poly hbox law hweight
      physical degree u p cap sliceLog testLog budget E)
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L degree d)
    (hSides : ∀ i, 0 < sides i) (hSliceLog : 0 ≤ sliceLog)
    (hDetectorBudget : 1 ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    (hGeometry : D.GeometryComplexityLE (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog))
    (hnum : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    {Forecast : Type} [Nonempty Forecast] {Pnative massLog capLog Edata : ℝ}
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (hNative : 0 ≤ Pnative)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hCap : Real.exp capLog ≤ cap)
    (hPrecision : actualForecastDataModelRequired budget Pnative massLog u p ≤ E)
    {Branch : Type} [Fintype Branch]
    (input : Branch → integerBox N → ℂ)
    (hinput : ∀ branch v, ‖input branch v‖ ≤ Real.exp p) :
    let Packet := LocalMajorSliceTest D sides sliceLog (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog)
    let commonBudget := max budget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : Fin nX → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : (integerBox N → ℂ) → ℝ :=
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical
        (fun _ (j : Packet) => j.slice.subtypeSites)
        (fun _ (j : Packet) t => j.weight t.val)
    let selectedLocal : (integerBox N → ℂ) →
      (CoefficientTorus (K := LayerSamplerVariables G I n B) U × Path → ℂ) → Prop :=
      fun err errLocal => ∀ center z, ∃ j : Packet, errLocal (center, z) =
        𝔼 t ∈ j.slice.subtypeSites, err (physical z t) * j.weight t.val
    ∃ models : Branch → CenteredForecastModel (integerBox N),
      ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        native (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) (fun f => (data f).target)
        localSeminorm selectedLocal (input branch) (Real.exp (Qmodel + 2))
        (Real.exp (-u)) (Real.exp (2 * Qmodel + 2 * u + 4 * p + 34)) (models branch) := by
  classical
  intro Packet commonBudget Qmodel native localSeminorm selectedLocal
  let : Nonempty Packet := LocalMajorSliceTest.nonempty D sides hSides sliceLog
    (Pdetect.eval₂ (Nat.castRingHom ℝ) testLog) hSliceLog hDetectorBudget hGeometry
  exact preparedFiniteScheduleDegreeModelsAtLaw_actualData
    (B := B) (U := U) (b := b) (S := S)
    N Pdetect μ poly hbox law hweight physical degree u p cap sliceLog testLog budget E hModel
    (Tests := fun _ => Packet) (Ldetect := fun _ _ => L) (dims := fun _ _ => d)
    (fun _ _ => D) (fun _ j => j.test) (fun _ j => j.slice.subtypeSites)
    (fun _ j i => (j.slice.start i : ℤ)) (fun _ j => j.stride) (fun _ j => j.slice.length)
    (fun _ j => j.stride_pos)
    (fun _ j => j.slice.subtypeSites_image_val.trans j.slice.integerPoints_eq_commonStrideBox)
    (fun _ j => j.slice.subtypeSites_dense j.dense) hnum
    (fun _ j => j.complexity) (fun _ j => j.norm)
    data hNative hAccuracy hCap hPrecision input hinput

end Erdos3.VectorPolynomial

end

end OAI
