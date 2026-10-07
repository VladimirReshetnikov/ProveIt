import OAI.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison
import OAI.Combinatorics.Progressions.Sampling.ForecastNativeRawSpatialFamily
import OAI.Combinatorics.Progressions.Sampling.ForecastShortGridEquiv

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*}
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem forecastJointNativeResidue_eq_axis [Fintype X]
    [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] (L : ℕ) (hm : 0 < m) {A : Type*}
    (deck : ∀ j, E j → A) (r : X ⊕ AllocatedActiveIntegerAxis U basis L → A) :
    forecastJointNativeResidue (I := I) U basis L deck r =
      fun a => Sum.elim (fun a : Σ j, E j => deck a.1 a.2) r
        (forecastCongruenceJointAxisEquiv (I := I) U basis L hm a) := by
  funext a
  rcases a with ⟨j, x | e | i⟩ <;> rfl

variable [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]

private theorem zmodReduction_val {N q : ℕ} [NeZero N] (hq : q ∣ N) (r : ZMod N) :
    (((r.val : ℤ) : ZMod q)) = ZMod.castHom hq (ZMod q) r := by
  rw [Int.cast_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val r]
  rw [map_natCast]

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Short" => AllocatedShortIntegerAxis U basis S.value
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Domain" => ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit) → ℝ)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

 theorem forecastNativeJointRawIntegrand
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : τ ≠ 0)
    (v : (Σ j, I j) → ℝ) (ks : Short → ℤ)
    (k : X ⊕ IntAxis → ℤ) (deck : ForecastSingleDeckResidues E N) :
    let u : X → ℤ := fun x => k (.inl x)
    let ka : IntAxis → ℤ := fun a => k (.inr a)
    let z := forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
      (forecastIntegerAxisMerge U basis S.value ks ka) deck
    let y := forecastJointCoordinateJoin U basis S.value v
      (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
        forecastJointGridScale U basis R S.value physicalN τ j)
    let axis := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
    forecastDensityPhysicalChartSource B U basis S density selected sample x
      active Y N gridVolume base physicalN τ u z *
        nativeSingleSiteCoverObservable U W physicalN u N
          (mixedCoveredJetChart U o basis hb bW N z) =
      (density y : ℂ) *
      (rationalInactiveForecast law active
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        Y N gridVolume (fun a _ => ks a)
        (fun a => Sum.elim (fun e : Σ j, E j => deck e.1 () e.2)
          (fun j => (k j : ZMod N)) (axis a)) : ℂ) *
      W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
        (fun x => (base x : ℝ) / physicalN x) τ (fun a _ => ks a)
        (fun a => Sum.elim (zmodPiReduction hq (fun e : Σ j, E j => deck e.1 () e.2))
          (fun j => (k j : ZMod q)) (axis a)) y := by
  dsimp only
  let u : X → ℤ := fun x => k (.inl x)
  let ka : IntAxis → ℤ := fun a => k (.inr a)
  have hk : Sum.elim u ka = k := by funext a; cases a <;> rfl
  have hy : forecastJointCoordinateJoin U basis S.value v
      (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
        forecastJointGridScale U basis R S.value physicalN τ j) =
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastActiveCoordinateJoin U basis S.value v
          (fun a => (ka a : ℝ) / allocatedActiveIntegerGridScale U basis R S.value a)) := by
    rw [← hk, forecastJointGrid_normalized_join]
    rfl
  rw [hy, forecastDensityPhysicalChartSource_normalized_raw_point B U basis S density selected
    sample x active Y N gridVolume base physicalN τ hR (fun a => a.property)]
  rw [W.nativeSingleSiteCoverObservable_normalized_raw_point U basis hb o bW S.value R
    (fun j => (hR j).ne') q hm hperiod hcover base u physicalN hN hτ N
    (dvd_trans hcover hq)]
  have hres (p : ℕ) :
      (fun a => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (fun i => forecastIntegerAxisMerge U basis S.value ks ka ⟨j, i⟩)
          (fun i => ((deck j () i).val : ℤ))) a : ZMod p)) =
      fun a => Sum.elim (fun e : Σ j, E j => (((deck e.1 () e.2).val : ℤ) : ZMod p))
        (fun j => (k j : ZMod p))
        (forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm a) := by
    rw [← forecastJointNativeResidue_integer, forecastJointNativeResidue_eq_axis U basis _ hm]
    funext a
    rcases a with ⟨j, x | e | i⟩ <;> rfl
  rw [hres, forecastJointNativeResidue_eq_axis U basis _ hm]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  congr 2
  funext a
  rcases a with ⟨j, a | e | i⟩
  · rfl
  · change ((deck j () e).val : ZMod q) = ZMod.castHom hq (ZMod q) (deck j () e)
    simpa only [Int.cast_natCast] using zmodReduction_val hq (deck j () e)
  · rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Short" => AllocatedShortIntegerAxis U basis S.value
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Domain" => ((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit) → ℝ)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "raw" => mixedCoveredJetRawReference (I := I) (O := fun _ : Fin m => Unit) (E := E) (n := n) N
local notation "source" => forecastDensityPhysicalChartSource B U basis S density selected sample x active Y N gridVolume base physicalN τ
local notation "chart" => mixedCoveredJetChart (O := fun _ : Fin m => Unit) U o basis hb bW N

private theorem forecastNativeJointSum
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : τ ≠ 0)
    (aux : (Σ j, E j) → ZMod N) (v : (Σ j, I j) → ℝ) :
    (∑' ks : Short → ℤ, ∑' k : X ⊕ IntAxis → ℤ,
      let u := fun x => k (.inl x)
      let z := forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
        (forecastIntegerAxisMerge U basis S.value ks (fun a => k (.inr a)))
        (fun j _ e => aux ⟨j, e⟩)
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)) =
    ∑' grid : Short → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ,
    ∑' k : X ⊕ IntAxis → ℤ,
      let y := forecastJointCoordinateJoin U basis S.value v
        (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
          forecastJointGridScale U basis R S.value physicalN τ j)
      let axis := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
      (density y : ℂ) *
        (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N gridVolume grid (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axis a)) : ℂ) *
        W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun x => (base x : ℝ) / physicalN x) τ grid
          (fun a => Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)) (axis a)) y
 := by
  let f := fun (grid : Short → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) =>
    ∑' k : X ⊕ IntAxis → ℤ,
      let y := forecastJointCoordinateJoin U basis S.value v
        (fun j => ((k j : ℝ) - forecastJointGridCenter U basis S.value base j) /
          forecastJointGridScale U basis R S.value physicalN τ j)
      let axis := forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis S.value hm
      (density y : ℂ) *
        (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N gridVolume grid (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axis a)) : ℂ) *
        W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
          (fun x => (base x : ℝ) / physicalN x) τ grid
          (fun a => Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)) (axis a)) y
  calc
    _ = ∑' ks : Short → ℤ, f (fun a _ => ks a) := by
      apply tsum_congr
      intro ks
      apply tsum_congr
      intro k
      exact forecastNativeJointRawIntegrand U basis B S density sample x active Y N gridVolume
        base physicalN τ hb o bW W hR q hq hm hperiod hcover hN hτ v ks k
          (fun j _ e => aux ⟨j, e⟩)
    _ = ∑' grid, f grid := forecastShortGrid_tsum f

theorem forecastNativeRawSum_eq_jointMean
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hN : ∀ x, 0 < physicalN x) (hτ : 0 < τ) (hV : gridVolume ≠ 0)
    (hf : ∀ u ∈ integerBox physicalN,
      Integrable (fun z => source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)) raw)
    (hzero : ∀ u ∉ integerBox physicalN, ∀ z,
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z) = 0) :
    (∑ u ∈ integerBox physicalN, ∫ z,
      source u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z) ∂raw) =
    ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) *
      ((gridVolume : ℂ) * ((∏ j, forecastJointGridScale U basis R S.value physicalN τ j : ℝ) : ℂ) *
        forecastJointOriginalGridMean U basis S.value hm law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N q hq gridVolume density
          (W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun x => (base x : ℝ) / physicalN x) τ)
          (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
          (forecastJointGridScale U basis R S.value physicalN τ)) := by
  rw [forecastRawSpatialBox_normalized_integral I E N U basis S.value X R hR _ _ hf hzero]
  congr 1
  rw [forecastSingleDeckAverage E N]
  rw [forecastJointOriginalGridMean_mul_normalization U basis S.value hm law active _ Y N q hq
    gridVolume density _ _ _ hV
    (fun j => (forecastJointGridScale_pos U basis hR S.value physicalN hN hτ j).ne')]
  apply Finset.expect_congr rfl
  intro aux haux
  apply integral_congr_ae
  refine ae_of_all _ (fun v => ?_)
  exact forecastNativeJointSum U basis B S density sample x active Y N gridVolume
    base physicalN τ hb o bW W hR q hq hm hperiod hcover hN hτ.ne' aux v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N
local notation "RawSource" => MixedCoveredJetSource I single Eout n N

variable [DecidableEq X]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem forecastNativeHaarMean_eq_jointMean
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hdensity : Continuous density)
    (hsupport : ∀ y, 2 < ‖y‖ → density y = 0)
    (hN : ∀ i, 0 < physicalN i) (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : Wtest.modulus ∣ q) (hcover : Wtest.cover ∣ q) (hV : 0 < volume) :
    (forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ) *
      (𝔼 u ∈ integerBox physicalN,
        ∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U Wtest physicalN u N y ∂haar) =
        forecastJointOriginalGridMean U basis S.value hm law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N q hq volume density
          (Wtest.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun x => (base x : ℝ) / physicalN x) τ)
          (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
          (forecastJointGridScale U basis R S.value physicalN τ) := by
  have hbox : @integerBox X inferInstance (Classical.decEq X) physicalN = integerBox physicalN := by
    ext u
    simp only [mem_integerBox]
  have hnorm (y) (hy : density y ≠ 0) : ‖y‖ ≤ 2 :=
    le_of_not_gt (fun h => hy (hsupport y h))
  have hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3 := by
    intro y hy a
    have hc : |y.2 a| ≤ ‖y.2‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.2 a
    exact (hc.trans ((le_max_right ‖y.1‖ ‖y.2‖).trans (hnorm y hy))).trans (by norm_num)
  have hspatial : ∀ y, density y ≠ 0 → ∀ i : X, |y.1 ⟨i, .inl ()⟩| ≤ 2 := by
    intro y hy i
    have hc : |y.1 ⟨i, .inl ()⟩| ≤ ‖y.1‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.1 ⟨i, .inl ()⟩
    exact hc.trans ((le_max_left ‖y.1‖ ‖y.2‖).trans (hnorm y hy))
  have hf (u : X → ℤ) : Integrable (fun z => chartSource u z *
      nativeSingleSiteCoverObservable U Wtest physicalN u N (chart z)) raw :=
    forecastNativeRawSpatialFamily_integrable B U basis S density sample x active Y N volume
      base physicalN τ o hb bW Wtest hR hσ hs hσ1 hactive r hr hr3 hradius
      C hC hchart hbudget hdensity u
  have hzero (u : X → ℤ) (hu : u ∉ integerBox physicalN) (z : RawSource) :
      chartSource u z * nativeSingleSiteCoverObservable U Wtest physicalN u N (chart z) = 0 := by
    unfold forecastDensityPhysicalChartSource forecastDensityPhysicalDeckSource
    rw [translatedForecastDensity_zero_outside_integerBox density hspatial physicalN hN hτ
      hmargin base hbase u _ hu, Complex.ofReal_zero, zero_mul, zero_mul]
  have hhaar := forecastNativeHaarMean_eq_rawSum B U basis S density sample x active Y N volume
    base physicalN τ o Wtest hR hσ hs hσ1 hactive r hr hr3 hradius C hC hchart hbudget
    hb bW ν hdensity
    (forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ)
  have hraw := forecastNativeRawSum_eq_jointMean U basis B S density sample x active Y N volume
    base physicalN τ hb o bW Wtest hR q hq hm hperiod hcover hN hτ hV.ne'
    (fun u _ => hf u) (fun u hu z => hzero u (by simpa only [hbox] using hu) z)
  simpa only [hbox] using hhaar.trans (forecastNativeRawMean_normalization (B := B) (U := U) (basis := basis) (S := S)
    (volume := volume) (physicalN := physicalN) (τ := τ) hR hN hV hτ _ _ hraw)

end Erdos3.VectorPolynomial

end

end OAI
