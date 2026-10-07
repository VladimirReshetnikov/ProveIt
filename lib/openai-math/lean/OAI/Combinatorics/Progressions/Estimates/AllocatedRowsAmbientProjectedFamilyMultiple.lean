/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Fourier.NormalizedTwistSingleSiteFourierHaar
import OAI.Combinatorics.Progressions.Probability.AllocatedAmbientProjectedDensityMultiple
import OAI.Combinatorics.Progressions.Probability.PhysicalRowsDensityTransport

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_mean_coefficient_unit_expansion
    {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → CoefficientTorus (K := K) U → ℝ) (C L : ℝ≥0) {δ : ℝ}
    (h : ∀ y, ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
        (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ L) ∧
        (∑ a, ‖coeff a‖) ≤ C ∧
        ∀ z, ‖(g y z : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ) :
    ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (coeff : F → ℂ) (factor : F → (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ),
        (∑ a, ‖coeff a‖) ≤ C ∧
        (∀ a, LipschitzWith (Fintype.card (CoefficientAmbientIndex K J) *
          (CircleFourier.characterLipConstant * L)) (factor a)) ∧
        (∀ a z, ‖factor a z‖ ≤ 1) ∧
        ∀ z, ‖(law.mean (fun y => g y z) : ℂ) -
          ∑ a, coeff a * factor a (coefficientAmbientTorus U z)‖ ≤ δ := by
  obtain ⟨F, inst, freq, coeff, hf, hc, happ⟩ := exists_coefficientFourierMixture U law g h
  let _ := inst
  let factor := fun a => ambientIntegerCharacter (fun t : CoefficientAmbientIndex K J =>
    freq a t.1.1 t.1.2.val t.2)
  refine ⟨F, inst, coeff, factor, hc, ?_, ?_, ?_⟩
  · intro a
    exact ambientIntegerCharacter_lipschitz _ L (fun t => hf a t.1.1 t.1.2.val t.1.2.property t.2)
  · intro a z
    exact (ambientIntegerCharacter_norm _ z).le
  · intro z
    have he := coefficientFourierAmbient_eq U freq coeff z
    change (∑ a, coeff a * factor a (coefficientAmbientTorus U z)) = _ at he
    rw [he]
    exact happ z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
variable (g : Y → EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)

noncomputable def physicalRowsProjectedMean (law : FiniteProbabilityWeights Y) (g : Y → EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ) (y : EuclideanJetLayers U Row) : ℂ :=
  law.complexMean (fun a => (g a (physicalRowsToStandard U y) : ℂ))

theorem physicalRowsProjectedMean_measurable (hg : ∀ a, Measurable (g a)) :
    Measurable (physicalRowsProjectedMean U law g) := by
  unfold physicalRowsProjectedMean FiniteProbabilityWeights.complexMean
  exact Finset.measurable_sum Finset.univ (fun a _ =>
    ((hg a).comp (physicalRowsToStandard_continuous U).measurable).complex_ofReal.const_mul _)

theorem physicalRowsProjectedMean_norm_le {C : ℝ} (hg : ∀ a y, |g a y| ≤ C)
    (y : EuclideanJetLayers U Row) : ‖physicalRowsProjectedMean U law g y‖ ≤ C := by
  apply (law.norm_complexMean_le_mean_norm _).trans
  apply (law.mean_mono (fun a => ?_)).trans_eq (law.mean_const C)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hg a (physicalRowsToStandard U y)

theorem physicalRowsProjectedMean_sample {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j ex, coefficients (p j) ex ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalRowsProjectedMean U law g
      (physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v) =
      law.complexMean (fun a => (g a (physicalCubeEuclideanSample U d p hm v) : ℂ)) := by
  unfold physicalRowsProjectedMean
  rw [physicalRowsToStandard_sample U d p hp hm]

theorem exists_physicalRowsProjectedMean_unit_expansion (C L : ℝ≥0) {δ : ℝ}
    (h : ∀ y, ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (frequency : F → ∀ j, (Fin q →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
        (∀ a j ex, ex.degree ≤ j.val + 1 → ∀ t, |(frequency a j ex t : ℝ)| ≤ L) ∧
        (∑ a, ‖coeff a‖) ≤ C ∧
        ∀ z, ‖(g y (standardPhysicalJetMap U z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ) :
    ∃ (F : Type) (inst : Fintype F), let _ := inst
      ∃ (coeff : F → ℂ) (factor : F → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ),
        (∑ a, ‖coeff a‖) ≤ C ∧
        (∀ a, LipschitzWith (Fintype.card (CoefficientAmbientIndex (Fin q) J) *
          (CircleFourier.characterLipConstant * L)) (factor a)) ∧
        (∀ a z, ‖factor a z‖ ≤ 1) ∧
        ∀ z, ‖physicalRowsProjectedMean U law g
          (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
            (fun j => (Subtype.val : Row j → Finset (Fin q))) z) -
          ∑ a, coeff a * factor a (coefficientAmbientTorus U z)‖ ≤ δ := by
  obtain ⟨F, inst, coeff, factor, hc, hf, hfb, happ⟩ :=
    exists_mean_coefficient_unit_expansion U law (fun y z => g y (standardPhysicalJetMap U z)) C L h
  let _ := inst
  refine ⟨F, inst, coeff, factor, hc, hf, hfb, ?_⟩
  intro z
  unfold physicalRowsProjectedMean
  rw [physicalRowsToStandard_coefficient, FiniteProbabilityWeights.complexMean_ofReal]
  exact happ z

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical BigOperators NNReal

attribute [local irreducible] boundedBooleanJetRows

variable {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
local notation "Row" => (fun j : Fin m =>
  {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
noncomputable local instance (priority := 2000) physicalRowsAmbientFintype (j : Fin m) : Fintype (Row j) :=
  Finset.Subtype.fintype (boundedBooleanJetRows (Fin dim) (j.val + 1))
local notation "Std" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))

noncomputable def physicalRowsAmbientToStandard
    (z : JetAmbientIndex Row J → UnitAddCircle) : JetAmbientIndex Std J → UnitAddCircle :=
  fun a => z ⟨a.1, (boundedBooleanJetRowsEquiv (Fin dim) (a.1.val + 1)).symm a.2.1, a.2.2⟩

theorem physicalRowsAmbientToStandard_lipschitz :
    LipschitzWith 1 (physicalRowsAmbientToStandard (m := m) (dim := dim) (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  exact dist_le_pi_dist z w _

theorem physicalRowsAmbientToStandard_eq (U : ∀ j, Submodule ℝ (J j → ℝ))
    (y : EuclideanJetLayers U Row) :
    physicalRowsAmbientToStandard (coveredJetAmbientTorus U 1 y) =
      coveredJetAmbientTorus U 1 (physicalRowsToStandard U y) := rfl

theorem finiteProbability_ambient_mean
    {Y X A B : Type*} [Fintype Y] [PseudoEMetricSpace A] [PseudoEMetricSpace B]
    (law : FiniteProbabilityWeights Y) (g : Y → X → ℝ) (F : Y → B → ℝ)
    (r : A → B) (q : X → A) {L C : ℝ≥0}
    (hr : LipschitzWith 1 r) (hF : ∀ a, LipschitzWith L (F a))
    (hFb : ∀ a z, F a z ∈ Set.Icc (0 : ℝ) C)
    (hFv : ∀ a x, g a x = F a (r (q x))) :
    ∃ G : A → ℂ, LipschitzWith L G ∧ (∀ z, ‖G z‖ ≤ C) ∧
      ∀ x, law.complexMean (fun a => (g a x : ℂ)) = G (q x) := by
  let R := fun z : A => law.mean (fun a => F a (r z))
  have hR : LipschitzWith L R := by
    apply law.mean_lipschitz_uniform_emetric
    intro a
    simpa only [mul_one, Function.comp_def] using (hF a).comp hr
  have hRb (z : A) : R z ∈ Set.Icc (0 : ℝ) C :=
    ⟨law.mean_nonneg (fun a => (hFb a _).1),
      (law.mean_mono (fun a => (hFb a _).2)).trans_eq (law.mean_const _)⟩
  refine ⟨fun z => (R z : ℂ), ?_, ?_, ?_⟩
  · simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hR
  · intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hRb z).1]
    exact (hRb z).2
  · intro x
    simp only [hFv, law.complexMean_ofReal]
    rfl

theorem exists_physicalRowsProjectedMean_ambient
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U Std → ℝ)
    (F : Y → (JetAmbientIndex Std J → UnitAddCircle) → ℝ)
    {L C : ℝ≥0} (hF : ∀ a, LipschitzWith L (F a))
    (hFb : ∀ a z, F a z ∈ Set.Icc (0 : ℝ) C)
    (hFv : ∀ a y, g a y = F a (coveredJetAmbientTorus U 1 y)) :
    ∃ G : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
      LipschitzWith L G ∧ (∀ z, ‖G z‖ ≤ C) ∧
      ∀ y, physicalRowsProjectedMean U law g y = G (coveredJetAmbientTorus U 1 y) := by
  have he (a : Y) (y : EuclideanJetLayers U Row) :
      g a (physicalRowsToStandard U y) =
        F a (physicalRowsAmbientToStandard (coveredJetAmbientTorus U 1 y)) :=
    (hFv a (physicalRowsToStandard U y)).trans
      (congrArg (F a) (physicalRowsAmbientToStandard_eq U y).symm)
  obtain ⟨G, hG, hGb, hGv⟩ := finiteProbability_ambient_mean
    (X := EuclideanJetLayers U Row)
    (A := JetAmbientIndex Row J → UnitAddCircle)
    (B := JetAmbientIndex Std J → UnitAddCircle)
    law (fun a (y : EuclideanJetLayers U Row) => g a (physicalRowsToStandard U y)) F
    (physicalRowsAmbientToStandard (m := m) (dim := dim) (J := J))
    (coveredJetAmbientTorus (O := Row) U 1)
    physicalRowsAmbientToStandard_lipschitz hF hFb he
  refine ⟨G, ?_, hGb, hGv⟩
  convert hG using 1
  congr 1
  exact Subsingleton.elim _ _

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_rows_ambient_projected_family (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S c x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection U (allocatedPhysicalCubeRoot B U b S c x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      ∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_allocated_ambient_projected_density m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod
  obtain ⟨d, hd, hdb, hcover⟩ := hcover B U b S c x hP hG hc hL hperiod
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    _ _ _ μrows _ _ density cap cover ξ densityLip sectionLip reconstructionLip Row Tuple
  have hex (y : Tuple) := hcover y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  choose g F hgc hgb hgi hgm hglaw hprojection hFb hFl hvalue using hex
  let rowG := fun (y : Tuple) (z : EuclideanJetLayers U Row) => g y (physicalRowsToStandard U z)
  have hpres := physicalRowsToStandard_measurePreserving U μrows ν
  refine ⟨rowG, fun y => (hgc y).comp (physicalRowsToStandard_continuous U),
    fun y z => hgb y _, ?_, ?_, ?_, ?_⟩
  · intro y
    convert hpres.integrable_comp_of_integrable (hgi y) using 1
    congr! (transparency := .reducible)
    dsimp only [ξ]
    congr! (transparency := .reducible)
  · intro y
    exact physicalRows_projected_density_law U μrows ν _ _ _ (g y) (hglaw y)
  · intro y
    exact hprojection y
  · intro law
    obtain ⟨Fmean, hFm, hFmb, hFmv⟩ := exists_physicalRowsProjectedMean_ambient U law g F
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      hFl (by simpa only [NNReal.coe_pow] using hFb) hvalue
    refine ⟨Fmean, ?_, ?_, hFmv⟩
    · exact hFm
    · simpa only [NNReal.coe_pow] using hFmb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_rows_ambient_projected_family_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S c x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection U (allocatedPhysicalCubeRoot B U b S c x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      ∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_allocated_ambient_projected_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hcover⟩ := hcover B U b S c x hP hG hc hL hperiod period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    _ _ _ μrows _ _ density cap cover ξ densityLip sectionLip reconstructionLip Row Tuple
  have hex (y : Tuple) := hcover y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  choose g F hgc hgb hgi hgm hglaw hprojection hFb hFl hvalue using hex
  let rowG := fun (y : Tuple) (z : EuclideanJetLayers U Row) => g y (physicalRowsToStandard U z)
  have hpres := physicalRowsToStandard_measurePreserving U μrows ν
  refine ⟨rowG, fun y => (hgc y).comp (physicalRowsToStandard_continuous U),
    fun y z => hgb y _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    convert hpres.integrable_comp_of_integrable (hgi y) using 1
    congr! (transparency := .reducible)
    dsimp only [ξ]
    congr! (transparency := .reducible)
  · intro y
    have he := hpres.integral_comp (physicalRowsStandardEquiv U).measurableEmbedding (g y)
    convert he.trans (hgm y) using 1
    congr! (transparency := .reducible)
  · intro y
    exact physicalRows_projected_density_law U μrows ν _ _ _ (g y) (hglaw y)
  · intro y
    exact hprojection y
  · intro y
    let pointLaw := FiniteProbabilityWeights.pointWeights y
    obtain ⟨Fmean, hFm, hFmb, hFmv⟩ := exists_physicalRowsProjectedMean_ambient U pointLaw g F
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      hFl (by simpa only [NNReal.coe_pow] using hFb) hvalue
    refine ⟨Fmean, hFm, ?_, ?_⟩
    · simpa only [NNReal.coe_pow] using hFmb
    · intro z
      simpa only [physicalRowsProjectedMean, pointLaw, FiniteProbabilityWeights.pointWeights_complexMean] using hFmv z
  · intro law
    obtain ⟨Fmean, hFm, hFmb, hFmv⟩ := exists_physicalRowsProjectedMean_ambient U law g F
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      hFl (by simpa only [NNReal.coe_pow] using hFb) hvalue
    refine ⟨Fmean, ?_, ?_, hFmv⟩
    · exact hFm
    · simpa only [NNReal.coe_pow] using hFmb

end Erdos3.VectorPolynomial

end

end OAI
