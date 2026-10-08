/- Modified for ProveIt: provide the factor, row-product, and full-product
SigmaFinite instances, plus the proved covered-chart OpensMeasurableSpace
instance, explicitly in coefficientCoveredDensity_global to avoid Lean 4.32
instance-search timeouts. Theorem statements are unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.MixedCoveredChartCompact
import OAI.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (pivot : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
  id (pivot j)).det ≠ 0)
variable (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩo : ∀ j t, IsOpen (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
variable (hw : ∀ j i e, 0 < w j i e)
variable (hs : ∀ j x, mixedArraySupported (c j) (w j) (p j) x → ∀ t,
  normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
      (mixedArrayIntegerImage (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) x) t)) ∈ Ω j t)

include hΩo hΩ hw hs in
theorem canonicalCoefficientDeckSample_density_pointwise
    (g : EuclideanJetLayers U O → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    (hlaw : ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun x => euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2)) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) g)
    (x : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)))
    (hx : mixedCoveredJetCoordinates U o d x ∈ coveredJetSourceRegion U b d Ω) :
    g (coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d x)) =
      canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d x := by
  let e := mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d
  let density := canonicalCoveredArrayDensity (B := B) U root A rows pivot hpivot c w p d
  let S := coveredJetSourceRegion (B := B) U b d Ω
  have hS : IsOpen S := coveredJetSourceRegion_isOpen U b d Ω hΩo
  have hmeas (j) (t) := (hΩo j t).measurableSet
  have hlaw' := canonicalCoefficientDeckSample_haar_density U root A rows pivot hpivot c w p
    o b d Ω hb bW ν hw hmeas hΩ hs
  have hrestriction :
      restrictedChartDensity (coveredJetChart U b hb bW d) S 1
        (fun y => canonicalSupportedArrayDensity U root A rows pivot hpivot c w p o b d Ω (e.symm y)) =
      restrictedChartDensity (coveredJetChart U b hb bW d) S 1 (density ∘ e.symm) := by
    unfold restrictedChartDensity
    congr 1
    funext y
    apply Set.indicator_of_mem
    change e (e.symm y.val) ∈ S
    simpa only [MeasurableEquiv.apply_symm_apply] using y.property
  have hmeasure : realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) g =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
        (restrictedChartDensity (coveredJetChart U b hb bW d) S 1 (density ∘ e.symm)) := by
    rw [← hrestriction]
    exact hlaw.symm.trans hlaw'
  have hd : Continuous density := canonicalCoveredArrayDensity_continuous root A rows pivot hpivot c w hw p U d
  have hd0 (z) : 0 ≤ density z :=
    div_nonneg (mul_nonneg (canonicalCoefficientJetImageDensity_nonneg root A rows pivot hpivot c w hw p z.1)
      (coefficientDeckJetDensity_nonneg root A rows d z.2)) (coveredJetArrayScale_pos U).le
  let : (coveredJetReference (O := O) (B := B) (n := n) U d).IsOpenPosMeasure :=
    coveredJetReference_isOpenPosMeasure U d
  have he := continuousDensity_open_chart (coveredJetReference U d)
    (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
    (coveredJetChart U b hb bW d) (coveredJetChart_continuous U b hb bW d) hS
    (coveredJetChart_embedding U b hb bW d Ω hmeas hΩ)
    (coveredJetChart_reference_map U b hb bW d ν Ω hmeas hΩ)
    (density ∘ e.symm) (hd.comp (mixedCoveredJetEquiv_symm_continuous U o d))
    (fun z => hd0 _) g hg hg0 hmeasure (show e x ∈ S from hx)
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] at he
  simpa only [e, mixedCoveredJetEquiv_apply, density] using he

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

include hΩo hΩ hw hs in
theorem coefficientCoveredDensity_pointwise
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (hinput : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (g : EuclideanJetLayers U O → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    (hlaw : (realDensityMeasure μ (fun y => canonicalCoefficientDensity U b hb o c w p
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))).map
      (euclideanCoefficientJetMap U root A rows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) g)
    (x : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)))
    (hx : mixedCoveredJetCoordinates U o d x ∈ coveredJetSourceRegion U b d Ω) :
    g (coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d x)) =
      canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d x := by
  apply canonicalCoefficientDeckSample_density_pointwise U root A rows pivot hpivot c w p o b hb bW d ν
    Ω hΩo hΩ hw hs g hg hg0 _ x hx
  change ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
    (euclideanCoefficientJetMap U root A rows ∘
      fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
        canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) = _
  rw [← Measure.map_map (euclideanCoefficientJetMap_continuous U root A rows).measurable
    (canonicalCoefficientDeckSample_measurable U bW b hb o d),
    canonicalCoefficientDeckSample_law U bW b hb o μ ν c w p hw hinput d]
  exact hlaw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

theorem euclideanJetHaar_isOpenPosMeasure {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))).IsOpenPosMeasure := by
  let : ∀ j, CompactSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun j => latticeQuotient_compact _
  let : ∀ j, (ν j).IsOpenPosMeasure := fun j =>
    isOpenPosMeasure_of_addLeftInvariant_of_compact (μ := ν j) Set.univ isCompact_univ (by simp)
  let : ∀ j, SigmaFinite (ν j) := fun j => inferInstance
  let : ∀ j, (Measure.pi (fun _ : O j => ν j)).IsOpenPosMeasure := fun j => inferInstance
  let : ∀ j, SigmaFinite (Measure.pi (fun _ : O j => ν j)) := fun j => inferInstance
  infer_instance

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (pivot : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
  id (pivot j)).det ≠ 0)
variable (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coefficientCoveredDensity_global
    (Ψ Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΨ : ∀ j t, IsCompact (Ψ j t)) (hΩo : ∀ j t, IsOpen (Ω j t))
    (hΨΩ : ∀ j t, Ψ j t ⊆ Ω j t) (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (hw : ∀ j i e, 0 < w j i e)
    (hinput : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (hs : ∀ j x, mixedArraySupported (c j) (w j) (p j) x → ∀ t,
      normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (mixedArrayIntegerImage (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) x) t)) ∈ Ψ j t)
    (g : EuclideanJetLayers U O → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    (hlaw : (realDensityMeasure μ (fun y => canonicalCoefficientDensity U b hb o c w p
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))).map
      (euclideanCoefficientJetMap U root A rows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) g) :
    (∀ x, mixedCoveredJetCoordinates U o d x ∈ coveredJetSourceRegion U b d Ω →
      g (coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d x)) =
        canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d x) ∧
    (∀ z ∉ coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ψ, g z = 0) := by
  constructor
  · exact fun x hx => coefficientCoveredDensity_pointwise U root A rows pivot hpivot c w p o b hb bW d ν
      Ω hΩo hΩ hw (fun j a ha t => hΨΩ j t (hs j a ha t)) μ hinput g hg hg0 hlaw x hx
  · let ξ := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
    let : ∀ j, SigmaFinite (ν j) := fun j => inferInstance
    let : ∀ j, SigmaFinite (Measure.pi (fun _ : O j => ν j)) :=
      fun j => Measure.pi.sigmaFinite _
    let : SigmaFinite ξ := Measure.pi.sigmaFinite _
    let : OpensMeasurableSpace (CoveredJetChartSource U O B n d) :=
      @BorelSpace.opensMeasurable _ _ _ (coveredJetChartSource_borel U d)
    let S := coveredJetSourceRegion (B := B) U b d Ψ
    let q := coveredJetChart (O := O) U b hb bW d
    let density := canonicalCoveredArrayDensity (B := B) U root A rows pivot hpivot c w p d
    let : ξ.IsOpenPosMeasure := euclideanJetHaar_isOpenPosMeasure U ν
    have hcompact : IsCompact (q '' S) :=
      (coveredJetSourceRegion_isCompact U b d Ψ hΨ).image (coveredJetChart_continuous U b hb bW d)
    have hdeck : ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
        (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
        (fun x => euclideanCoefficientJetMap U root A rows
          (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2)) =
        realDensityMeasure ξ g := by
      change ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
        (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
        (euclideanCoefficientJetMap U root A rows ∘
          fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
            canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) = _
      rw [← Measure.map_map (euclideanCoefficientJetMap_continuous U root A rows).measurable
        (canonicalCoefficientDeckSample_measurable U bW b hb o d),
        canonicalCoefficientDeckSample_law U bW b hb o μ ν c w p hw hinput d]
      exact hlaw
    have harray : realDensityMeasure ξ g =
        (realDensityMeasure (coveredJetArrayReference U d) density).map
          (fun x => q (mixedCoveredJetCoordinates U o d x)) :=
      hdeck.symm.trans (canonicalCoefficientDeckSample_array_density U root A rows pivot hpivot c w p o b hb bW hw d)
    apply continuousDensity_zero_off_closed ξ g hg hg0 hcompact.isClosed
    rw [harray]
    apply (ae_map_iff ((coveredJetChart_continuous U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable U o d)).aemeasurable hcompact.isClosed.measurableSet).mpr
    filter_upwards [canonicalCoveredArrayDensity_support U root A rows pivot hpivot c w p o b d Ψ
      hw (fun j t => (hΨ j t).isClosed.measurableSet) hs] with x hx
    exact ⟨mixedCoveredJetCoordinates U o d x, hx, rfl⟩

end Erdos3.VectorPolynomial

end

end OAI
