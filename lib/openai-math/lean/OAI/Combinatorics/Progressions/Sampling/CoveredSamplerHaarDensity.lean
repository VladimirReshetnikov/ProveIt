/- Modified for ProveIt: supply explicit product-measure finiteness and
chart-source open-set measurability instances on Lean 4.32;
theorem statements and bounds are unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.MixedArrayImageSupport
import OAI.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors
import OAI.Combinatorics.Progressions.Probability.MixedCoveredDensityMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (pivot : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
  id (pivot j)).det ≠ 0)
variable (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def canonicalCoveredArrayDensity (d : ℕ) [NeZero d]
    (x : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) : ℝ :=
  (canonicalCoefficientJetImageDensity root A rows pivot hpivot c w p x.1 *
    coefficientDeckJetDensity root A rows d x.2) / coveredJetArrayScale (O := O) U

theorem canonicalCoveredArrayDensity_law (hw : ∀ j i e, 0 < w j i e) (d : ℕ) [NeZero d] :
    ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun x => (canonicalCoefficientJetArrays root A rows x.1,
        coefficientDeckJetMap root A rows d x.2)) =
    realDensityMeasure (coveredJetArrayReference U d)
      (canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d) := by
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (c j) (w j) (p j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  let : IsProbabilityMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    Measure.pi.instIsProbabilityMeasure _
  let : IsFiniteMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) := by
    constructor
    rw [measure_univ]
    exact ENNReal.one_lt_top
  let : SigmaFinite (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    IsFiniteMeasure.toSigmaFinite _
  let : SFinite (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) := inferInstance
  have hF := canonicalCoefficientJetArrays_measurable (I := I) (n := n) root A rows
  have hR : Measurable (coefficientDeckJetMap (B := B) root A rows d) := measurable_of_finite _
  change Measure.map (Prod.map (canonicalCoefficientJetArrays root A rows)
    (coefficientDeckJetMap root A rows d)) _ = _
  rw [← Measure.map_prod_map _ _ hF hR,
    canonicalCoefficientJetImageDensity_law root A rows pivot hpivot c w hw p,
    PMF.toMeasure_map _ _ hR, coefficientDeckJetDensity_law]
  rw [binaryDensity_measure _ _ _ _
    (canonicalCoefficientJetImageDensity_measurable root A rows pivot hpivot c w p)
    (measurable_of_finite _)
    (canonicalCoefficientJetImageDensity_nonneg root A rows pivot hpivot c w hw p)]
  exact (coveredJetArrayReference_density U d _).symm

theorem canonicalCoefficientDeckSample_array_density [Fintype α]
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hw : ∀ j i e, 0 < w j i e) (d : ℕ) [NeZero d] :
    ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun x => euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2)) =
    (realDensityMeasure (coveredJetArrayReference U d)
      (canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d)).map
        (fun x => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d x)) := by
  let : OpensMeasurableSpace (CoveredJetChartSource U O B n d) :=
    @BorelSpace.opensMeasurable _ _ _ (coveredJetChartSource_borel U d)
  have hF := canonicalCoefficientJetArrays_measurable (I := I) (n := n) root A rows
  have hR : Measurable (coefficientDeckJetMap (B := B) root A rows d) := measurable_of_finite _
  have hq : Measurable (fun x => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d x)) :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := B) (n := n) U o d)
  have hpair : Measurable (fun x : CoefficientSamplerArrays (K := K) I n ×
      CoefficientDeckResidues (K := K) B d =>
      (canonicalCoefficientJetArrays root A rows x.1, coefficientDeckJetMap root A rows d x.2)) :=
    hF.prodMap hR
  rw [← canonicalCoveredArrayDensity_law U root A rows pivot hpivot c w p hw d,
    Measure.map_map hq hpair]
  congr 1
  funext x
  exact canonicalCoefficientDeckSample_chart U o root A rows b hb bW d x.1 x.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
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
variable (d : ℕ) [NeZero d] (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

noncomputable def canonicalSupportedArrayDensity :
    ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ :=
  (mixedCoveredJetCoordinates U o d ⁻¹' coveredJetSourceRegion U b d Ω).indicator
    (canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d)

theorem canonicalCoveredArrayDensity_support (hw : ∀ j i e, 0 < w j i e)
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hs : ∀ j x, mixedArraySupported (c j) (w j) (p j) x → ∀ t,
      normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (mixedArrayIntegerImage (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) x) t)) ∈ Ω j t) :
    ∀ᵐ x ∂realDensityMeasure (coveredJetArrayReference (B := B) U d)
      (canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d),
      mixedCoveredJetCoordinates U o d x ∈ coveredJetSourceRegion U b d Ω := by
  let μ := fun j => mixedScalarArrayLaw (c j) (w j) (p j)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  have hinput : ∀ᵐ x ∂Measure.pi μ, ∀ j, mixedArraySupported (c j) (w j) (p j) (x j) :=
    ae_all_iff.mpr (fun j => (Measure.quasiMeasurePreserving_eval μ j).ae
      (mixedScalarArrayLaw_support (c j) (w j) (hw j) (p j)))
  rw [← canonicalCoveredArrayDensity_law U root A rows pivot hpivot c w p hw d]
  have hF := canonicalCoefficientJetArrays_measurable (I := I) (n := n) root A rows
  have hR : Measurable (coefficientDeckJetMap (B := B) root A rows d) := measurable_of_finite _
  have hpair : Measurable (fun x : CoefficientSamplerArrays (K := K) I n ×
      CoefficientDeckResidues (K := K) B d =>
      (canonicalCoefficientJetArrays root A rows x.1, coefficientDeckJetMap root A rows d x.2)) :=
    hF.prodMap hR
  have hS := (coveredJetSourceRegion_measurable U b d Ω hΩm).preimage
    (mixedCoveredJetCoordinates_measurable (O := O) (B := B) (n := n) U o d)
  apply (ae_map_iff hpair.aemeasurable hS).mpr
  have hall : ∀ᵐ x ∂(Measure.pi μ).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure,
      ∀ j, mixedArraySupported (c j) (w j) (p j) (x.1 j) :=
    Measure.quasiMeasurePreserving_fst.ae hinput
  filter_upwards [hall] with x hx
  intro j _ t _
  exact ⟨hs j (x.1 j) (hx j) t, Set.mem_univ _⟩

theorem canonicalCoefficientDeckSample_haar_density [Fintype α]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hw : ∀ j i e, 0 < w j i e) (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (hs : ∀ j x, mixedArraySupported (c j) (w j) (p j) x → ∀ t,
      normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (mixedArrayIntegerImage (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) x) t)) ∈ Ω j t) :
    ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun x => euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2)) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun y => canonicalSupportedArrayDensity U root A rows pivot hpivot c w p o b d Ω
          ((mixedCoveredJetEquiv U o d).symm y))) := by
  have hS := (coveredJetSourceRegion_measurable U b d Ω hΩm).preimage
    (mixedCoveredJetCoordinates_measurable (O := O) (B := B) (n := n) U o d)
  have hrestrict := realDensityMeasure_eq_indicator_of_ae (coveredJetArrayReference U d)
    (canonicalCoveredArrayDensity U root A rows pivot hpivot c w p d) hS
    (canonicalCoveredArrayDensity_support U root A rows pivot hpivot c w p o b d Ω hw hΩm hs)
  rw [canonicalCoefficientDeckSample_array_density U root A rows pivot hpivot c w p o b hb bW hw d,
    hrestrict]
  apply coveredJetArray_density_law U o b hb bW d ν Ω hΩm hΩ
  intro x hx
  apply Set.indicator_of_notMem
  exact hx

end Erdos3.VectorPolynomial

end

end OAI
