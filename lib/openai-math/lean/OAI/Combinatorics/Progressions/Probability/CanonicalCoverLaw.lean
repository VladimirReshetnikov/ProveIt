/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged.  Construct mapped probability instances from measurability. -/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OAI.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
import OAI.Combinatorics.Progressions.Estimates.HaarShiftImage
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt
import OAI.Combinatorics.Progressions.Lattices.AffineCubePositiveComparison
import OAI.Combinatorics.Progressions.Linear.CoefficientCoverKernel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientCover_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) :
    MeasurePreserving (quotientIntegerCover (coefficientIntegerLattice U) q) μ μ := by
  have : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (quotientIntegerCover_continuous (coefficientIntegerLattice U) q)
    (quotientIntegerCover_surjective (coefficientIntegerLattice U) q hq) rfl

theorem coefficientCover_integrable {K E : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [NormedAddCommGroup E]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) (f : CoefficientTorus (K := K) U → E) (hf : Integrable f μ) :
    Integrable (fun x => f (quotientIntegerCover (coefficientIntegerLattice U) q x)) μ :=
  (coefficientCover_measurePreserving U μ q hq).integrable_comp_of_integrable hf

theorem coefficientCover_integral {K E : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) (f : CoefficientTorus (K := K) U → E)
    (hf : AEStronglyMeasurable f μ) :
    (∫ x, f (quotientIntegerCover (coefficientIntegerLattice U) q x) ∂μ) = ∫ x, f x ∂μ := by
  have hp := coefficientCover_measurePreserving U μ q hq
  have hf' : AEStronglyMeasurable f (Measure.map (quotientIntegerCover (coefficientIntegerLattice U) q) μ) := by
    rwa [hp.map_eq]
  simpa only [hp.map_eq] using (integral_map hp.measurable.aemeasurable hf').symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory

instance subspaceArrayIntegerLattice_closed {I D : Type*} (U : Submodule ℝ (D → ℝ)) :
    IsClosed (subspaceArrayIntegerLattice I U : Set (I → U)) := by
  change IsClosed {x : I → U | ∀ i a, ∃ n : ℤ, (x i).val a = n}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro a
  have hc : Continuous (fun x : I → U => (x i).val a) :=
    (continuous_apply a).comp (continuous_subtype_val.comp (continuous_apply i))
  have h : IsClosed {x : I → U | ∃ n : ℤ, (n : ℝ) = (x i).val a} :=
    Real.isClosedEmbedding_intCast.isClosed_range.preimage hc
  simpa only [eq_comm] using h

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))
variable [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]

noncomputable def euclideanSubspaceTorusMeasurableEquiv :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃ᵐ
        SubspaceArrayTorus Unit U := by
  let : BorelSpace (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) :=
    QuotientAddGroup.borelSpace
  exact (euclideanSubspaceTorusHomeomorph U).toMeasurableEquiv

variable (ν : Measure (euclideanSubspace U ⧸
  (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup))

noncomputable def euclideanSubspaceTorusMeasure : Measure (SubspaceArrayTorus Unit U) :=
  Measure.map (euclideanSubspaceTorusMeasurableEquiv U) ν

theorem euclideanSubspaceTorusMeasure_probability [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (euclideanSubspaceTorusMeasure U ν) := by
  unfold euclideanSubspaceTorusMeasure
  exact Measure.isProbabilityMeasure_map
    (euclideanSubspaceTorusMeasurableEquiv U).measurable.aemeasurable

theorem euclideanSubspaceTorusMeasure_invariant [ν.IsAddLeftInvariant] :
    (euclideanSubspaceTorusMeasure U ν).IsAddLeftInvariant :=
  isAddLeftInvariant_map (euclideanSubspaceTorusEquiv U).toAddMonoidHom.toAddHom
    (euclideanSubspaceTorusMeasurableEquiv U).measurable (euclideanSubspaceTorusEquiv U).surjective

theorem euclideanSubspaceTorusMeasure_mass
    (f : (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) → ℝ)
    (hf : Integrable f ν) (hm : (∫ x, f x ∂ν) = 1) :
    Integrable (fun y => f ((euclideanSubspaceTorusEquiv U).symm y))
        (euclideanSubspaceTorusMeasure U ν) ∧
      (∫ y, f ((euclideanSubspaceTorusEquiv U).symm y)
        ∂euclideanSubspaceTorusMeasure U ν) = 1 := by
  let e := euclideanSubspaceTorusMeasurableEquiv U
  change Integrable (fun y => f (e.symm y)) (Measure.map e ν) ∧
    (∫ y, f (e.symm y) ∂Measure.map e ν) = 1
  constructor
  · apply (integrable_map_equiv e _).mpr
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hf
  · rw [integral_map_equiv]
    simpa only [MeasurableEquiv.symm_apply_apply] using hm

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientCover_density_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) (D : CoefficientTorus (K := K) U → ℝ)
    (hD : Integrable D μ) (hmass : (∫ x, D x ∂μ) = 1) :
    Integrable (fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)) μ ∧
      (∫ x, D (quotientIntegerCover (coefficientIntegerLattice U) q x) ∂μ) = 1 :=
  ⟨coefficientCover_integrable U μ q hq D hD,
    (coefficientCover_integral U μ q hq D hD.aestronglyMeasurable).trans hmass⟩

theorem coefficientCover_density_sample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (hq : 0 < q) (D : CoefficientTorus (K := K) U → ℝ) (b : Option K → I → ℝ) :
    D (quotientIntegerCover (coefficientIntegerLattice U) q (affineCoefficientCoverSample U p hm q b)) =
      D (affineSampleCoefficientTorus U p hm b) := by
  rw [affineCoefficientCoverSample_projection U p hm q hq]

theorem coefficientCover_density_approximation {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (q : ℕ) (D : CoefficientTorus (K := K) U → ℝ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {η : ℝ}
    (happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η) :
    ∀ x, ‖(D (quotientIntegerCover (coefficientIntegerLattice U) q x) : ℂ) -
      coefficientTorusFourierSum U (fun a => dilateCoefficientFrequency q (frequency a)) c x‖ ≤ η := by
  intro x
  simpa only [coefficientTorusFourierSum_cover] using
    happrox (quotientIntegerCover (coefficientIntegerLattice U) q x)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem exists_covered_coefficient_density {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus S U)] [BorelSpace (SiteTorus S U)]
    (site : S → K → ℤ) (q : ℕ) (hq : 0 < q)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Continuous D) {B : ℝ}
    (hcap : ∀ x, D x ∈ Set.Icc (0 : ℝ) B) (hmass : (∫ x, D x ∂μ) = 1) :
    let E := coefficientSiteTorusMap U site
    let π := Set.rangeFactorization E
    let C := quotientIntegerCover (coefficientIntegerLattice U) q
    let R := coefficientSiteResidual U site (fun _ => q) T
    let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => q) T
    ∃ g : Set.range E → ℝ, Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) B) ∧
      Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
      (∀ x, g (π x) = linearQuotientAverage (coefficientIntegerLattice U) R hR μ D (C x)) ∧
      (realDensityMeasure μ (fun x => D (C x))).map π = realDensityMeasure (μ.map π) g := by
  intro E π C R hR
  have hE : Continuous E := coefficientSiteTorusMap_continuous U site
  have hπ : Measurable π := hE.rangeFactorization.measurable
  have hC : Continuous C := quotientIntegerCover_continuous _ q
  have hCp := coefficientCover_measurePreserving U μ q hq
  have hRc := linearQuotientEndomorphism_continuous _ R hR R.continuous_of_finiteDimensional
  have hb (x) : ‖D x‖ ≤ B := by rw [Real.norm_of_nonneg (hcap x).1]; exact (hcap x).2
  let f := linearQuotientAverage (coefficientIntegerLattice U) R hR μ D
  have hfc : Continuous f := BooleanCubeKernel.coefficientResidualAverage_continuous U R hR μ D hD hb
  have hi : Integrable D μ := Integrable.of_bound hD.aestronglyMeasurable B (ae_of_all μ hb)
  have hprob := linearQuotientAverage_probability _ R hR μ hRc.measurable D hD.measurable hi
    (fun x => (hcap x).1) hmass
  have hfiber (x y : CoefficientTorus (K := K) U) (hxy : E x = E y) : f (C x) = f (C y) := by
    exact linearQuotientAverage_cover_eq_of_map_eq (Y := SiteTorus S U)
      (coefficientIntegerLattice U) R hR μ q (coefficientSiteTorusMap U site)
      (coefficientSiteResidual_cover_on_kernel U site q T) D x y hxy
  obtain ⟨g, hgc, hg⟩ := exists_continuous_image_factor E hE (fun x => f (C x)) (hfc.comp hC)
    hfiber
  let _ : IsProbabilityMeasure (μ.map π) := Measure.isProbabilityMeasure_map hπ.aemeasurable
  have hgb (y) : g y ∈ Set.Icc (0 : ℝ) B := by
    obtain ⟨x, hx⟩ := Set.rangeFactorization_surjective y
    rw [← hx, hg]
    refine ⟨hprob.1 _, ?_⟩
    have h := linearQuotientAverage_bound _ R hR μ D hb (C x)
    rwa [Real.norm_of_nonneg (hprob.1 _)] at h
  have hgi : Integrable g (μ.map π) := Integrable.of_bound hgc.aestronglyMeasurable B
    (ae_of_all _ (fun y => by rw [Real.norm_of_nonneg (hgb y).1]; exact (hgb y).2))
  have hgmass : (∫ y, g y ∂μ.map π) = 1 := by
    rw [integral_map hπ.aemeasurable hgc.aestronglyMeasurable]
    change (∫ x, g (Set.rangeFactorization E x) ∂μ) = 1
    simp_rw [hg]
    exact (coefficientCover_integral U μ q hq f hfc.aestronglyMeasurable).trans hprob.2.2
  refine ⟨g, hgc, hgb, hgi, hgmass, hg, ?_⟩
  have hLmass : (∫ x, D (C x) ∂μ) = 1 :=
    (coefficientCover_integral U μ q hq D hD.aestronglyMeasurable).trans hmass
  have hLi : Integrable (fun x => D (C x)) μ := coefficientCover_integrable U μ q hq D hi
  have he (x) : linearQuotientAverage (coefficientIntegerLattice U) R hR μ (fun x => D (C x)) x =
      g (π x) := by
    rw [hg]
    exact (linearQuotientAverage_cover _ R hR μ q hCp D x
      (BooleanCubeKernel.coefficientResidual_section_integrable U R hR μ D hD hb (C x)).aestronglyMeasurable).symm
  have hshift : haarShiftDensity μ (-⇑(linearQuotientEndomorphism (coefficientIntegerLattice U) R hR))
      (fun x => D (C x)) = fun x => g (π x) := by
    funext x
    simpa only [haarShiftDensity, densityMixture, Pi.neg_apply, sub_neg_eq_add, linearQuotientAverage] using he x
  have hlaw := haarShiftDensity_map_eq μ μ (-⇑(linearQuotientEndomorphism (coefficientIntegerLattice U) R hR))
    hRc.measurable.neg (fun x => D (C x)) (hD.comp hC).measurable hLi (fun x => (hcap _).1) hLmass π hπ
    (fun y x => by
      apply Subtype.ext
      change E (x + -linearQuotientEndomorphism _ R hR y) = E x
      rw [map_add, map_neg, coefficientSiteResidual_site_zero U site q T hT, neg_zero, add_zero])
  rw [hshift] at hlaw
  rw [← hlaw]
  exact measurePreserving_realDensity_map μ (μ.map π) π ⟨hπ, rfl⟩ g hgc.measurable hgi (fun y => (hgb y).1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientCoverLaw
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (d : ℕ) (hd : 0 < d) :
    letI := coefficientCoverKernelFintype (K := K) U d hd
    finiteKernelLiftLaw (G := CoefficientTorus (K := K) U) (H := CoefficientTorus (K := K) U)
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d)
        (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
        (canonicalCoefficientCoverLift U b hb o d) =
      realDensityMeasure μ (fun y => canonicalCoefficientDensity U b hb o c w p
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) := by
  let _ := coefficientCoverKernelFintype (K := K) U d hd
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (c j) (w j) (p j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  let : IsProbabilityMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    Measure.pi.instIsProbabilityMeasure _
  have hi := (canonicalCoefficientDensity_mass U b hb o c w p μ ν hw hs).1
  apply finiteKernelLift_density (G := CoefficientTorus (K := K) U) (H := CoefficientTorus (K := K) U)
    (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d)
    (quotientIntegerCover_continuous _ d) (quotientIntegerCover_surjective _ d hd)
    μ μ (coefficientCover_measurePreserving U μ d hd)
    (canonicalCoefficientDensity U b hb o c w p)
    (canonicalCoefficientDensity_measurable U b hb o c w p) hi
    (canonicalCoefficientDensity_nonneg U b hb o c w p hw)
    _ _ (canonicalCoefficientCoverLift_measurable U b hb o d)
  have he : quotientIntegerCover (coefficientIntegerLattice (K := K) U) d ∘
      canonicalCoefficientCoverLift U b hb o d = canonicalCoefficientSample U b hb o :=
    funext (canonicalCoefficientCoverLift_projection U b hb o d hd)
  rw [he]
  exact canonicalCoefficientDensity_law U b hb o c w p μ ν hw hs

end Erdos3.VectorPolynomial

end

end OAI
