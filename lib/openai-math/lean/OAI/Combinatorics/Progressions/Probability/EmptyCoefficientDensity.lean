/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Specify the product-integral measure family and its sigma-finiteness on Lean 4.32.
Mathematical statements are unchanged. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Fourier.EuclideanCoefficientTorus
import OAI.Combinatorics.Progressions.Geometry.MixedArraySourceSupport

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalArrayDensity (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    (y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) : ℝ :=
  ∏ j, canonicalMixedDensity W b hb o (fun i => c i j) (fun i => w i j) (fun i => p i j) (y j)

theorem canonicalArrayDensity_measurable (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ) :
    Measurable (canonicalArrayDensity W b hb o c w p) :=
  Finset.measurable_prod _ (fun j _ =>
    (canonicalMixedDensity_measurable W b hb o _ _ _).comp (measurable_pi_apply j))

theorem canonicalArrayDensity_recover (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    {y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalArrayDensity W b hb o c w p y ≠ 0) :
    ∃ x : (I → J → ℝ) × (Fin n → J → ℤ),
      mixedArrayQuotient W b hb o x = y ∧ mixedArrayInChart W b o x ∧ mixedArraySupported c w p x := by
  classical
  have hs (j : J) := canonicalMixedDensity_recover W b hb o (fun i => c i j)
    (fun i => w i j) (fun i => p i j) ((Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j))
  choose a hac haq has using hs
  let x := (mixedArrayRegroup I (Fin n) J).symm a
  have hx : mixedArrayRegroup I (Fin n) J x = a := (mixedArrayRegroup I (Fin n) J).apply_symm_apply a
  refine ⟨x, ?_, ?_, ?_⟩
  · funext j
    change normalizedLatticeQuotient W b hb (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) = y j
    rw [hx]
    exact haq j
  · intro j
    change normalizedLatticePoint W b (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) ∈ _
    rw [hx]
    exact hac j
  · intro j
    rw [hx]
    exact has j

theorem canonicalArrayDensity_recover_unique (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    {y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalArrayDensity W b hb o c w p y ≠ 0) :
    ∃! x : (I → J → ℝ) × (Fin n → J → ℤ),
      mixedArrayQuotient W b hb o x = y ∧ mixedArrayInChart W b o x ∧ mixedArraySupported c w p x := by
  obtain ⟨x, hx⟩ := canonicalArrayDensity_recover W b hb o c w p hy
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact mixedArrayQuotient_injOn_chart W b hb o hz.2.1 hx.2.1 (hz.1.trans hx.1.symm)

theorem canonicalArrayDensity_apply (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    (x : (I → J → ℝ) × (Fin n → J → ℤ)) (hx : mixedArrayInChart W b o x) :
    canonicalArrayDensity W b hb o c w p (mixedArrayQuotient W b hb o x) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) ^ Fintype.card J *
        ∏ j, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j)
          (mixedArrayRegroup I (Fin n) J x j) := by
  unfold canonicalArrayDensity mixedArrayQuotient
  simp_rw [canonicalMixedDensity_apply W b hb o _ _ _ (hx _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem canonicalArrayDensity_nonzero_iff
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    (y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalArrayDensity W b hb o c w p y ≠ 0 ↔
      ∃ x : (I → J → ℝ) × (Fin n → J → ℤ),
        mixedArrayQuotient W b hb o x = y ∧ mixedArrayInChart W b o x ∧ mixedArraySupported c w p x := by
  classical
  constructor
  · exact canonicalArrayDensity_recover W b hb o c w p
  · rintro ⟨x, rfl, hx, hs⟩
    rw [canonicalArrayDensity_apply W b hb o c w p x hx]
    exact mul_ne_zero (pow_ne_zero _ (ZLattice.covolume_pos _ volume).ne')
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hs j))

theorem canonicalArrayDensity_nonneg
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ) (y) :
    0 ≤ canonicalArrayDensity W b hb o c w p y :=
  Finset.prod_nonneg (fun j _ => canonicalMixedDensity_nonneg W b hb o _ _ (fun i => hw i j) _ _)

theorem canonicalArrayDensity_mass
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j) x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Integrable (canonicalArrayDensity W b hb o c w p) (Measure.pi (fun _ : J => μ)) ∧
      (∫ y, canonicalArrayDensity W b hb o c w p y ∂Measure.pi (fun _ : J => μ)) = 1 := by
  have hslot (j) := canonicalMixedDensity_mass W b hb o μ _ _ (fun i => hw i j) _ (hs j)
  refine ⟨Integrable.fintype_prod_dep (fun j => (hslot j).1), ?_⟩
  unfold canonicalArrayDensity
  rw [@integral_fintype_prod_eq_prod ℝ J _ _ _ _ _ (fun _ : J => μ)
    (fun _ => IsFiniteMeasure.toSigmaFinite μ)]
  exact Finset.prod_eq_one (fun j _ => (hslot j).2)

theorem canonicalArrayDensity_law
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j) x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Measure.map (mixedArrayQuotient W b hb o) (mixedScalarArrayLaw c w p) =
      realDensityMeasure (Measure.pi (fun _ : J => μ)) (canonicalArrayDensity W b hb o c w p) := by
  let q := fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart o x)
  have hq : Measurable q := (normalizedLatticeQuotient_measurable W b hb).comp (orthonormalMixedChart o).measurable
  have hqa : Measurable (fun x : J → (I → ℝ) × (Fin n → ℤ) => fun j => q (x j)) :=
    Measurable.of_eval (fun j => hq.comp (measurable_pi_apply j))
  change Measure.map ((fun x j => q (x j)) ∘ mixedArrayRegroup I (Fin n) J) (mixedScalarArrayLaw c w p) = _
  rw [← Measure.map_map hqa (mixedArrayRegroup I (Fin n) J).measurable, mixedScalarArrayLaw_regroup c w hw p]
  exact productDensity_pushforward _ (fun _ : J => μ) (fun _ => q) (fun _ => hq)
    (fun j => canonicalMixedDensity W b hb o (fun i => c i j) (fun i => w i j) (fun i => p i j))
    (fun j => (canonicalMixedDensity_mass W b hb o μ _ _ (fun i => hw i j) _ (hs j)).1)
    (fun j => canonicalMixedDensity_nonneg W b hb o _ _ (fun i => hw i j) _)
    (fun j => canonicalMixedDensity_law W b hb o μ _ _ (fun i => hw i j) _ (hs j))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

abbrev CoefficientSamplerArrays (I : Fin m → Type*) (n : Fin m → ℕ) :=
  ∀ j : Fin m,
    (I j → BoundedCoefficientExponent K (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℤ)

noncomputable def canonicalCoefficientSample (a : CoefficientSamplerArrays (K := K) I n) :
    CoefficientTorus (K := K) U :=
  (euclideanCoefficientEquiv U).symm
    (fun j => mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j))

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def canonicalCoefficientDensity (y : CoefficientTorus (K := K) U) : ℝ :=
  ∏ j, canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
    (euclideanCoefficientEquiv U y j)

theorem canonicalCoefficientDensity_recover_unique
    {y : CoefficientTorus (K := K) U} (hy : canonicalCoefficientDensity U b hb o c w p y ≠ 0) :
    ∃! a : CoefficientSamplerArrays (K := K) I n,
      canonicalCoefficientSample U b hb o a = y ∧
        ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (a j) ∧
          mixedArraySupported (c j) (w j) (p j) (a j) := by
  classical
  have hs (j : Fin m) := canonicalArrayDensity_recover_unique
    (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
    ((Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j))
  choose a ha hu using hs
  refine ⟨a, ⟨?_, fun j => (ha j).2⟩, ?_⟩
  · apply (euclideanCoefficientEquiv U).injective
    rw [canonicalCoefficientSample, AddEquiv.apply_symm_apply]
    exact funext (fun j => (ha j).1)
  · intro z hz
    have hq := congrArg (euclideanCoefficientEquiv U) hz.1
    rw [canonicalCoefficientSample, AddEquiv.apply_symm_apply] at hq
    exact funext (fun j => hu j (z j) ⟨congrFun hq j, hz.2 j⟩)

theorem canonicalCoefficientDensity_measurable
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] :
    Measurable (canonicalCoefficientDensity U b hb o c w p) := by
  apply Finset.measurable_prod
  intro j _
  exact (canonicalArrayDensity_measurable _ (b j) (hb j) (o j) (c j) (w j) (p j)).comp
    ((measurable_pi_apply j).comp (euclideanCoefficientEquiv_continuous U).measurable)

theorem canonicalCoefficientSample_measurable
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] :
    Measurable (canonicalCoefficientSample (K := K) U b hb o) :=
  (euclideanCoefficientMeasurableEquiv (K := K) U).symm.measurable.comp
    (Measurable.of_eval (fun j =>
      (mixedArrayQuotient_measurable _ (b j) (hb j) (o j)).comp (measurable_pi_apply j)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem canonicalCoefficientDensity_nonneg (hw : ∀ j i d, 0 < w j i d)
    (y : CoefficientTorus (K := K) U) : 0 ≤ canonicalCoefficientDensity U b hb o c w p y :=
  Finset.prod_nonneg (fun j _ => canonicalArrayDensity_nonneg _ (b j) (hb j) (o j)
    (c j) (w j) (hw j) (p j) _)

theorem canonicalCoefficientDensity_nonzero_iff (y : CoefficientTorus (K := K) U) :
    canonicalCoefficientDensity U b hb o c w p y ≠ 0 ↔
      ∃ a : CoefficientSamplerArrays (K := K) I n,
        canonicalCoefficientSample U b hb o a = y ∧
          ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (a j) ∧
            mixedArraySupported (c j) (w j) (p j) (a j) := by
  constructor
  · intro hy
    exact (canonicalCoefficientDensity_recover_unique U b hb o c w p hy).exists
  · rintro ⟨a, rfl, ha⟩
    unfold canonicalCoefficientDensity canonicalCoefficientSample
    rw [AddEquiv.apply_symm_apply]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact (canonicalArrayDensity_nonzero_iff _ (b j) (hb j) (o j) (c j) (w j) (p j) _).mpr
      ⟨a j, rfl, ha j⟩

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hw : ∀ j i d, 0 < w j i d)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))

include ν hw hs

theorem canonicalCoefficientDensity_mass :
    Integrable (canonicalCoefficientDensity U b hb o c w p) μ ∧
      (∫ y, canonicalCoefficientDensity U b hb o c w p y ∂μ) = 1 := by
  let f := fun j => canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
  have hm (j) := canonicalArrayDensity_mass _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j)
  have hi : Integrable (tensorCutoffWeight f)
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) :=
    Integrable.fintype_prod_dep (fun j => (hm j).1)
  have hp := euclideanCoefficient_measurePreserving U μ ν
  refine ⟨hp.integrable_comp_of_integrable hi, ?_⟩
  have he := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (tensorCutoffWeight f) (Measure.map (euclideanCoefficientEquiv U) μ) from
      hp.map_eq.symm ▸ hi.aestronglyMeasurable)
  change (∫ y, tensorCutoffWeight f (euclideanCoefficientEquiv U y) ∂μ) = 1
  rw [← he, hp.map_eq]
  change (∫ y : EuclideanCoefficientLayers (K := K) U, (∏ j, f j (y j))
    ∂Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun j _ => (hm j).2)

omit [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem canonicalCoefficientLayers_law :
    Measure.map (fun a : CoefficientSamplerArrays (K := K) I n => fun j =>
      mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j))
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) =
      realDensityMeasure
        (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)))
        (fun y : EuclideanCoefficientLayers (K := K) U => ∏ j,
          canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j)
            (c j) (w j) (p j) (y j)) := by
  let f := fun j => canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
  let q := fun j => mixedArrayQuotient (J := BoundedCoefficientExponent K (j.val + 1))
    (euclideanSubspace (U j)) (b j) (hb j) (o j)
  let : ∀ j, IsProbabilityMeasure
      (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) :=
    fun j => Measure.pi.instIsProbabilityMeasure _
  have hq (j) : Measurable (q j) := mixedArrayQuotient_measurable _ (b j) (hb j) (o j)
  have hm (j) := canonicalArrayDensity_mass _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j)
  exact productDensity_pushforward (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) q hq f
    (fun j => (hm j).1)
    (fun j => canonicalArrayDensity_nonneg _ (b j) (hb j) (o j) (c j) (w j) (hw j) (p j))
    (fun j => canonicalArrayDensity_law _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j))

theorem canonicalCoefficientDensity_law :
    Measure.map (canonicalCoefficientSample (K := K) U b hb o)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) =
        realDensityMeasure μ (canonicalCoefficientDensity U b hb o c w p) := by
  let q := fun a : CoefficientSamplerArrays (K := K) I n => fun j =>
    mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j)
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))
  let e := euclideanCoefficientMeasurableEquiv (K := K) U
  have hq : Measurable q := Measurable.of_eval (fun j =>
    (mixedArrayQuotient_measurable _ (b j) (hb j) (o j)).comp (measurable_pi_apply j))
  have hp : Measure.map e μ = ξ := (euclideanCoefficient_measurePreserving U μ ν).map_eq
  have hinv : Measure.map e.symm ξ = μ := by rw [← hp]; exact e.map_symm_map
  change Measure.map (e.symm ∘ q) _ = _
  rw [← Measure.map_map e.symm.measurable hq,
    canonicalCoefficientLayers_law U b hb o c w p ν hw hs,
    realDensityMeasure_map_equiv, hinv]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem canonicalMixedDensity_empty
    {D I : Type*} [Fintype D] [Fintype I] [IsEmpty D] [IsEmpty I]
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W)
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (p : Fin n → PMF ℤ)
    (y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalMixedDensity W b hb o c w p y = 1 := by
  let Q := W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let : Subsingleton Q := ⟨by
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg QuotientAddGroup.mk (Subsingleton.elim x y)⟩
  let μ : Measure Q := probabilityAddHaar Q
  let : IsProbabilityMeasure μ := probabilityAddHaar_probability Q
  let : μ.IsAddLeftInvariant := probabilityAddHaar_invariant Q
  have hmass := (canonicalMixedDensity_mass W b hb o μ c w
    (fun i => isEmptyElim i) p (fun _ _ i => isEmptyElim i)).2
  have hconst : canonicalMixedDensity W b hb o c w p =
      fun _ => canonicalMixedDensity W b hb o c w p y := by
    funext z
    exact congrArg (canonicalMixedDensity W b hb o c w p) (Subsingleton.elim z y)
  rw [hconst] at hmass
  simpa using hmass

namespace VectorPolynomial

theorem canonicalCoefficientDensity_empty
    {K : Type*} [Fintype K] {m : ℕ}
    {J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
    [∀ j, IsEmpty (J j)] [∀ j, IsEmpty (I j)]
    {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (y : CoefficientTorus (K := K) U) :
    canonicalCoefficientDensity U b hb o c w p y = 1 := by
  unfold canonicalCoefficientDensity
  apply Finset.prod_eq_one
  intro j _
  unfold canonicalArrayDensity
  apply Finset.prod_eq_one
  intro e _
  exact canonicalMixedDensity_empty _ (b j) (hb j) (o j) _ _ _ _

end VectorPolynomial
end Erdos3

end

end OAI
