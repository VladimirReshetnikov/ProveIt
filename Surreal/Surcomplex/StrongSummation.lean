import Surreal.Foundations.SignSequenceStrongSummation
import Surreal.Surcomplex.HahnCoherence

/-!
# Strong sums of actual surcomplex numbers

The canonical complex normal form combines the canonical real and imaginary
normal forms. Native complex Hahn strong summability is equivalent to strong
summability of both actual coordinate families. Their coordinatewise strong
sum has exactly the native complex coefficient sum, and small Hahn workspace
evaluation commutes with it. Index smallness is explicit; no topological sum
or uniqueness from approximation bounds is used.
-/

universe u v w

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The canonical complex Hahn series of an actual surcomplex number. -/
def rawNormalForm (z : Surcomplex.{u}) :
    _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℂ :=
  HahnSeries.realComplexHahnEquiv
    ⟨SignSequence.rawNormalForm z.re, SignSequence.rawNormalForm z.im⟩

/-- Canonical complex coefficients are the pair of canonical real coefficients. -/
@[simp] theorem coeff_rawNormalForm (z : Surcomplex.{u}) (a : _root_.Surreal.{u}ᵒᵈ) :
    (rawNormalForm z).coeff a =
      ⟨(SignSequence.rawNormalForm z.re).coeff a,
        (SignSequence.rawNormalForm z.im).coeff a⟩ :=
  HahnSeries.coeff_realComplexHahnEquiv _ _

/-- The complex support is exactly the union of the coordinate supports. -/
theorem support_rawNormalForm (z : Surcomplex.{u}) :
    (rawNormalForm z).support =
      (SignSequence.rawNormalForm z.re).support ∪
        (SignSequence.rawNormalForm z.im).support :=
  HahnSeries.support_realComplexHahnEquiv _

/-- The canonical complex normal form has lower-universe-small support. -/
instance small_support_rawNormalForm (z : Surcomplex.{u}) :
    Small.{u} (rawNormalForm z).support := by
  rw [support_rawNormalForm]
  infer_instance

/-- Exact complex normal forms determine the actual number. -/
theorem rawNormalForm_injective : Function.Injective (rawNormalForm : Surcomplex.{u} → _) := by
  intro z w h
  have hc := HahnSeries.realComplexHahnEquiv.injective h
  apply ext
  · apply SmallNormalForm.cutEvaluationRingEquiv.symm.injective
    apply Subtype.ext
    apply ofLex.injective
    exact congrArg QuadraticAlgebra.re hc
  · apply SmallNormalForm.cutEvaluationRingEquiv.symm.injective
    apply Subtype.ext
    apply ofLex.injective
    exact congrArg QuadraticAlgebra.im hc

/-- Joint support well-ordering and finite complex coefficient fibers. -/
def StronglySummable {ι : Type v} (f : ι → Surcomplex.{u}) : Prop :=
  (⋃ i, (rawNormalForm (f i)).support).IsPWO ∧
    ∀ a, {i | (rawNormalForm (f i)).coeff a ≠ 0}.Finite

private theorem co_support_rawNormalForm {ι : Type v} (f : ι → Surcomplex.{u})
    (a : _root_.Surreal.{u}ᵒᵈ) :
    {i | (rawNormalForm (f i)).coeff a ≠ 0} =
      {i | (SignSequence.rawNormalForm (f i).re).coeff a ≠ 0} ∪
        {i | (SignSequence.rawNormalForm (f i).im).coeff a ≠ 0} := by
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, coeff_rawNormalForm,
    ne_eq, Complex.ext_iff, Complex.zero_re, Complex.zero_im, not_and_or]

/-- Native complex strong summability is exactly coordinatewise actual strong summability. -/
theorem stronglySummable_iff_re_im {ι : Type v} (f : ι → Surcomplex.{u}) :
    StronglySummable f ↔
      SignSequence.StronglySummable (fun i => (f i).re) ∧
        SignSequence.StronglySummable (fun i => (f i).im) := by
  simp only [StronglySummable, SignSequence.StronglySummable,
    support_rawNormalForm, Set.iUnion_union_distrib, Set.isPWO_union,
    co_support_rawNormalForm, Set.finite_union, forall_and]
  tauto

theorem StronglySummable.re {ι : Type v} {f : ι → Surcomplex.{u}}
    (hf : StronglySummable f) : SignSequence.StronglySummable (fun i => (f i).re) :=
  ((stronglySummable_iff_re_im f).mp hf).1

theorem StronglySummable.im {ι : Type v} {f : ι → Surcomplex.{u}}
    (hf : StronglySummable f) : SignSequence.StronglySummable (fun i => (f i).im) :=
  ((stronglySummable_iff_re_im f).mp hf).2

/-- The native complex family supplied by the actual strong summability predicate. -/
def StronglySummable.toHahnFamily {ι : Type v} {f : ι → Surcomplex.{u}}
    (hf : StronglySummable f) :
    _root_.HahnSeries.SummableFamily (_root_.Surreal.{u}ᵒᵈ) ℂ ι where
  toFun i := rawNormalForm (f i)
  isPWO_iUnion_support' := hf.1
  finite_co_support' := hf.2

@[simp] theorem StronglySummable.toHahnFamily_apply {ι : Type v}
    {f : ι → Surcomplex.{u}} (hf : StronglySummable f) (i : ι) :
    hf.toHahnFamily i = rawNormalForm (f i) := rfl

/-- Actual complex strong summation is coordinatewise actual real strong summation. -/
def strongSum {ι : Type v} [Small.{u} ι] (f : ι → Surcomplex.{u})
    (hf : StronglySummable f) : Surcomplex.{u} :=
  ⟨SignSequence.strongSum (fun i => (f i).re) hf.re,
    SignSequence.strongSum (fun i => (f i).im) hf.im⟩

@[simp] theorem strongSum_re {ι : Type v} [Small.{u} ι]
    (f : ι → Surcomplex.{u}) (hf : StronglySummable f) :
    (strongSum f hf).re = SignSequence.strongSum (fun i => (f i).re) hf.re := rfl

@[simp] theorem strongSum_im {ι : Type v} [Small.{u} ι]
    (f : ι → Surcomplex.{u}) (hf : StronglySummable f) :
    (strongSum f hf).im = SignSequence.strongSum (fun i => (f i).im) hf.im := rfl

/-- Coordinatewise actual summation equals the native complex Hahn sum exactly. -/
@[simp] theorem rawNormalForm_strongSum {ι : Type v} [Small.{u} ι]
    (f : ι → Surcomplex.{u}) (hf : StronglySummable f) :
    rawNormalForm (strongSum f hf) = hf.toHahnFamily.hsum := by
  apply _root_.HahnSeries.ext
  funext a
  rw [coeff_rawNormalForm, strongSum_re, strongSum_im,
    SignSequence.rawNormalForm_strongSum, SignSequence.rawNormalForm_strongSum]
  apply Complex.ext
  · simpa only [_root_.HahnSeries.SummableFamily.coeff_hsum,
      StronglySummable.toHahnFamily_apply, coeff_rawNormalForm,
      SignSequence.StronglySummable.toHahnFamily_apply, Complex.coe_reAddGroupHom] using
      (Complex.reAddGroupHom.map_finsum (hf.toHahnFamily.finite_co_support a)).symm
  · simpa only [_root_.HahnSeries.SummableFamily.coeff_hsum,
      StronglySummable.toHahnFamily_apply, coeff_rawNormalForm,
      SignSequence.StronglySummable.toHahnFamily_apply, Complex.coe_imAddGroupHom] using
      (Complex.imAddGroupHom.map_finsum (hf.toHahnFamily.finite_co_support a)).symm

/-- Actual strong sums have the finite sum of the input coefficients at every exponent. -/
theorem coeff_rawNormalForm_strongSum {ι : Type v} [Small.{u} ι]
    (f : ι → Surcomplex.{u}) (hf : StronglySummable f) (a : _root_.Surreal.{u}ᵒᵈ) :
    (rawNormalForm (strongSum f hf)).coeff a = ∑ᶠ i, (rawNormalForm (f i)).coeff a := by
  rw [rawNormalForm_strongSum]
  exact _root_.HahnSeries.SummableFamily.coeff_hsum

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ] {ι : Type w}

/-- Actual complex workspace evaluation retains exactly the embedded native Hahn series. -/
@[simp] theorem rawNormalForm_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℂ) :
    rawNormalForm (hahnEmbedding e he x) =
      HahnSeries.workspaceEmbedding (SmallNormalForm.hahnGrowthMap e)
        (SmallNormalForm.hahnGrowthMap_strictMono e he) x := by
  obtain ⟨z, rfl⟩ := HahnSeries.realComplexHahnEquiv.surjective x
  rw [hahnEmbedding_realComplexHahnEquiv, rawNormalForm,
    SignSequence.rawNormalForm_hahnEmbedding, SignSequence.rawNormalForm_hahnEmbedding,
    HahnSeries.workspaceEmbedding_realComplexHahnEquiv]

/-- Complex workspace embeddings preserve joint strong summability for every index type. -/
theorem stronglySummable_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (s : _root_.HahnSeries.SummableFamily Γ ℂ ι) :
    StronglySummable (fun i => hahnEmbedding e he (s i)) := by
  let t := HahnSeries.mapExponentsFamily (SmallNormalForm.hahnGrowthMap e)
    (SmallNormalForm.hahnGrowthMap_strictMono e he) s
  constructor
  · simpa only [t, HahnSeries.mapExponentsFamily_apply,
      rawNormalForm_hahnEmbedding] using t.isPWO_iUnion_support
  · intro a
    simpa only [t, HahnSeries.mapExponentsFamily_apply,
      rawNormalForm_hahnEmbedding, Function.HasFiniteSupport, Function.support]
      using t.finite_co_support a

/-- The family behind actual summation is the native exponent transport. -/
theorem toHahnFamily_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (s : _root_.HahnSeries.SummableFamily Γ ℂ ι) :
    (stronglySummable_hahnEmbedding e he s).toHahnFamily =
      HahnSeries.mapExponentsFamily (SmallNormalForm.hahnGrowthMap e)
        (SmallNormalForm.hahnGrowthMap_strictMono e he) s := by
  apply _root_.HahnSeries.SummableFamily.ext
  intro i
  exact rawNormalForm_hahnEmbedding e he (s i)

/-- Actual complex evaluation commutes with every small-index native strong sum. -/
theorem strongSum_hahnEmbedding [Small.{u} ι]
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (s : _root_.HahnSeries.SummableFamily Γ ℂ ι) :
    strongSum (fun i => hahnEmbedding e he (s i)) (stronglySummable_hahnEmbedding e he s) =
      hahnEmbedding e he s.hsum := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_hahnEmbedding,
    toHahnFamily_hahnEmbedding, HahnSeries.hsum_mapExponentsFamily]

end Workspace

end

end Surreal.Surcomplex
