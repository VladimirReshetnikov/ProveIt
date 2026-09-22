import Surreal.Foundations.SignSequenceHahnEmbedding

/-!
# Strong sums of actual surreal numbers

Canonical normal forms identify an actual family with native Hahn series.
Strong summability requires a partially well-ordered union of supports and
finite coefficient fibers. For a small index type the resulting Hahn sum
has small support, so the proved normal-form equivalence evaluates it as an
actual surreal number. This is coefficientwise strong summation, with no
topological convergence or approximation-only uniqueness assumption.

Every small real Hahn workspace embedding preserves these families and their
strong sums. The index-smallness hypothesis on the sum is explicit and is
independent of the exponent workspace's smallness.
-/

universe u v w

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The native Hahn series underlying the canonical normal form of an actual surreal. -/
def rawNormalForm (x : SignSequence.{u}) :
    _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℝ :=
  ofLex (SmallNormalForm.normalForm x).val

/-- Raw normal forms retain the lower-universe support bound. -/
instance small_support_rawNormalForm (x : SignSequence.{u}) :
    Small.{u} (rawNormalForm x).support :=
  _root_.SurrealHahnSeries.small_support (SmallNormalForm.normalForm x)

/-- Both strong summability conditions are imposed on canonical normal forms. -/
def StronglySummable {ι : Type v} (f : ι → SignSequence.{u}) : Prop :=
  (⋃ i, (rawNormalForm (f i)).support).IsPWO ∧
    ∀ a, {i | (rawNormalForm (f i)).coeff a ≠ 0}.Finite

/-- A strong summability proof supplies the native summable family without choices. -/
def StronglySummable.toHahnFamily {ι : Type v} {f : ι → SignSequence.{u}}
    (hf : StronglySummable f) :
    _root_.HahnSeries.SummableFamily (_root_.Surreal.{u}ᵒᵈ) ℝ ι where
  toFun i := rawNormalForm (f i)
  isPWO_iUnion_support' := hf.1
  finite_co_support' := hf.2

@[simp] theorem StronglySummable.toHahnFamily_apply {ι : Type v}
    {f : ι → SignSequence.{u}} (hf : StronglySummable f) (i : ι) :
    hf.toHahnFamily i = rawNormalForm (f i) := rfl

/-- Small index families have small formal sums, including after coefficient cancellation. -/
theorem StronglySummable.small_support_hsum {ι : Type v} [Small.{u} ι]
    {f : ι → SignSequence.{u}} (hf : StronglySummable f) :
    Small.{u} hf.toHahnFamily.hsum.support := by
  letI : ∀ i, Small.{u} (hf.toHahnFamily i).support :=
    fun i => small_support_rawNormalForm (f i)
  exact small_subset _root_.HahnSeries.SummableFamily.support_hsum_subset

/-- The actual strong sum is the evaluation of the coefficientwise formal sum. -/
def strongSum {ι : Type v} [Small.{u} ι] (f : ι → SignSequence.{u})
    (hf : StronglySummable f) : SignSequence.{u} :=
  SmallNormalForm.cutEvaluation
    (SmallNormalForm.ofHahn hf.toHahnFamily.hsum hf.small_support_hsum)

/-- Extraction recovers precisely the formal sum, not merely its finite approximations. -/
@[simp] theorem normalForm_strongSum {ι : Type v} [Small.{u} ι]
    (f : ι → SignSequence.{u}) (hf : StronglySummable f) :
    SmallNormalForm.normalForm (strongSum f hf) =
      SmallNormalForm.ofHahn hf.toHahnFamily.hsum hf.small_support_hsum :=
  SmallNormalForm.normalForm_cutEvaluation _

/-- On native Hahn coefficients the actual sum is exactly `SummableFamily.hsum`. -/
@[simp] theorem rawNormalForm_strongSum {ι : Type v} [Small.{u} ι]
    (f : ι → SignSequence.{u}) (hf : StronglySummable f) :
    rawNormalForm (strongSum f hf) = hf.toHahnFamily.hsum := by
  rw [rawNormalForm, normalForm_strongSum, SmallNormalForm.ofLex_ofHahn]

/-- Every growth coefficient of an actual strong sum is its finite coefficient sum. -/
theorem coeff_normalForm_strongSum {ι : Type v} [Small.{u} ι]
    (f : ι → SignSequence.{u}) (hf : StronglySummable f) (a : SignSequence.{u}) :
    SmallNormalForm.coeff (SmallNormalForm.normalForm (strongSum f hf)) a =
      ∑ᶠ i, SmallNormalForm.coeff (SmallNormalForm.normalForm (f i)) a := by
  change (rawNormalForm (strongSum f hf)).coeff (OrderDual.toDual (toSurreal a)) = _
  rw [rawNormalForm_strongSum]
  exact _root_.HahnSeries.SummableFamily.coeff_hsum

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ] {ι : Type w}

/-- The raw normal form of a workspace value is the native exponent embedding. -/
@[simp] theorem rawNormalForm_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    rawNormalForm (hahnEmbedding e he x) =
      Surreal.HahnSeries.workspaceEmbedding (SmallNormalForm.hahnGrowthMap e)
        (SmallNormalForm.hahnGrowthMap_strictMono e he) x := by
  rw [rawNormalForm, normalForm_hahnEmbedding, SmallNormalForm.ofLex_hahnEmbedding]

/-- An actual Hahn workspace embedding preserves joint strong summability. -/
theorem stronglySummable_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (s : _root_.HahnSeries.SummableFamily Γ ℝ ι) :
    StronglySummable (fun i => hahnEmbedding e he (s i)) := by
  let t := Surreal.HahnSeries.mapExponentsFamily (SmallNormalForm.hahnGrowthMap e)
    (SmallNormalForm.hahnGrowthMap_strictMono e he) s
  constructor
  · simpa only [t, Surreal.HahnSeries.mapExponentsFamily_apply,
      rawNormalForm_hahnEmbedding] using t.isPWO_iUnion_support
  · intro a
    simpa only [t, Surreal.HahnSeries.mapExponentsFamily_apply,
      rawNormalForm_hahnEmbedding, Function.HasFiniteSupport, Function.support]
      using t.finite_co_support a

/-- The induced native family is the existing support-preserving exponent transport. -/
theorem toHahnFamily_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (s : _root_.HahnSeries.SummableFamily Γ ℝ ι) :
    (stronglySummable_hahnEmbedding e he s).toHahnFamily =
      Surreal.HahnSeries.mapExponentsFamily (SmallNormalForm.hahnGrowthMap e)
        (SmallNormalForm.hahnGrowthMap_strictMono e he) s := by
  apply _root_.HahnSeries.SummableFamily.ext
  intro i
  exact rawNormalForm_hahnEmbedding e he (s i)

/-- Actual evaluation of a Hahn workspace commutes with every small strong sum. -/
theorem strongSum_hahnEmbedding [Small.{u} ι]
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (s : _root_.HahnSeries.SummableFamily Γ ℝ ι) :
    strongSum (fun i => hahnEmbedding e he (s i)) (stronglySummable_hahnEmbedding e he s) =
      hahnEmbedding e he s.hsum := by
  apply SmallNormalForm.cutEvaluationRingEquiv.symm.injective
  change SmallNormalForm.normalForm _ = SmallNormalForm.normalForm _
  rw [normalForm_strongSum, normalForm_hahnEmbedding]
  apply Subtype.ext
  apply ofLex.injective
  rw [SmallNormalForm.ofLex_ofHahn, SmallNormalForm.ofLex_hahnEmbedding,
    toHahnFamily_hahnEmbedding, Surreal.HahnSeries.hsum_mapExponentsFamily]

end Workspace

end

end Surreal.Foundations.SignSequence
