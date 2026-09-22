import Surreal.HahnSeries.StrongEvaluation
import Surreal.Foundations.SignSequencePowerSeries
import Surreal.Surcomplex.PowerSeries

/-!
# Strong additivity of actual formal-series evaluation

A source-summable family of ordinary formal series evaluates to an actual
strongly summable family at any infinitesimal argument. For a small source
index type, evaluation of its coefficient sum is the actual strong sum.
This establishes the strong-additivity clause of `thm:exact` on the actual
carriers. Zero arguments and arbitrary coefficient sizes are included.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

private abbrev strongArgumentFamily (x : SignSequence.{u}) : Unit → SignSequence.{u} := fun _ => x

private abbrev strongArgumentExponents (x : SignSequence.{u}) :=
  workspaceExponents (⋃ i, SmallNormalForm.support
    (SmallNormalForm.normalForm (strongArgumentFamily x i)))

private def strongArgumentInclusion (x : SignSequence.{u}) :
    strongArgumentExponents x →+ SignSequence.{u} :=
  (strongArgumentExponents x).subtype.toAddMonoidHom

private theorem strongArgumentInclusion_strictMono (x : SignSequence.{u}) :
    StrictMono (strongArgumentInclusion x) := fun _ _ h => h

private abbrev strongArgumentPreimage (x : SignSequence.{u}) :
    _root_.HahnSeries (strongArgumentExponents x) ℝ :=
  familyHahnPreimage (strongArgumentFamily x) ()

private theorem strongArgument_spec (x : SignSequence.{u}) :
    hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x)
      (strongArgumentPreimage x) = x :=
  familyWorkspaceEmbedding_preimage (strongArgumentFamily x) ()

private theorem strongArgument_pos (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    0 < (strongArgumentPreimage x).orderTop := by
  apply (isInfinitesimal_hahnEmbedding_iff (strongArgumentInclusion x)
    (strongArgumentInclusion_strictMono x) _).mp
  simpa only [strongArgument_spec] using hx

private theorem strongArgument_evaluation (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) :
    powerSeriesEvaluation x hx f =
      hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x)
        (HahnSeries.evaluate (strongArgumentPreimage x) (strongArgument_pos x hx) f) := by
  simpa only [strongArgument_spec] using powerSeriesEvaluation_hahnEmbedding
    (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x)
    (strongArgumentPreimage x) (strongArgument_pos x hx) f

/-- Actual evaluation preserves both summability conditions for any source-summable family. -/
theorem stronglySummable_powerSeriesEvaluation {ι : Type v}
    (x : SignSequence.{u}) (hx : IsInfinitesimal x) (f : ι → PowerSeries ℝ)
    (hf : HahnSeries.PowerSeriesSummable f) :
    StronglySummable (fun i => powerSeriesEvaluation x hx (f i)) := by
  let s := HahnSeries.evaluatedPowerSeriesFamily (strongArgumentPreimage x)
    (strongArgument_pos x hx) f hf
  have hs (i : ι) :
      hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) (s i) =
        powerSeriesEvaluation x hx (f i) := by
    rw [HahnSeries.evaluatedPowerSeriesFamily_apply, ← strongArgument_evaluation]
  simpa only [hs] using stronglySummable_hahnEmbedding
    (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) s

/-- Evaluation of a small coefficient sum is precisely the actual strong sum of its values. -/
theorem powerSeriesEvaluation_powerSeriesSum {ι : Type v} [Small.{u} ι]
    (x : SignSequence.{u}) (hx : IsInfinitesimal x) (f : ι → PowerSeries ℝ)
    (hf : HahnSeries.PowerSeriesSummable f) :
    powerSeriesEvaluation x hx (HahnSeries.powerSeriesSum f) =
      strongSum (fun i => powerSeriesEvaluation x hx (f i))
        (stronglySummable_powerSeriesEvaluation x hx f hf) := by
  let s := HahnSeries.evaluatedPowerSeriesFamily (strongArgumentPreimage x)
    (strongArgument_pos x hx) f hf
  have hs (i : ι) :
      hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) (s i) =
        powerSeriesEvaluation x hx (f i) := by
    rw [HahnSeries.evaluatedPowerSeriesFamily_apply, ← strongArgument_evaluation]
  have hsum := strongSum_hahnEmbedding
    (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) s
  rw [show s.hsum = HahnSeries.evaluate (strongArgumentPreimage x)
    (strongArgument_pos x hx) (HahnSeries.powerSeriesSum f) from
      (HahnSeries.evaluate_powerSeriesSum _ _ f hf).symm,
    ← strongArgument_evaluation] at hsum
  simpa only [hs] using hsum.symm

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private abbrev strongArgumentFamily (x : Surcomplex.{u}) : Unit → Surcomplex.{u} := fun _ => x

private abbrev strongArgumentExponents (x : Surcomplex.{u}) :=
  familyWorkspaceExponents (strongArgumentFamily x)

private def strongArgumentInclusion (x : Surcomplex.{u}) :
    strongArgumentExponents x →+ SignSequence.{u} :=
  (strongArgumentExponents x).subtype.toAddMonoidHom

private theorem strongArgumentInclusion_strictMono (x : Surcomplex.{u}) :
    StrictMono (strongArgumentInclusion x) := fun _ _ h => h

private abbrev strongArgumentPreimage (x : Surcomplex.{u}) :
    _root_.HahnSeries (strongArgumentExponents x) ℂ :=
  familyHahnPreimage (strongArgumentFamily x) ()

private theorem strongArgument_spec (x : Surcomplex.{u}) :
    hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x)
      (strongArgumentPreimage x) = x :=
  familyWorkspaceEmbedding_preimage (strongArgumentFamily x) ()

private theorem strongArgument_pos (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    0 < (strongArgumentPreimage x).orderTop := by
  apply (isInfinitesimal_hahnEmbedding_iff (strongArgumentInclusion x)
    (strongArgumentInclusion_strictMono x) _).mp
  simpa only [strongArgument_spec] using hx

private theorem strongArgument_evaluation (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) :
    powerSeriesEvaluation x hx f =
      hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x)
        (HahnSeries.evaluate (strongArgumentPreimage x) (strongArgument_pos x hx) f) := by
  simpa only [strongArgument_spec] using powerSeriesEvaluation_hahnEmbedding
    (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x)
    (strongArgumentPreimage x) (strongArgument_pos x hx) f

/-- Actual evaluation preserves both summability conditions for any source-summable family. -/
theorem stronglySummable_powerSeriesEvaluation {ι : Type v}
    (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (f : ι → PowerSeries ℂ)
    (hf : HahnSeries.PowerSeriesSummable f) :
    StronglySummable (fun i => powerSeriesEvaluation x hx (f i)) := by
  let s := HahnSeries.evaluatedPowerSeriesFamily (strongArgumentPreimage x)
    (strongArgument_pos x hx) f hf
  have hs (i : ι) :
      hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) (s i) =
        powerSeriesEvaluation x hx (f i) := by
    rw [HahnSeries.evaluatedPowerSeriesFamily_apply, ← strongArgument_evaluation]
  simpa only [hs] using stronglySummable_hahnEmbedding
    (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) s

/-- Evaluation of a small coefficient sum is precisely the actual strong sum of its values. -/
theorem powerSeriesEvaluation_powerSeriesSum {ι : Type v} [Small.{u} ι]
    (x : Surcomplex.{u}) (hx : IsInfinitesimal x) (f : ι → PowerSeries ℂ)
    (hf : HahnSeries.PowerSeriesSummable f) :
    powerSeriesEvaluation x hx (HahnSeries.powerSeriesSum f) =
      strongSum (fun i => powerSeriesEvaluation x hx (f i))
        (stronglySummable_powerSeriesEvaluation x hx f hf) := by
  let s := HahnSeries.evaluatedPowerSeriesFamily (strongArgumentPreimage x)
    (strongArgument_pos x hx) f hf
  have hs (i : ι) :
      hahnEmbedding (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) (s i) =
        powerSeriesEvaluation x hx (f i) := by
    rw [HahnSeries.evaluatedPowerSeriesFamily_apply, ← strongArgument_evaluation]
  have hsum := strongSum_hahnEmbedding
    (strongArgumentInclusion x) (strongArgumentInclusion_strictMono x) s
  rw [show s.hsum = HahnSeries.evaluate (strongArgumentPreimage x)
    (strongArgument_pos x hx) (HahnSeries.powerSeriesSum f) from
      (HahnSeries.evaluate_powerSeriesSum _ _ f hf).symm,
    ← strongArgument_evaluation] at hsum
  simpa only [hs] using hsum.symm

end

end Surreal.Surcomplex
