import Surreal.Surcomplex.StrongAlgebra
import Surreal.Surcomplex.PowerSeries
import Surreal.Foundations.SignSequenceStandardPartTopology

/-!
# Conjugation of actual strong sums and formal evaluation

Conjugation acts coordinatewise on canonical strong sums. Consequently it
commutes with admissible formal evaluation after conjugating the ordinary
coefficients. The index universe bound remains explicit for actual sums.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Conjugation preserves actual infinitesimality. -/
theorem infinitesimal_conj {x : Surcomplex.{u}} (hx : IsInfinitesimal x) :
    IsInfinitesimal (conj x) := by
  constructor
  · simpa only [conj_re] using hx.1
  · simpa only [conj_im] using SignSequence.infinitesimal_neg hx.2

/-- Both coordinate summability conditions are invariant under conjugation. -/
theorem StronglySummable.conj {ι : Type v} {f : ι → Surcomplex.{u}}
    (hf : StronglySummable f) : StronglySummable (fun i => Surcomplex.conj (f i)) := by
  rw [stronglySummable_iff_re_im]
  simp only [conj_re, conj_im]
  exact ⟨hf.re, hf.im.neg⟩

/-- Conjugation commutes with every small actual strong sum. -/
theorem strongSum_conj {ι : Type v} [Small.{u} ι] (f : ι → Surcomplex.{u})
    (hf : StronglySummable f) :
    strongSum (fun i => conj (f i)) hf.conj = conj (strongSum f hf) := by
  apply ext
  · simp only [strongSum_re, conj_re]
  · simpa only [strongSum_im, conj_im] using SignSequence.strongSum_neg hf.im

/-- Formal evaluation commutes with conjugating the argument and all coefficients. -/
theorem powerSeriesEvaluation_conj (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) :
    powerSeriesEvaluation (conj x) (infinitesimal_conj hx)
      (PowerSeries.map (starRingEnd ℂ) f) = conj (powerSeriesEvaluation x hx f) := by
  rw [powerSeriesEvaluation_eq_strongSum, powerSeriesEvaluation_eq_strongSum,
    ← strongSum_conj]
  congr 1
  funext n
  simp only [PowerSeries.coeff_map, starRingEnd_apply, ofComplex_conj, map_mul, map_pow]

end
end Surreal.Surcomplex
