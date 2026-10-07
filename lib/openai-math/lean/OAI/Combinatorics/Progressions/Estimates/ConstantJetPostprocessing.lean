/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Probability.RandomCoefficientMassComparison

namespace OAI

section

namespace Erdos3

theorem booleanConstantJet_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α)
    (constant : Ω → D → ℝ) (hc : ∀ d, Measurable (fun a => constant a d)) :
    Measurable (fun a => booleanConstantJet sets (constant a)) := by
  apply Measurable.of_eval
  intro o
  by_cases hs : sets o.1 o.2 = ∅
  · simpa only [booleanConstantJet, hs, ite_true] using hc o.1
  · simpa only [booleanConstantJet, hs, ite_false] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))

theorem constantJet_postprocess_measurable {Ω D α Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [Fintype D] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    (constant : Ω → D → ℝ) (hc : ∀ d, Measurable (fun a => constant a d))
    (P : Ω × ((Σ d, O d) → ℝ) → Y) (hP : Measurable P) :
    Measurable (fun p : Ω × ((Σ d, O d) → ℝ) =>
      P (p.1, booleanConstantJet sets (constant p.1) + p.2)) :=
  hP.comp (measurable_fst.prodMk
    (((booleanConstantJet_measurable_comp sets constant hc).comp measurable_fst).add measurable_snd))

end Erdos3

end

end OAI
