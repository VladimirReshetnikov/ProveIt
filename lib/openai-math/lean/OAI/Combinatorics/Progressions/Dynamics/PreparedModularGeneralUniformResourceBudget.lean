import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorLateCoarseConsumer

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedModularGeneral_uniform_resource_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P L : ℝ}, 0 ≤ P → P ≤ L → ∀ s : Fin (m + 1),
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) P L
      r.nativeBudget ∈ Set.Icc 0 ((2 * P + C) ^ C) ∧
      r.required ∈ Set.Icc 0 ((P + L + C) ^ C) := by
  let K (s : Fin (m + 1)) := preparedModularGeneralDetectorConstants m s.val
  let A (s : Fin (m + 1)) := Classical.choose
    (exists_preparedModularGeneralDetector_resource_budget (K s) (s.val + 1))
  let B (s : Fin (m + 1)) := Classical.choose
    (exists_preparedModularGeneralDetector_early_native_budget (K s) (s.val + 1))
  let poly : Polynomial ℕ := ∑ s : Fin (m + 1),
    ((Polynomial.X + Polynomial.C (A s)) ^ A s +
      (Polynomial.X + Polynomial.C (B s)) ^ B s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  have stage (T : ℝ) (hT : 0 ≤ T) (s : Fin (m + 1)) :
      (T + A s) ^ A s ≤ (T + C) ^ C ∧ (T + B s) ^ B s ≤ (T + C) ^ C := by
    have hsum : (T + A s) ^ A s + (T + B s) ^ B s ≤
        ∑ t : Fin (m + 1), ((T + A t) ^ A t + (T + B t) ^ B t) :=
      Finset.single_le_sum (f := fun t : Fin (m + 1) =>
        (T + (A t : ℝ)) ^ A t + (T + (B t : ℝ)) ^ B t)
        (fun t _ => by positivity) (Finset.mem_univ s)
    have hall : (∑ t : Fin (m + 1), ((T + A t) ^ A t + (T + B t) ^ B t)) ≤
        (T + C) ^ C := by
      simpa [poly, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using hbound T hT
    have ha : 0 ≤ (T + (A s : ℝ)) ^ A s := by positivity
    have hb : 0 ≤ (T + (B s : ℝ)) ^ B s := by positivity
    constructor <;> linarith only [hsum, hall, ha, hb]
  refine ⟨C, hC, ?_⟩
  intro P L hP hPL s r
  have hearly := (Classical.choose_spec
    (exists_preparedModularGeneralDetector_early_native_budget (K s) (s.val + 1))).2 hP L
  have hlate := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget (K s) (s.val + 1))).2 hP hPL).1
  exact ⟨⟨hearly.2.1.1, hearly.2.1.2.trans (stage (2 * P) (by positivity) s).2⟩,
    ⟨hlate.required.1, hlate.required.2.trans
      (stage (P + L) (add_nonneg hP (hP.trans hPL)) s).1⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
