import DiophantineConsistency.PRAStageTermCompilation
import DiophantineConsistency.HerbrandFixedGoalWeakening
import DiophantineConsistency.HerbrandStageSupport
/-! Apply the coded χ defeat to the scheduled candidate terms. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageChiForcing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFiniteFunctionCodes PRAStageCodedChi PRAStageTermCompilation
  HerbrandParameterizedWitness HerbrandTupleSchedule HerbrandFixedGoalWeakening HerbrandStageSupport

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

/-- If the selected q instance follows from the current existential χ stage,
then a challenge triple falsifies that entire stage. The selected-instance
implication is explicit and must be obtained from contextual selection. -/
theorem modelForceCurrent {r j : ℕ} (pred : Code (r+3*j+3)) (qCode : Code (r+3*j+3))
    (e : ℕ → M)
    (hSelect : ∀ x y w : M,
      (current r j (chiMatrix pred)).Eval ![] (updateChallenges r j e x y w) →
      (chiMatrix pred).Eval
        ![Structure.func (L := language) qCode (Fin.cases x (Fin.cases y
            (Fin.cases w (fun i : Fin (r+3*j) => e i.val)))), w,y,x,
          Semiterm.val ![] e (candidate j 3), Semiterm.val ![] e (candidate j 2),
          Semiterm.val ![] e (candidate j 1), Semiterm.val ![] e (candidate j 0)] e) :
    ∃ x y w, ¬(current r j (chiMatrix pred)).Eval ![] (updateChallenges r j e x y w) := by
  let n := r+3*j
  let cCode := parameterCode n (candidate j 1)
  let baseCode := parameterCode n (candidate j 3)
  let stopCode := parameterCode n (candidate j 2)
  obtain ⟨x,y,w,h⟩ := modelChiDefeat pred cCode baseCode stopCode qCode e
    (Semiterm.val ![] e (candidate j 0))
  refine ⟨x,y,w, ?_⟩
  intro hc
  apply h
  have hh := hSelect x y w hc
  change (chiMatrix pred).Eval _ e at hh
  simpa only [cCode, baseCode, stopCode, n, modelCandidateCode] using hh
end models
end DiophantineConsistency.PRAStageChiForcing
