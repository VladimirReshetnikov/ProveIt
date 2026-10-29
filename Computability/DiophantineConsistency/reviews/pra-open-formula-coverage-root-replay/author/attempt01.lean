import DiophantineConsistency.PRAOpenFormulaCompiler

/-! Parsing Foundation quantifier-free semisentences into the compiler syntax. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAOpenFormulaCoverage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAOpenFormulaCompiler

def parseFormula : {n : ℕ} → Semisentence language n → Option (OpenFormula n)
  | _, .rel Language.ORing.Rel.eq v => some (.equal (v 0) (v 1))
  | _, .rel Language.ORing.Rel.lt v => some (.less (v 0) (v 1))
  | _, .nrel Language.ORing.Rel.eq v => some (.not (.equal (v 0) (v 1)))
  | _, .nrel Language.ORing.Rel.lt v => some (.not (.less (v 0) (v 1)))
  | _, ⊤ => some .top
  | _, ⊥ => some .bot
  | _, p ⋏ q => do
      let a ← parseFormula p
      let b ← parseFormula q
      some (.and a b)
  | _, p ⋎ q => do
      let a ← parseFormula p
      let b ← parseFormula q
      some (.or a b)
  | _, ∀⁰ _ => none
  | _, ∃⁰ _ => none

theorem parseFormula_open {n : ℕ} (φ : Semisentence language n) (h : φ.Open) :
    ∃ p, parseFormula φ = some p ∧ asFormula p = φ := by
  induction φ using Semiformula.rec' with
  | rel r v =>
      cases r with
      | eq =>
        refine ⟨.equal (v 0) (v 1), rfl, ?_⟩
        simp only [asFormula]
        rw [←Matrix.fun_eq_vec_two v]
      | lt =>
        refine ⟨.less (v 0) (v 1), rfl, ?_⟩
        simp only [asFormula]
        rw [←Matrix.fun_eq_vec_two v]
  | nrel r v =>
      cases r with
      | eq =>
        refine ⟨.not (.equal (v 0) (v 1)), rfl, ?_⟩
        simp only [asFormula, Semiformula.neg_rel]
        rw [←Matrix.fun_eq_vec_two v]
      | lt =>
        refine ⟨.not (.less (v 0) (v 1)), rfl, ?_⟩
        simp only [asFormula, Semiformula.neg_rel]
        rw [←Matrix.fun_eq_vec_two v]
  | top => exact ⟨.top, rfl, rfl⟩
  | bot => exact ⟨.bot, rfl, rfl⟩
  | and p q ihp ihq =>
      have hp : p.Open := by simpa [Semiformula.Open] using h.1
      have hq : q.Open := by simpa [Semiformula.Open] using h.2
      obtain ⟨a, ha, ha'⟩ := ihp hp
      obtain ⟨b, hb, hb'⟩ := ihq hq
      refine ⟨.and a b, ?_, ?_⟩
      · simp [parseFormula, ha, hb]
      · simp [asFormula, ha', hb']
  | or p q ihp ihq =>
      have hp : p.Open := by simpa [Semiformula.Open] using h.1
      have hq : q.Open := by simpa [Semiformula.Open] using h.2
      obtain ⟨a, ha, ha'⟩ := ihp hp
      obtain ⟨b, hb, hb'⟩ := ihq hq
      refine ⟨.or a b, ?_, ?_⟩
      · simp [parseFormula, ha, hb]
      · simp [asFormula, ha', hb']
  | all p ih => simp [Semiformula.Open] at h
  | exs p ih => simp [Semiformula.Open] at h

end DiophantineConsistency.PRAOpenFormulaCoverage
