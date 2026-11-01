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
  | hrel r v =>
      cases r with
      | eq =>
        refine ⟨.equal (v 0) (v 1), rfl, ?_⟩
        simp only [asFormula]
        rw [←Matrix.fun_eq_vec_two v]
      | lt =>
        refine ⟨.less (v 0) (v 1), rfl, ?_⟩
        simp only [asFormula]
        rw [←Matrix.fun_eq_vec_two v]
  | hnrel r v =>
      cases r with
      | eq =>
        refine ⟨.not (.equal (v 0) (v 1)), rfl, ?_⟩
        simp only [asFormula, Semiformula.neg_rel]
        rw [←Matrix.fun_eq_vec_two v]
      | lt =>
        refine ⟨.not (.less (v 0) (v 1)), rfl, ?_⟩
        simp only [asFormula, Semiformula.neg_rel]
        rw [←Matrix.fun_eq_vec_two v]
  | hverum => exact ⟨.top, rfl, rfl⟩
  | hfalsum => exact ⟨.bot, rfl, rfl⟩
  | hand p q ihp ihq =>
      simp only [Semiformula.Open, Semiformula.qr_and, Nat.max_eq_zero_iff] at h
      have hp : p.Open := h.1
      have hq : q.Open := h.2
      obtain ⟨a, ha, ha'⟩ := ihp hp
      obtain ⟨b, hb, hb'⟩ := ihq hq
      refine ⟨.and a b, ?_, ?_⟩
      · simp [parseFormula, ha, hb]
      · simp [asFormula, ha', hb']
  | hor p q ihp ihq =>
      simp only [Semiformula.Open, Semiformula.qr_or, Nat.max_eq_zero_iff] at h
      have hp : p.Open := h.1
      have hq : q.Open := h.2
      obtain ⟨a, ha, ha'⟩ := ihp hp
      obtain ⟨b, hb, hb'⟩ := ihq hq
      refine ⟨.or a b, ?_, ?_⟩
      · simp [parseFormula, ha, hb]
      · simp [asFormula, ha', hb']
  | hall p ih => simp [Semiformula.Open] at h
  | hexs p ih => simp [Semiformula.Open] at h

/-- The universal closure of equality to one exactly expresses the formula. -/
def characteristicSentence {n : ℕ} (c : Code n) (φ : Semisentence language n) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode c (vars n), applyCode oneCode Fin.elim0]) 🡘 φ)

/-- Conditional on an object-theory equality-bit certificate, every actual
Foundation open semisentence has a fixed PR characteristic code with a
candidate-PRA proof of its universal correctness sentence. -/
theorem PRA_proves_openCharacteristic {n : ℕ} (eqCode : Code 2)
    (hBit : PRA ⊢ eqBitSentence eqCode) (hCorrect : PRA ⊢ eqCorrectSentence eqCode)
    (φ : Semisentence language n) (hOpen : φ.Open) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ characteristicSentence c φ := by
  obtain ⟨p, _, hp⟩ := parseFormula_open φ hOpen
  subst φ
  refine ⟨compileFormula eqCode p, eval_primrec _, ?_⟩
  exact PRA_proves_formulaCorrect eqCode p hBit hCorrect

end DiophantineConsistency.PRAOpenFormulaCoverage
