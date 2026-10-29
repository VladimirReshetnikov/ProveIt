import DiophantineConsistency.PRAEqualityCode

/-! Pack the finitely many free parameters of a syntactic formula as bound arguments. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFormulaParameters
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAOpenFormulaCoverage PRAEqualityCode

private theorem fixed_no_free {n : ℕ} (φ : Semiproposition language n) :
    (Rew.fixitr n φ.fvSup ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  rw [Rew.eq_bind (Rew.fixitr n φ.fvSup)]
  simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk]
  intro h
  rcases Semiformula.fvar?_rew h with (⟨z,hz⟩ | ⟨z,hz,hx⟩)
  · simp at hz
  · have hz' : z < φ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
    simp [hz'] at hx

def packParameters {n : ℕ} (φ : Semiproposition language n) :
    Semisentence language (n + φ.fvSup) :=
  (Rew.fixitr n φ.fvSup ▹ φ).toEmpty (fixed_no_free φ)

theorem packParameters_emb {n : ℕ} (φ : Semiproposition language n) :
    (Rewriting.emb (packParameters φ) : Semiproposition language (n + φ.fvSup)) =
      Rew.fixitr n φ.fvSup ▹ φ := by
  simp [packParameters]

theorem qr_rew {n m : ℕ} (φ : Semiproposition language n) (w : SyntacticRew language n m) :
    (w ▹ φ).qr = φ.qr := by
  induction φ using Semiformula.rec' generalizing m with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand p q ihp ihq => simp [ihp, ihq]
  | hor p q ihp ihq => simp [ihp, ihq]
  | hall p ih => simp [ih]
  | hexs p ih => simp [ih]

theorem packParameters_open {n : ℕ} (φ : Semiproposition language n) (h : φ.Open) :
    (packParameters φ).Open := by
  have he := packParameters_emb φ
  have hq := congrArg Semiformula.qr he
  have hb : (Rewriting.emb (packParameters φ) : Semiproposition language (n + φ.fvSup)).qr =
      (packParameters φ).qr := by
    sorry
  rw [hb, qr_rew] at hq
  exact hq.trans h

/-- Every open formula with free numerical parameters has, after their explicit
packing into bound argument positions, a certified PR characteristic. -/
theorem PRA_proves_packedOpenCharacteristic {n : ℕ} (φ : Semiproposition language n)
    (h : φ.Open) :
    ∃ c : Code (n + φ.fvSup), Primrec (eval c) ∧
      PRA ⊢ characteristicSentence c (packParameters φ) :=
  PRAEqualityCode.PRA_proves_openCharacteristic (packParameters φ) (packParameters_open φ h)

end DiophantineConsistency.PRAFormulaParameters
