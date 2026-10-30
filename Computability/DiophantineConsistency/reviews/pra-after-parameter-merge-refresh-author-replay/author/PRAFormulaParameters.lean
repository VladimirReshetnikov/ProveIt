import DiophantineConsistency.PRAEqualityCode

/-! Pack the finitely many free parameters of a syntactic formula as bound arguments. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFormulaParameters
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAOpenFormulaCoverage PRAEqualityCode

/-- Fixing all parameters below an upper bound leaves no free variables. -/
theorem fixed_no_free_of_le {n : ℕ} (φ : Semiproposition language n)
    (r : ℕ) (hr : φ.fvSup ≤ r) :
    (Rew.fixitr n r ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  rw [Rew.eq_bind (Rew.fixitr n r)]
  simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk]
  intro h
  rcases Semiformula.fvar?_rew h with (⟨z,hz⟩ | ⟨z,hz,hx⟩)
  · simp at hz
  · have hz' : z < r := lt_of_lt_of_le (Semiformula.lt_fvSup_of_fvar? hz) hr
    simp [hz'] at hx

private theorem fixed_no_free {n : ℕ} (φ : Semiproposition language n) :
    (Rew.fixitr n φ.fvSup ▹ φ).freeVariables = ∅ :=
  fixed_no_free_of_le φ φ.fvSup le_rfl

def packParameters {n : ℕ} (φ : Semiproposition language n) :
    Semisentence language (n + φ.fvSup) :=
  (Rew.fixitr n φ.fvSup ▹ φ).toEmpty (fixed_no_free φ)

theorem packParameters_emb {n : ℕ} (φ : Semiproposition language n) :
    (Rewriting.emb (packParameters φ) : Semiproposition language (n + φ.fvSup)) =
      Rew.fixitr n φ.fvSup ▹ φ := by
  simp [packParameters]

theorem qr_rew {ξ η : Type} {n m : ℕ} (φ : Semiformula language ξ n)
    (w : Rew language ξ n η m) : (w ▹ φ).qr = φ.qr := by
  induction φ using Semiformula.rec' generalizing η m with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rfl
  | hnrel r v => rfl
  | hand p q ihp ihq => simp [ihp, ihq]
  | hor p q ihp ihq => simp [ihp, ihq]
  | hall p ih => simp [ih]
  | hexs p ih => simp [ih]

/-- Fixing free parameters preserves an open formula. -/
theorem fixed_pack_open {n : ℕ} (φ : Semiproposition language n)
    (r : ℕ) (hr : φ.fvSup ≤ r) (h : φ.Open) :
    ((Rew.fixitr n r ▹ φ).toEmpty (fixed_no_free_of_le φ r hr)).Open := by
  let packed := (Rew.fixitr n r ▹ φ).toEmpty (fixed_no_free_of_le φ r hr)
  have he : (Rewriting.emb packed : Semiproposition language (n+r)) = Rew.fixitr n r ▹ φ := by
    simp [packed]
  have hq := congrArg Semiformula.qr he
  have hb : (Rewriting.emb packed : Semiproposition language _).qr = packed.qr :=
    qr_rew packed (Rew.emb : Rew language Empty _ ℕ _)
  rw [hb, qr_rew] at hq
  exact hq.trans h

theorem packParameters_open {n : ℕ} (φ : Semiproposition language n) (h : φ.Open) :
    (packParameters φ).Open := by
  exact fixed_pack_open φ φ.fvSup le_rfl h

/-- Evaluation of a formula whose free parameters are fixed below a bound. -/
theorem fixed_pack_eval {M : Type} [Structure language M] {n : ℕ}
    (φ : Semiproposition language n) (r : ℕ) (hr : φ.fvSup ≤ r)
    (v : Fin (n+r) → M) (fallback : ℕ → M) :
    ((Rew.fixitr n r ▹ φ).toEmpty (fixed_no_free_of_le φ r hr)).Eval v Empty.elim ↔
      φ.Eval (fun i => v (i.castAdd r))
        (fun i => if hi : i < r then v (Fin.natAdd n ⟨i,hi⟩) else fallback (i-r)) := by
  rw [←Semiformula.eval_toEmpty (f := fallback) (fixed_no_free_of_le φ r hr)]
  rw [Semiformula.eval_rew]
  simp only [Function.comp_def, Rew.fixitr_bvar, Semiterm.val_bvar, Rew.fixitr_fvar]
  have heq : (fun i => Semiterm.val v fallback
      (if hi : i < r then (#(Fin.natAdd n ⟨i,hi⟩) : SyntacticSemiterm language (n+r)) else &(i-r))) =
      (fun i => if hi : i < r then v (Fin.natAdd n ⟨i,hi⟩) else fallback (i-r)) := by
    funext i
    split <;> rfl
  rw [heq]

/-- Packed arguments evaluate as the original bound variables followed by the
free parameters occurring below the formula's finite free-variable bound. -/
theorem packParameters_eval {M : Type} [Structure language M] {n : ℕ}
    (φ : Semiproposition language n) (v : Fin (n + φ.fvSup) → M) (fallback : ℕ → M) :
    (packParameters φ).Eval v Empty.elim ↔
      φ.Eval (fun i => v (i.castAdd φ.fvSup))
        (fun i => if hi : i < φ.fvSup then v (Fin.natAdd n ⟨i,hi⟩) else fallback (i - φ.fvSup)) := by
  exact fixed_pack_eval φ φ.fvSup le_rfl v fallback

/-- Every open formula with free numerical parameters has, after their explicit
packing into bound argument positions, a certified PR characteristic. -/
theorem PRA_proves_packedOpenCharacteristic {n : ℕ} (φ : Semiproposition language n)
    (h : φ.Open) :
    ∃ c : Code (n + φ.fvSup), Primrec (eval c) ∧
      PRA ⊢ characteristicSentence c (packParameters φ) :=
  PRAEqualityCode.PRA_proves_openCharacteristic (packParameters φ) (packParameters_open φ h)

end DiophantineConsistency.PRAFormulaParameters
