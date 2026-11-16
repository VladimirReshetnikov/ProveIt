import IPRABridge.Syntax
import IPRADerivations.Core.Semiring

/-! The designated Foundation arithmetic symbols agree with the shared
ConciseIPRA operations at arbitrary terms in the object theory. -/

set_option autoImplicit false

namespace IPRABridge

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open scoped Fm
open DiophantineConsistency.PRAFiniteFunctionCodes (Code)
open DiophantineConsistency.PRALanguage (addCore addCode mulCore mulCode)
open LeanProofs.ConciseIPRA.PTm (app zero succ)
open Syn (var)

/-- A Foundation symbol applied to terms in the ordinary ConciseIPRA language. -/
abbrev translatedApp {n k : ℕ} (f : Code k) (ts : Fin k → PTm n) : PTm n :=
  .app (toConciseCode f) ts

theorem toConcise_addCore : toConciseCode addCore = Sym.add := by
  simp only [addCore, Sym.add, toConciseCode]
  congr 2
  funext i
  fin_cases i
  rfl

private theorem toConcise_swap (f : Code 2) :
    toConciseCode (.comp f (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) =
      .comp (toConciseCode f) ![.proj 1, .proj 0] := rfl

private theorem substTranslatedBinary {n m : ℕ} (σ : Fin n → PTm m) (f : Code 2) (a b : PTm n) :
    Syn.subst σ (translatedApp f ![a, b]) = translatedApp f ![Syn.subst σ a, Syn.subst σ b] := by
  change app _ _ = app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Translating a composition with exchanged projections applies the symbol
to the same two arguments in reverse order. -/
theorem translated_swap (f : Code 2) (a b : PTm n) :
    Γ ⊢[PRAAx] translatedApp (.comp f (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) ![a, b]
      ≐ translatedApp f ![b, a] := by
  change Γ ⊢[PRAAx] app (toConciseCode _) ![a, b] ≐ _
  rw [toConcise_swap]
  refine (PRA.comp _ _ _).eqTrans (congrApp _ ?_)
  intro i
  fin_cases i
  · exact PRA.proj 1 ![a, b]
  · exact PRA.proj 0 ![a, b]

/-- The Foundation addition core is the shared addition symbol. -/
theorem translated_addCore (a b : PTm n) : Γ ⊢[PRAAx] translatedApp addCore ![a, b] ≐ a + b := by
  change Γ ⊢[PRAAx] app (toConciseCode addCore) ![a, b] ≐ _
  rw [toConcise_addCore]
  exact .eqRefl _

/-- The designated Foundation addition agrees with shared addition. -/
theorem translated_addCode (a b : PTm n) : Γ ⊢[PRAAx] translatedApp addCode ![a, b] ≐ a + b :=
  (translated_swap addCore a b).eqTrans ((translated_addCore b a).eqTrans (add_comm b a))

/-- Shared cancellation applied to Foundation's designated addition. -/
theorem translated_addCode_left_cancel {a b c : PTm n}
    (h : Γ ⊢[PRAAx] translatedApp addCode ![a, b] ≐ translatedApp addCode ![a, c]) :
    Γ ⊢[PRAAx] b ≐ c :=
  add_left_cancel ((translated_addCode a b).eqSymm.eqTrans (h.eqTrans (translated_addCode a c)))

private def translatedMulStep : PR 3 :=
  .comp (toConciseCode addCode) ![.proj 1, .proj 2]

private theorem toConcise_mulCore :
    toConciseCode mulCore = .prec (Sym.zeroK 1) translatedMulStep := by
  simp only [mulCore, toConciseCode, Sym.zeroK, translatedMulStep]
  congr 2

private theorem translated_mulCore_zero (b : PTm n) :
    Γ ⊢[PRAAx] translatedApp mulCore ![zero, b] ≐ zero := by
  change Γ ⊢[PRAAx] app (toConciseCode mulCore) ![zero, b] ≐ zero
  rw [toConcise_mulCore]
  exact (PRA.precZero _ _ ![b]).eqTrans (zeroK_eq ![b])

private theorem translated_mulCore_succ (a b : PTm n) :
    Γ ⊢[PRAAx] translatedApp mulCore ![succ a, b] ≐ translatedApp mulCore ![a, b] + b := by
  let args : Fin 3 → PTm n := Fin.cases a (Fin.cases (translatedApp mulCore ![a, b]) ![b])
  have h₁ : Γ ⊢[PRAAx] translatedApp mulCore ![succ a, b] ≐ app translatedMulStep args := by
    simp only [translatedApp, toConcise_mulCore, args]
    exact PRA.precSucc _ _ a ![b]
  have h₂ : Γ ⊢[PRAAx] app translatedMulStep args ≐
      translatedApp addCode ![translatedApp mulCore ![a, b], b] := by
    unfold translatedMulStep
    refine (PRA.comp _ _ _).eqTrans (congrApp _ ?_)
    intro i
    fin_cases i
    · exact PRA.proj 1 args
    · exact PRA.proj 2 args
  exact h₁.eqTrans (h₂.eqTrans (translated_addCode _ _))

private theorem translated_mulCore_variables :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] translatedApp mulCore ![var 0, var 1] ≐ var 0 * var 1 := by
  let p : Fm PTm 2 := translatedApp mulCore ![var 0, var 1] ≐ var 0 * var 1
  change [] ⊢[PRAAx] p
  apply ind p trivial
  · simp only [p, Fm.subst_eq, PTm.subst_mul, substTranslatedBinary, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one]
    exact (translated_mulCore_zero _).eqTrans (zero_mul _).eqSymm
  · simp only [p, Fm.subst_eq, PTm.subst_mul, substTranslatedBinary, Syn.subst_var,
      Syn.repl_zero, repl_one]
    exact (translated_mulCore_succ _ _).eqTrans
      ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (succ_mul _ _).eqSymm)

/-- The Foundation multiplication core agrees with shared multiplication.
The recursion steps use the checked comparison of the designated additions. -/
theorem translated_mulCore (a b : PTm n) : Γ ⊢[PRAAx] translatedApp mulCore ![a, b] ≐ a * b := by
  have h := inst (Γ := Γ) translated_mulCore_variables ![a, b]
  simpa only [Fm.subst_eq, PTm.subst_mul, substTranslatedBinary, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- The designated Foundation multiplication agrees with shared multiplication. -/
theorem translated_mulCode (a b : PTm n) : Γ ⊢[PRAAx] translatedApp mulCode ![a, b] ≐ a * b :=
  (translated_swap mulCore a b).eqTrans ((translated_mulCore b a).eqTrans (mul_comm b a))

end IPRABridge
