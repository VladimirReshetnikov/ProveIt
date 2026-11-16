import IPRABridge.ArithmeticSymbols
import IPRADerivations.Core.Order
import DiophantineConsistency.PRATheory

/-! The characteristic function for Foundation's strict order and the ordinary
ConciseIPRA order formula agree at arbitrary terms. -/

set_option autoImplicit false

namespace IPRABridge

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (monus pred)
open DiophantineConsistency.PRAFiniteFunctionCodes (Code)
open DiophantineConsistency.PRALanguage (oneCode)
open DiophantineConsistency.PRATheory (predCode subCore subCode nonzeroCode ltBitCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The Foundation numeral one denotes the successor of zero. -/
theorem translated_oneCode :
    Γ ⊢[PRAAx] translatedApp oneCode Fin.elim0 ≐ succ zero := by
  change Γ ⊢[PRAAx] app (.comp .succ ![PR.zero]) Fin.elim0 ≐ succ zero
  refine (PRA.comp _ _ _).eqTrans (congrApp .succ ?_)
  intro i
  fin_cases i
  exact .eqRefl _

/-- Foundation's predecessor is the shared predecessor. -/
theorem translated_predCode (a : PTm n) :
    Γ ⊢[PRAAx] translatedApp predCode ![a] ≐ pred a :=
  .eqRefl _

/-- The Foundation subtraction core recurses on its first argument. -/
theorem translated_subCore (a b : PTm n) :
    Γ ⊢[PRAAx] translatedApp subCore ![a, b] ≐ monus b a :=
  .eqRefl _

/-- The designated Foundation subtraction agrees with shared truncated
subtraction in the usual argument order. -/
theorem translated_subCode (a b : PTm n) :
    Γ ⊢[PRAAx] translatedApp subCode ![a, b] ≐ monus a b :=
  (translated_swap subCore a b).eqTrans (translated_subCore b a)

private def nonzeroStep : PR 2 := .comp .succ ![Sym.zeroK 2]

private theorem translated_nonzero_zero :
    Γ ⊢[PRAAx] translatedApp nonzeroCode ![zero] ≐ zero := by
  change Γ ⊢[PRAAx] app (.prec .zero nonzeroStep) ![zero] ≐ zero
  exact PRA.precZero .zero nonzeroStep Fin.elim0

private theorem translated_nonzero_succ (a : PTm n) :
    Γ ⊢[PRAAx] translatedApp nonzeroCode ![succ a] ≐ succ zero := by
  let args : Fin 2 → PTm n := Fin.cases a
    (Fin.cases (translatedApp nonzeroCode ![a]) Fin.elim0)
  have h : Γ ⊢[PRAAx] translatedApp nonzeroCode ![succ a] ≐ app nonzeroStep args := by
    change Γ ⊢[PRAAx] app (.prec .zero nonzeroStep) ![succ a] ≐ app nonzeroStep args
    exact PRA.precSucc .zero nonzeroStep a Fin.elim0
  refine h.eqTrans ((PRA.comp .succ ![Sym.zeroK 2] args).eqTrans (congrApp .succ ?_))
  intro i
  fin_cases i
  exact zeroK_eq args

private theorem congrTranslatedNonzero {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] translatedApp nonzeroCode ![a] ≐ translatedApp nonzeroCode ![b] := by
  apply congrApp
  intro i
  fin_cases i
  exact h

private def swappedSubCode : Code 2 :=
  .comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))

private theorem translated_ltBitCode_monus (a b : PTm n) :
    Γ ⊢[PRAAx] translatedApp ltBitCode ![a, b] ≐ translatedApp nonzeroCode ![monus b a] := by
  have h : Γ ⊢[PRAAx] translatedApp ltBitCode ![a, b] ≐
      translatedApp nonzeroCode ![translatedApp swappedSubCode ![a, b]] := by
    change Γ ⊢[PRAAx] app (.comp (toConciseCode nonzeroCode) ![toConciseCode swappedSubCode])
      ![a, b] ≐ _
    refine (PRA.comp _ _ _).eqTrans (congrApp _ ?_)
    intro i
    fin_cases i
    exact .eqRefl _
  exact h.eqTrans (congrTranslatedNonzero ((translated_swap subCode a b).eqTrans (translated_subCode b a)))

/-- Testing Foundation's order bit for one is equivalent to shared strict
order as an object-theory biconditional. -/
theorem translated_ltBitCode (a b : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (translatedApp ltBitCode ![a, b] ≐ translatedApp oneCode Fin.elim0)
      (lt a b) := by
  apply Prf.iffI <;> apply Prf.impI
  · refine .orE (lt_or_le a b) Prf.hyp0 ?_
    refine succ_ne_zero' (a := zero) _ ?_
    exact translated_oneCode.eqSymm.eqTrans (Prf.hyp1.eqSymm.eqTrans
      ((translated_ltBitCode_monus a b).eqTrans
        ((congrTranslatedNonzero Prf.hyp0).eqTrans translated_nonzero_zero)))
  · refine .orE (zero_or_succ (monus b a)) ?_ ?_
    · exact le_lt_absurd (a := b) (b := a) _ Prf.hyp0 Prf.hyp1
    · exact (translated_ltBitCode_monus a b).eqTrans
        ((congrTranslatedNonzero Prf.hyp0).eqTrans
          ((translated_nonzero_succ _).eqTrans translated_oneCode.eqSymm))

/-- Equal arguments never make the Foundation strict-order bit one. -/
theorem translated_ltBitCode_irrefl (a : PTm n) :
    Γ ⊢[PRAAx] neg (translatedApp ltBitCode ![a, a] ≐ translatedApp oneCode Fin.elim0) :=
  .impI (lt_irrefl a _ ((translated_ltBitCode a a).iffMp Prf.hyp0))

/-- No argument lies strictly below zero. -/
theorem translated_ltBitCode_below_zero (a : PTm n) :
    Γ ⊢[PRAAx] neg (translatedApp ltBitCode ![a, zero] ≐ translatedApp oneCode Fin.elim0) :=
  .impI (le_lt_absurd _ (zero_le a) ((translated_ltBitCode a zero).iffMp Prf.hyp0))

/-- Zero lies strictly below every successor. -/
theorem translated_ltBitCode_zero_succ (a : PTm n) :
    Γ ⊢[PRAAx] translatedApp ltBitCode ![zero, succ a] ≐ translatedApp oneCode Fin.elim0 :=
  (translated_ltBitCode zero (succ a)).iffMpr ((succ_monus_succ zero a).eqTrans (zero_monus a))

end IPRABridge
