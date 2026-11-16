import IPRABridge.OrderSymbols
import IPRADerivations.Core.Pairing
import DiophantineConsistency.PRAIsZero

/-! The Foundation zero test has the same object-language meaning as the
ordinary ConciseIPRA equality bit with second argument zero. -/

set_option autoImplicit false

namespace IPRABridge

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (pred)
open DiophantineConsistency.PRALanguage (oneCode)
open DiophantineConsistency.PRAIsZero (isZeroCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem translated_isZero_zero :
    Γ ⊢[PRAAx] translatedApp isZeroCode ![zero] ≐ one := by
  change Γ ⊢[PRAAx] app (.prec (toConciseCode oneCode) (Sym.zeroK 2)) ![zero] ≐ one
  exact (PRA.precZero _ _ Fin.elim0).eqTrans translated_oneCode

private theorem translated_isZero_succ (a : PTm n) :
    Γ ⊢[PRAAx] translatedApp isZeroCode ![succ a] ≐ zero := by
  change Γ ⊢[PRAAx] app (.prec (toConciseCode oneCode) (Sym.zeroK 2)) ![succ a] ≐ zero
  exact (PRA.precSucc _ _ a Fin.elim0).eqTrans (zeroK_eq _)

private theorem congrTranslatedIsZero {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] translatedApp isZeroCode ![a] ≐ translatedApp isZeroCode ![b] := by
  apply congrApp
  intro i
  fin_cases i
  exact h

/-- The comparison holds at an arbitrary term and in any proof context. -/
theorem translated_isZeroCode (a : PTm n) :
    Γ ⊢[PRAAx] translatedApp isZeroCode ![a] ≐ eqb a zero := by
  refine .orE (zero_or_succ a) ?_ ?_
  · exact (congrTranslatedIsZero Prf.hyp0).eqTrans
      (translated_isZero_zero.eqTrans (eqb_of_eq Prf.hyp0).eqSymm)
  · have hne : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] neg (a ≐ zero) :=
      .impI (succ_ne_zero (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))
    exact (congrTranslatedIsZero Prf.hyp0).eqTrans
      ((translated_isZero_succ (pred a)).eqTrans (eqb_of_ne hne).eqSymm)

end IPRABridge
