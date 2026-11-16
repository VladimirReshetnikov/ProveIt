/-!
Object-theory scaffold for ProveIt/ConciseIPRA.

Place this file under the ProveIt Lean source path (or add that path to Lake).
The `axiom` declarations are named obligations, not completed proofs.  Their
purpose is to make the intended theorem types and final transfer step explicit.
-/
import ConciseIPRA.BiInterpretation
import ConciseIPRA.TeqRec

namespace LeanProofs.ConciseIPRA.NumberTheory

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Intended PR symbol for Euler's totient. -/
axiom phiPR : PR 1

/-- Intended PR symbol for a bounded divisor sum of `phiPR`. -/
axiom sumDivPhiPR : PR 1

/-- Intended object formula `sum_{d | n} phi(d) = n`. -/
axiom sumPhiFormula : Fm PTm 1

/-- Main ordinary-iPRA obligation for the divisor-sum theorem. -/
axiom sumPhi_pra :
  ([] : List (Fm PTm 1)) ⊢[PRAAx] sumPhiFormula

/-- Faithful transfer into the concise scalar theory. -/
theorem sumPhi_teq :
    ([] : List (Fm Tm 1)) ⊢[TeqAx]
      sumPhiFormula.map (fun _ => FromPRA.sigma) :=
  (pra_theorem_iff sumPhiFormula).mp sumPhi_pra

/-- Intended PR symbol for a completely additive prime weight `L_w`.
The first argument is a code/parameter for the weight in the eventual module. -/
axiom weightedLogPR : PR 2

/-- Intended PR symbol for weighted von Mangoldt. -/
axiom weightedMangoldtPR : PR 2

/-- Representative object formula for the weighted divisor sum. -/
axiom mangoldtDivisorFormula : Fm PTm 2

/-- Ordinary-iPRA proof obligation. -/
axiom mangoldtDivisor_pra :
  ([] : List (Fm PTm 2)) ⊢[PRAAx] mangoldtDivisorFormula

/-- Transfer endpoint for the weighted Mangoldt divisor sum. -/
theorem mangoldtDivisor_teq :
    ([] : List (Fm Tm 2)) ⊢[TeqAx]
      mangoldtDivisorFormula.map (fun _ => FromPRA.sigma) :=
  (pra_theorem_iff mangoldtDivisorFormula).mp mangoldtDivisor_pra

end LeanProofs.ConciseIPRA.NumberTheory
