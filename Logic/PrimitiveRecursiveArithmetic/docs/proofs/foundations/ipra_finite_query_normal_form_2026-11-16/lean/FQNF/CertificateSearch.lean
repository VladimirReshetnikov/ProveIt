import IPRADerivations.Core.Search
import FQNF.KernelCore

/-!
# Least bounded certificate selection

This file states the arithmetic bridge from a reflected Boolean verifier to an
explicit least certificate.  It is the main missing reusable lemma identified
by the repository audit.
-/

namespace LeanProofs.IPRA.FQNF

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : Nat} {Gamma : List (Fm PTm n)}

/-- The verifier is written as a two-variable term: certificate first, packed
query second.  It returns `1` on success and `0` on failure. -/
def failureBody (check : PTm 2) : PTm 2 :=
  monus (succ zero) check

/-- The least certificate below `bound` accepted by `check`. -/
def selectT (check : PTm 2) (bound query : PTm n) : PTm n :=
  Search.mu (failureBody check) bound query

/-- Booleanity of a checker, expressed at arbitrary arguments. -/
def BooleanChecker (check : PTm 2) : Fm PTm 2 :=
  (check ≐ zero) ⋎ (check ≐ succ zero)

/-- A successful explicit witness yields a successful least selected code.

The proof is a short specialization of `Search.search_found`: success implies
`failureBody = 0`; search returns a zero no later than the witness; Booleanity
converts `failureBody = 0` back to `check = 1`. -/
theorem select_of_witness
    (check : PTm 2) {bound query witness : PTm n}
    (hbool : Gamma ⊢[PRAAx]
      (Syn.subst ![witness, query] (BooleanChecker check)))
    (hbound : Gamma ⊢[PRAAx] lt witness bound)
    (hgood : Gamma ⊢[PRAAx]
      inst2 check witness query ≐ succ zero) :
    Gamma ⊢[PRAAx]
      lt (selectT check bound query) bound ⋏
      ((inst2 check (selectT check bound query) query ≐ succ zero) ⋏
       le (selectT check bound query) witness) := by
  sorry

/-- Existential producer form.  The conclusion is independent of the unknown
witness, so intuitionistic existential elimination is sufficient; no choice
principle is used. -/
theorem select_of_exists
    (check : PTm 2) (bound query : PTm n)
    (hbool : Gamma ⊢[PRAAx]
      Fm.all (BooleanChecker check).subst ![var 0, Syn.shift query])
    (hexists : Gamma ⊢[PRAAx]
      Fm.ex (lt (var 0) (Syn.shift bound) ⋏
        (inst2 check (var 0) (Syn.shift query) ≐ succ zero))) :
    Gamma ⊢[PRAAx]
      lt (selectT check bound query) bound ⋏
      (inst2 check (selectT check bound query) query ≐ succ zero) := by
  sorry

/-- Generic terminal extraction after selection. -/
theorem compile_selected_certificate
    (check : PTm 2) (bound query : PTm n) (Goal : Fm PTm n)
    (hselected : Gamma ⊢[PRAAx]
      lt (selectT check bound query) bound ⋏
      (inst2 check (selectT check bound query) query ≐ succ zero))
    (hextract : Gamma ⊢[PRAAx]
      ((inst2 check (selectT check bound query) query ≐ succ zero) ⟶ Goal)) :
    Gamma ⊢[PRAAx] Goal :=
  Prf.impE hextract (Prf.andE₂ hselected)

end LeanProofs.IPRA.FQNF
