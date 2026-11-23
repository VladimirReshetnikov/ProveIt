import IPRADerivations.Core.Fubini
import IPRADerivations.Core.Division
import IPRADerivations.Core.Powers

/-!
Directed multiplicity matrices in the ProveIt object language.
The three free input terms are the matrix width, numeral base and packed
digits. At width N and base B >= 2, the digit at i*N+j is the number of
arcs i -> j. The sum exchange itself works for any base. The open and
closed endpoints are derivability statements in PRAAx.
-/

namespace LeanProofs.IPRA.GraphIncidence

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The single parameter expected by the finite-sum body. -/
def pack (width base digits : PTm n) : PTm n :=
  pairT width (pairT base digits)

def readEntry (i j z : PTm n) : PTm n :=
  let width := fstT z
  let base := fstT (sndT z)
  let digits := sndT (sndT z)
  rem (quo digits (pw base (i * width + j))) base

/-- Slots 0 and 1 are the row and column; slot 2 carries all input data. -/
def adjacencyBody : PTm 3 := readEntry (var 0) (var 1) (var 2)

/-- Removing the pair projections is an equality derived in the object theory. -/
theorem readEntry_pack (i j width base digits : PTm n) :
    Γ ⊢[PRAAx] readEntry i j (pack width base digits) ≐
      rem (quo digits (pw base (i * width + j))) base := by
  have hW : Γ ⊢[PRAAx] fstT (pack width base digits) ≐ width :=
    fst_pair _ _
  have hR : Γ ⊢[PRAAx] sndT (pack width base digits) ≐ pairT base digits :=
    snd_pair _ _
  have hB := (congrFst hR).eqTrans (fst_pair _ _)
  have hD := (congrSnd hR).eqTrans (snd_pair _ _)
  have hIndex := congrAdd (congrMul (Prf.eqRefl i) hW) (Prf.eqRefl j)
  -- powF reads the exponent first, although pw takes the base first.
  exact congrAp2 remF
    (congrAp2 quoF hD (congrAp2 powF hIndex hB)) hB

def totalOut (width base digits : PTm n) : PTm n :=
  ap2 (sumF (oB adjacencyBody)) width (pairT width (pack width base digits))

def totalIn (width base digits : PTm n) : PTm n :=
  ap2 (sumF (pB adjacencyBody)) width (pairT width (pack width base digits))

/-- Sum of row degrees equals sum of column degrees in the object theory. -/
theorem totalOut_eq_totalIn (width base digits : PTm n) :
    Γ ⊢[PRAAx] totalOut width base digits ≐ totalIn width base digits :=
  fubini adjacencyBody width width (pack width base digits)

abbrev incidenceFormula : Fm PTm 3 :=
  totalOut (var 0) (var 1) (var 2) ≐ totalIn (var 0) (var 1) (var 2)

theorem incidence_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] incidenceFormula :=
  totalOut_eq_totalIn (var 0) (var 1) (var 2)

theorem incidence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 incidenceFormula :=
  closeUniv 3 incidence_open

end LeanProofs.IPRA.GraphIncidence
