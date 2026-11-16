import ConciseIPRA.NativeBiInterpretation

/-!
# Explicit object-language destination

STATUS: uncompiled integration outline, requiring the ProveIt workspace pinned
in README.md. This file does not import RationalGeometry to pretend that a host
Rat theorem is an iPRA derivation. The missing work is the concrete compilation
of its finite arithmetic into PR terms and the construction of main_derivation.

An input code contains five rational codes [m,a,q,r,x]. The guard rejects
malformed codes and tests Sigma*Delta*(1-x*x) != 0. residualsZero tests all
Einstein--Maxwell residuals at that input, using the fixed rational formulas.
All operations are totalized on invalid data, which are excluded by the guard.
-/

namespace KNIPRA.ObjectTarget

open LeanProofs.ConciseIPRA
open LeanProofs.ConciseIPRA.Syn

/-- Slots to be filled by concrete terms built from PR.zero/succ/proj/comp/prec.
The slots are explicit; no semantic compiler or universal PR interpreter is assumed. -/
structure ArithmeticSymbols where
  regularInput : PR 1
  residualsZero : PR 1

def one {n : Nat} : PTm n := PTm.succ PTm.zero

def call (f : PR 1) (t : PTm n) : PTm n := PTm.app f (fun _ => t)

def openStatement (s : ArithmeticSymbols) : Fm PTm 1 :=
  .imp (.eq (call s.regularInput (PTm.var 0)) one)
       (.eq (call s.residualsZero (PTm.var 0)) one)

def statement (s : ArithmeticSymbols) : Fm PTm 0 := .all (openStatement s)

/-- The actual endpoint required for an object-theory formalization. -/
def MainDerivationGoal (s : ArithmeticSymbols) : Prop :=
  Prf PRAAx [] (statement s)

/-- Once the missing object proof is constructed, the repository's checked
bridge transports it. This theorem assumes, rather than supplies, that proof. -/
theorem native_of_main (s : ArithmeticSymbols) (h : MainDerivationGoal s) :
    NPrf [] (NFm.ofPRA (statement s)) := by
  exact (pra_iff_native (Γ := []) (φ := statement s)).mp h

end KNIPRA.ObjectTarget
