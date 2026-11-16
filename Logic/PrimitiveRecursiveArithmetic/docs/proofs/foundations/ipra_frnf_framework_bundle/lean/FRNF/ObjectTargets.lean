import IPRADerivations.Core.Search
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.BoundedSums
import FRNF.Kernel

/-!
# Object-language implementation targets for FRNF

This file is an explicit roadmap, not a completed formalization.  Every `sorry`
below names a mathematical obligation discussed and proved informally in the
paper.  The intended endpoint of each theorem is an actual `Prf PRAAx` value.
No theorem in this file should be advertised as kernel checked until the
placeholders are removed and the root axiom audit succeeds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.FRNF

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

/-- Bounded formulas before Boolean compilation. -/
inductive BForm : Nat → Type
  | eq {n} (s t : PTm n) : BForm n
  | bot {n} : BForm n
  | and {n} (A B : BForm n) : BForm n
  | or {n} (A B : BForm n) : BForm n
  | imp {n} (A B : BForm n) : BForm n
  | allLt {n} (bound : PTm n) (body : BForm (n + 1)) : BForm n
  | exLt {n} (bound : PTm n) (body : BForm (n + 1)) : BForm n

/-- Reification of a bounded formula into the existing first-order syntax. -/
opaque BForm.toFm {n : Nat} : BForm n → Fm PTm n

/-- Primitive-recursive characteristic symbol generated structurally. -/
opaque BForm.char {n : Nat} : BForm n → PR n

/-- Characteristic term at the free variables. -/
def BForm.charTm {n : Nat} (A : BForm n) : PTm n :=
  app A.char var

/-- Truth of the characteristic equation implies the bounded formula. -/
theorem BForm.ofChar {n : Nat} (A : BForm n) :
    [A.charTm ≐ succ zero] ⊢[PRAAx] A.toFm := by
  sorry

/-- A bounded formula proves its characteristic equation. -/
theorem BForm.toChar {n : Nat} (A : BForm n) :
    [A.toFm] ⊢[PRAAx] A.charTm ≐ succ zero := by
  sorry

/-- The generated characteristic term is Boolean-valued. -/
theorem BForm.boolean {n : Nat} (A : BForm n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      (A.charTm ≐ zero) ⋎ (A.charTm ≐ succ zero) := by
  sorry

/--
An encoded table supports length, lookup, update and bounded folds.  The
implementation should reuse `pairT`, `fstT`, `sndT`, and simultaneous recursion.
-/
structure TableSymbols where
  len : PR 1
  get : PR 2
  set : PR 3
  foldMax : PR 2

/-- Correctness package for encoded finite tables. -/
structure TableCertificate (T : TableSymbols) where
  getSetSame : ∀ {n : Nat} (tab i value : PTm n),
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      app T.get ![app T.set ![tab, i, value], i] ≐ value
  getSetOther : ∀ {n : Nat} (tab i j value : PTm n),
    [neg (i ≐ j)] ⊢[PRAAx]
      app T.get ![app T.set ![tab, i, value], j] ≐ app T.get ![tab, j]

/-- Closed object formulas generated after fixing the concrete symbols. -/
opaque demandClosureFormula : Fm PTm 0
opaque backwardViabilityFormula : Fm PTm 0
opaque stableCloudFormula : Fm PTm 0
opaque finiteNetMinimumFormula : Fm PTm 0
opaque guardedReciprocalFormula : Fm PTm 0

/-- Object theorem for the reverse acyclic demand pass. -/
theorem demandClosure_correct :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] demandClosureFormula := by
  sorry

/-- Object theorem for backward viability on a finite layered relation. -/
theorem backwardViability_correct :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] backwardViabilityFormula := by
  sorry

/-- Stable-observer theorem for a candidate cloud with a diameter bound. -/
theorem stableCloud_correct :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] stableCloudFormula := by
  sorry

/-- Finite-net minimum with explicit coverage and continuity moduli. -/
theorem finiteNetMinimum_correct :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] finiteNetMinimumFormula := by
  sorry

/-- Guarded reciprocal with a supplied positive rational lower bound. -/
theorem guardedReciprocal_correct :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] guardedReciprocalFormula := by
  sorry

end LeanProofs.IPRA.FRNF
