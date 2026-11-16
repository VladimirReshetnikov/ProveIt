import IPRADerivations.Core.Search
import STRIVE.MixedRadix

/-!
# STRIVE-iPRA: interface for one specialized bounded formula

The metalevel compiler emits one value symbol, two code bounds, two checkers,
and canonical positive/negative code terms.  This file states the exact
object-theory package expected from that generated module.  It avoids an
object-language universal formula evaluator: every instance is a fixed
specialization.
-/

namespace LeanProofs.IPRA.STRIVE

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ}

/-- Instantiate a certificate-indexed term at an outer-scope certificate. -/
def atCert (t : PTm (n + 1)) (c : PTm n) : PTm n := Syn.subst (inst c) t

/-- Proof-producing result of compiling one fixed bounded formula. -/
structure CompiledFormula (n : ℕ) where
  meaning : Fm PTm n
  value : PTm n
  positiveBound : PTm n
  negativeBound : PTm n
  positiveCheck : PTm (n + 1)
  negativeCheck : PTm (n + 1)
  canonicalPositive : PTm n
  canonicalNegative : PTm n

  valueBoolean : ([] : List (Fm PTm n)) ⊢[PRAAx]
    (value ≐ zero) ⋎ (value ≐ succ zero)
  valueCorrect : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Fm.iff (value ≐ succ zero) meaning

  positiveSound : [positiveCheck ≐ succ zero] ⊢[PRAAx] meaning.shift
  negativeSound : [negativeCheck ≐ succ zero] ⊢[PRAAx] Fm.neg meaning.shift
  positiveCodeBound : [positiveCheck ≐ succ zero] ⊢[PRAAx]
    lt (var 0) positiveBound.shift
  negativeCodeBound : [negativeCheck ≐ succ zero] ⊢[PRAAx]
    lt (var 0) negativeBound.shift

  canonicalPositiveAccepted : ([] : List (Fm PTm n)) ⊢[PRAAx]
    (value ≐ succ zero) ⟶
      (atCert positiveCheck canonicalPositive ≐ succ zero)
  canonicalNegativeAccepted : ([] : List (Fm PTm n)) ⊢[PRAAx]
    (value ≐ zero) ⟶
      (atCert negativeCheck canonicalNegative ≐ succ zero)

namespace CompiledFormula

/-- A checked positive code gives the public formula. -/
theorem ofPositiveCheck (C : CompiledFormula n) {Γ : List (Fm PTm n)} {c : PTm n}
    (h : Γ ⊢[PRAAx] atCert C.positiveCheck c ≐ succ zero) :
    Γ ⊢[PRAAx] C.meaning := by
  -- Specialize `positiveSound` at `c`, then discharge its one hypothesis.
  have hs := C.positiveSound.subst (inst c)
  simpa [atCert] using Prf.impE (Prf.impI hs) h

/-- A checked negative code gives the intuitionistic negation. -/
theorem ofNegativeCheck (C : CompiledFormula n) {Γ : List (Fm PTm n)} {c : PTm n}
    (h : Γ ⊢[PRAAx] atCert C.negativeCheck c ≐ succ zero) :
    Γ ⊢[PRAAx] Fm.neg C.meaning := by
  have hs := C.negativeSound.subst (inst c)
  simpa [atCert] using Prf.impE (Prf.impI hs) h

end CompiledFormula

/-!
## Constructor targets

Implement one constructor per fixed syntax node.  Each constructor is a finite
Lean definition assembling concrete PR symbols and the corresponding
`Prf PRAAx` fields.
-/

/-- Decidable reflected atom. -/
def compileAtom
    (meaning : Fm PTm n) (test : PTm n)
    (testBoolean : ([] : List (Fm PTm n)) ⊢[PRAAx]
      (test ≐ zero) ⋎ (test ≐ succ zero))
    (reflection : ([] : List (Fm PTm n)) ⊢[PRAAx]
      Fm.iff (test ≐ succ zero) meaning) : CompiledFormula n := by
  -- Both signed code spaces have the singleton code 0; each checker recomputes
  -- the atom and compares it with the claimed side.
  sorry

/-- Conjunction constructor: positive codes are pairs; negative codes are a
least failing branch in a disjoint sum. -/
def compileAnd (A B : CompiledFormula n) : CompiledFormula n := by
  sorry

/-- Disjunction constructor: positive codes are a least winning branch;
negative codes are pairs. -/
def compileOr (A B : CompiledFormula n) : CompiledFormula n := by
  sorry

/-- Bounded existential constructor specialized to one concrete bound/body.
Positive codes form a disjoint sum over witnesses.  Negative codes are one
heterogeneous mixed-radix table of negative child codes. -/
def compileExists
    (bound : PTm n)
    (body : CompiledFormula (n + 1))
    (wellScoped : True := True) : CompiledFormula n := by
  -- Generate prefix sums/products of child code bounds.  Positive canonical
  -- selection adapts `Search.mu`; the failure checker decodes every digit and
  -- folds the child checks.  Correctness uses qf induction on the bound.
  sorry

/-- Bounded universal constructor, dual to `compileExists`. -/
def compileForall
    (bound : PTm n)
    (body : CompiledFormula (n + 1))
    (wellScoped : True := True) : CompiledFormula n := by
  sorry

end LeanProofs.IPRA.STRIVE
