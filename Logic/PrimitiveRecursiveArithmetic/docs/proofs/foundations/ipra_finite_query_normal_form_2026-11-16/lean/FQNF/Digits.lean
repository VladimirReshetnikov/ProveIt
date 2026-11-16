import IPRADerivations.Core.Division
import IPRADerivations.Core.MultiSums

/-!
# Single-code bounded arrays: formalization milestones

The paper's normalization theorem encodes a bounded array as one natural
number.  This file fixes the exact term-level definitions and the theorem
statements needed for a complete object-iPRA implementation.

Visible `sorry` terms are deliberate roadmap markers.  Each target is reduced
in `lean/FORMALIZATION_PLAN.md` to existing theorems in `Core/Division`,
`Core/Powers`, `Core/MultiSums`, and `Core/Order`.
-/

namespace LeanProofs.IPRA.FQNF

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : Nat} {Gamma : List (Fm PTm n)}

/-- `b^i`, with the exponent first in the repository's `powF`. -/
def place (b i : PTm n) : PTm n := ap2 powF i b

/-- The base-`b` digit of `z` at position `i`. -/
def digitT (z i b : PTm n) : PTm n :=
  rem (quo z (place b i)) b

@[simp] theorem subst_place {m : Nat} (sigma : Fin n -> PTm m)
    (b i : PTm n) :
    Syn.subst sigma (place b i) = place (Syn.subst sigma b) (Syn.subst sigma i) := by
  simp [place]

@[simp] theorem subst_digitT {m : Nat} (sigma : Fin n -> PTm m)
    (z i b : PTm n) :
    Syn.subst sigma (digitT z i b) =
      digitT (Syn.subst sigma z) (Syn.subst sigma i) (Syn.subst sigma b) := by
  simp [digitT, place]

/-- Every digit is below a positive base. -/
theorem digit_lt_base {z i b' : PTm n} :
    Gamma ⊢[PRAAx] lt (digitT z i (succ b')) (succ b') := by
  sorry

/-- A little-endian array body `a(i,x)` encoded by the bounded sum
`sum_{i<L} a(i,x) b^i`.

The final implementation should define a specialized `PR` symbol using
`sumF`/`multiSumF`.  This term-level declaration records its intended API. -/
opaque encodeArray (body : PTm 2) (length parameter base : PTm n) : PTm n

/-- If every component is below `b` and `b >= 2`, the code is below `b^L`. -/
theorem encodeArray_bound
    (body : PTm 2) (length parameter b' : PTm n)
    (hcomponents : Gamma ⊢[PRAAx]
      Fm.all (lt (var 0) (Syn.shift length) ⟶
        lt (inst2 body (var 0) (Syn.shift parameter)) (Syn.shift (succ (succ b')))))) :
    Gamma ⊢[PRAAx]
      lt (encodeArray body length parameter (succ (succ b')))
        (place (succ (succ b')) length) := by
  sorry

/-- Decoding recovers each in-range component. -/
theorem digit_encodeArray
    (body : PTm 2) {length index parameter b' : PTm n}
    (hindex : Gamma ⊢[PRAAx] lt index length)
    (hcomponents : Gamma ⊢[PRAAx]
      Fm.all (lt (var 0) (Syn.shift length) ⟶
        lt (inst2 body (var 0) (Syn.shift parameter)) (Syn.shift (succ (succ b')))))) :
    Gamma ⊢[PRAAx]
      digitT (encodeArray body length parameter (succ (succ b')))
        index (succ (succ b')) ≐ inst2 body index parameter := by
  sorry

/-- Mixed-radix packing of a fixed finite tuple.  A variable-length version is
obtained by primitive recursion on `length`. -/
opaque packMixed (radix value : PTm 2) (length parameter : PTm n) : PTm n

/-- The product of the component radices is the master bound. -/
opaque mixedBound (radix : PTm 2) (length parameter : PTm n) : PTm n

/-- Mixed-radix projection. -/
opaque mixedGet (code index : PTm n) (radix : PTm 2) (parameter : PTm n) : PTm n

/-- The central master-certificate decoding theorem. -/
theorem mixedGet_packMixed
    (radix value : PTm 2) {length index parameter : PTm n}
    (hindex : Gamma ⊢[PRAAx] lt index length)
    (hradix : Gamma ⊢[PRAAx]
      Fm.all (lt (var 0) (Syn.shift length) ⟶
        lt zero (inst2 radix (var 0) (Syn.shift parameter))))
    (hvalue : Gamma ⊢[PRAAx]
      Fm.all (lt (var 0) (Syn.shift length) ⟶
        lt (inst2 value (var 0) (Syn.shift parameter))
          (inst2 radix (var 0) (Syn.shift parameter))))) :
    Gamma ⊢[PRAAx]
      mixedGet (packMixed radix value length parameter) index radix parameter
        ≐ inst2 value index parameter := by
  sorry

end LeanProofs.IPRA.FQNF
