import ConciseIPRA.NativeBiInterpretation

/-!
# Exact shape of the embedded-iPRA completion targets

STATUS: object-language specification and conditional transport, not a
completed proof of the triangle theorems.  The parameters `checkCode` must be
the PR syntax trees compiled from the specified checkers; they have not been
constructed in this packet.  Selecting a constant-zero symbol would not
satisfy the compiler/correspondence obligation in OUTLINE.md.

Inspected API: VladimirReshetnikov/ProveIt at
38cafaa5be7f4602567440bcebc754abdbacefc9.
No `Prf PRAAx` proof of a geometric or numerical checker is asserted here.
-/

namespace TriangleIPRA.ObjectTargets

open LeanProofs.ConciseIPRA

/-- A checker equation with `arity` free numerical variables. -/
def checkerFormula {arity : ℕ} (checkCode : PR arity) : Fm PTm arity :=
  .eq (.app checkCode PTm.var) PTm.zero

theorem checkerFormula_qf {arity : ℕ} (checkCode : PR arity) :
    (checkerFormula checkCode).QF := True.intro

/-- Close all numerical variables. Universal closure is an inference step;
it is not the formula used for induction. -/
def closeAll : (arity : ℕ) → Fm PTm arity → Fm PTm 0
  | 0, φ => φ
  | arity + 1, φ => closeAll arity (.all φ)

/-- Completion criterion for the specific compiled checker. -/
def InternalTarget {arity : ℕ} (checkCode : PR arity) : Prop :=
  Prf PRAAx [] (closeAll arity (checkerFormula checkCode))

/-- Four coded rational coordinates suffice for the polynomial kernel. -/
abbrev PolynomialTarget (checkCode : PR 4) : Prop := InternalTarget checkCode

/-- Three natural inputs are numerator, positive denominator, and precision. -/
abbrev SquareRootTarget (checkCode : PR 3) : Prop := InternalTarget checkCode

/-- The existing bi-interpretation transports a derivation AFTER it exists.
This theorem does not construct the required `h`. -/
theorem transferToNative {n : ℕ} {φ : Fm PTm n}
    (h : Prf PRAAx [] φ) : NPrf [] (NFm.ofPRA φ) := by
  simpa using (pra_iff_native (Γ := []) (φ := φ)).mp h

end TriangleIPRA.ObjectTargets
