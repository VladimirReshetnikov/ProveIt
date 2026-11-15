import ConciseIPRA.NativeBiInterpretation

/-!
# Embedded-iPRA completion targets

This file states the exact shape of the final ProveIt targets.  It does not
pretend that the primitive-recursive checker codes or their `PRAAx` derivations
have already been constructed.

Inspected repository: VladimirReshetnikov/ProveIt
commit: 948fe06760595e3bce468b67d25032bbbf7f376d
-/

namespace MollweideCircleIPRA.ObjectTargets

open LeanProofs.ConciseIPRA

/-- A primitive-recursive checker succeeds when its output is zero. -/
def checkerFormula {arity : ℕ} (checkCode : PR arity) : Fm PTm arity :=
  .eq (.app checkCode PTm.var) PTm.zero

/-- Checker equations are quantifier-free and therefore eligible for iPRA
induction after the checker has been compiled to a `PR` term. -/
theorem checkerFormula_qf {arity : ℕ} (checkCode : PR arity) :
    (checkerFormula checkCode).QF := True.intro

/-- Universal closure is performed only after the quantifier-free checker
proof; it is not smuggled into the induction formula. -/
def closeAll : (arity : ℕ) → Fm PTm arity → Fm PTm 0
  | 0, phi => phi
  | arity + 1, phi => closeAll arity (.all phi)

/-- Final derivability criterion in the ordinary iPRA presentation. -/
def InternalTarget {arity : ℕ} (checkCode : PR arity) : Prop :=
  Prf PRAAx [] (closeAll arity (checkerFormula checkCode))

/-- Target for the triangle polynomial certificate bundle. -/
abbrev TrianglePolynomialTarget {arity : ℕ} (checkCode : PR arity) : Prop :=
  InternalTarget checkCode

/-- Target for the power-of-a-point polynomial certificate bundle. -/
abbrev CirclePolynomialTarget {arity : ℕ} (checkCode : PR arity) : Prop :=
  InternalTarget checkCode

/-- Target for bounded positive-square-root and reciprocal routines. -/
abbrev AnalyticPrimitiveTarget {arity : ℕ} (checkCode : PR arity) : Prop :=
  InternalTarget checkCode

/-- Once a `PRAAx` derivation exists, the current ConciseIPRA
bi-interpretation transports it to the native kernel. -/
theorem transferToNative {n : ℕ} {phi : Fm PTm n}
    (h : Prf PRAAx [] phi) : NPrf [] (NFm.ofPRA phi) := by
  simpa using (pra_iff_native (Γ := []) (φ := phi)).mp h

end MollweideCircleIPRA.ObjectTargets
