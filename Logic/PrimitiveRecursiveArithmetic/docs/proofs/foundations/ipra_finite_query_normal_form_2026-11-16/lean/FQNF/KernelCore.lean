import IPRADerivations.Core.Search

/-!
# Kernel-facing structural core of finite-query normal form

This file is intentionally small.  It contains only logical composition and
checker-reflection combinators whose conclusions are literal `Prf PRAAx`
derivations.  It is designed to live under
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/FQNF/`.

No semantic theorem about `Nat` is converted into an object-iPRA theorem.
Arithmetic work enters through explicit derivations supplied to these
combinators.

STATUS IN THIS ARTIFACT: source-oriented and statically audited; Lean was not
available in the artifact runtime, so no compilation claim is made.
-/

namespace LeanProofs.IPRA.FQNF

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n k : Nat}
variable {Gamma Delta : List (Fm PTm n)}
variable {phi psi chi : Fm PTm n}

/-- `Derives Gamma Delta` says that every formula listed in `Delta` has an
object-iPRA derivation from `Gamma`. -/
def Derives (Gamma Delta : List (Fm PTm n)) : Prop :=
  forall {theta : Fm PTm n}, theta ∈ Delta -> Gamma ⊢[PRAAx] theta

namespace Derives

/-- The empty list is derivable from every context. -/
theorem nil : Derives Gamma [] := by
  intro theta h
  exact False.elim (by simpa using h)

/-- Add one already-derived formula to a derivable bundle. -/
theorem cons (hphi : Gamma ⊢[PRAAx] phi) (hDelta : Derives Gamma Delta) :
    Derives Gamma (phi :: Delta) := by
  intro theta htheta
  rcases List.mem_cons.mp htheta with h | h
  · subst theta
    exact hphi
  · exact hDelta h

/-- Every context derives itself. -/
theorem refl : Derives Gamma Gamma := by
  intro theta htheta
  exact Prf.hyp htheta

/-- Monotonicity on the target bundle. -/
theorem mono (h : Derives Gamma Delta) {Xi : List (Fm PTm n)}
    (sub : Xi ⊆ Delta) : Derives Gamma Xi := by
  intro theta htheta
  exact h (sub htheta)

end Derives

/-- Compile one local proof node.  The local derivation may use the formulas in
`Delta` and the permanent assumptions `Gamma`; simultaneous cut replaces every
member of `Delta` by its already-compiled derivation. -/
theorem compileLocal
    (hDelta : Derives Gamma Delta)
    (hlocal : Delta ++ Gamma ⊢[PRAAx] phi) :
    Gamma ⊢[PRAAx] phi := by
  exact hlocal.trans (by
    intro theta htheta
    rcases List.mem_append.mp htheta with htheta | htheta
    · exact hDelta htheta
    · exact Prf.hyp htheta)

/-- Extend a compiled proof bundle by one local node. -/
theorem compileAndExtend
    (hDelta : Derives Gamma Delta)
    (hlocal : Delta ++ Gamma ⊢[PRAAx] phi) :
    Derives Gamma (phi :: Delta) :=
  Derives.cons (compileLocal hDelta hlocal) hDelta

/-- A fixed primitive-recursive checker together with object-iPRA reflection in
both directions.  The `qf` field makes the specification available as an
induction invariant after specialization. -/
structure ReflectedChecker (k : Nat) where
  check : PR k
  spec : Fm PTm k
  qf : spec.QF
  sound : ([] : List (Fm PTm k)) ⊢[PRAAx]
    ((app check var ≐ succ zero) ⟶ spec)
  complete : ([] : List (Fm PTm k)) ⊢[PRAAx]
    (spec ⟶ (app check var ≐ succ zero))

namespace ReflectedChecker

/-- The checker equation at concrete arguments. -/
def holds (C : ReflectedChecker k) (ts : Fin k -> PTm n) : Fm PTm n :=
  app C.check ts ≐ succ zero

/-- Soundness specialized to arbitrary terms and arbitrary assumptions. -/
theorem soundAt (C : ReflectedChecker k) (ts : Fin k -> PTm n)
    (h : Gamma ⊢[PRAAx] C.holds ts) :
    Gamma ⊢[PRAAx] C.spec.subst ts := by
  have hs : Gamma ⊢[PRAAx] (C.holds ts ⟶ C.spec.subst ts) := by
    simpa [holds] using LeanProofs.IPRA.inst (Γ := Gamma) C.sound ts
  exact Prf.impE hs h

/-- Completeness specialized to arbitrary terms and arbitrary assumptions. -/
theorem completeAt (C : ReflectedChecker k) (ts : Fin k -> PTm n)
    (h : Gamma ⊢[PRAAx] C.spec.subst ts) :
    Gamma ⊢[PRAAx] C.holds ts := by
  have hc : Gamma ⊢[PRAAx] (C.spec.subst ts ⟶ C.holds ts) := by
    simpa [holds] using LeanProofs.IPRA.inst (Γ := Gamma) C.complete ts
  exact Prf.impE hc h

end ReflectedChecker

/-- Quantifier-free induction specialized at an explicit fuel term. -/
theorem invariantAt
    (I : Fm PTm (n + 1)) (hI : I.QF) (fuel : PTm n)
    (h0 : Gamma ⊢[PRAAx] I.subst (inst zero))
    (hS : I :: Gamma.map Fm.shift ⊢[PRAAx]
      I.subst (repl (succ (var 0)))) :
    Gamma ⊢[PRAAx] I.subst (inst fuel) :=
  Prf.allE fuel (PRA.qfInd I hI h0 hS)

/-- A bounded loop may terminate in an arbitrary, possibly quantified,
conclusion once the terminal invariant implies that conclusion. -/
theorem loopProduces
    (I : Fm PTm (n + 1)) (hI : I.QF) (fuel : PTm n)
    (C : Fm PTm n)
    (h0 : Gamma ⊢[PRAAx] I.subst (inst zero))
    (hS : I :: Gamma.map Fm.shift ⊢[PRAAx]
      I.subst (repl (succ (var 0))))
    (hfinish : Gamma ⊢[PRAAx] (I.subst (inst fuel) ⟶ C)) :
    Gamma ⊢[PRAAx] C :=
  Prf.impE hfinish (invariantAt I hI fuel h0 hS)

/-- Eliminate two independently obtained certificates by a local stability
proof.  Neither certificate is required to be a canonical representative. -/
theorem stableOfIndependent
    (C1 C2 O : Fm PTm n)
    (h1 : Gamma ⊢[PRAAx] C1)
    (h2 : Gamma ⊢[PRAAx] C2)
    (hstable : C1 :: C2 :: Gamma ⊢[PRAAx] O) :
    Gamma ⊢[PRAAx] O :=
  Prf.impE (Prf.impE (Prf.impI (Prf.impI hstable)) h2) h1

/-- A global or ineffective input remains an explicit premise. -/
theorem useBoundary
    (Boundary : Fm PTm n)
    (hBoundary : Gamma ⊢[PRAAx] Boundary)
    (hLocal : Gamma ⊢[PRAAx] (Boundary ⟶ phi)) :
    Gamma ⊢[PRAAx] phi :=
  Prf.impE hLocal hBoundary

/-- Exact branch recovery is just ordinary implication elimination once a
separation/gap theorem has been supplied.  The mathematical content belongs in
`hGapToExact`, not in this structural rule. -/
theorem exactFromGap
    (Approx Gap Exact : Fm PTm n)
    (hApprox : Gamma ⊢[PRAAx] Approx)
    (hGap : Gamma ⊢[PRAAx] Gap)
    (hGapToExact : Approx :: Gap :: Gamma ⊢[PRAAx] Exact) :
    Gamma ⊢[PRAAx] Exact :=
  stableOfIndependent Approx Gap Exact hApprox hGap hGapToExact

end LeanProofs.IPRA.FQNF
