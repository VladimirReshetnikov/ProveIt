import KIFCS.OpenContract

/-!
# Fixed bounded-formula strategy interface

The eventual compiler recurses in Lean's metatheory over one fixed bounded
formula.  It returns concrete PR symbols for certificate constructors and
checkers together with the object contracts recorded below.  This file does
not postulate a universal evaluator for arbitrary formula codes.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.KIFCS

open Syn
open scoped Fm
open PTm (zero succ)

/-- A formula reflected by a Boolean-valued term. -/
structure Reflected (n : Nat) where
  formula : Fm PTm n
  code : PTm n
  range : Contract [] ((code ≐ zero) ⋎ (code ≐ succ zero))
  trueSound : Contract [code ≐ succ zero] formula
  falseSound : Contract [code ≐ zero] (formula ⟶ Fm.bot)

/-- Concrete certificate/checker interface returned for a fixed bounded
formula.  Certificate codes are ordinary natural-number terms. -/
structure StrategyInterface (n : Nat) where
  target : Fm PTm n
  truthCert : PTm n
  falseCert : PTm n
  truthCheck : PTm n
  falseCheck : PTm n
  truthSound : Contract [truthCheck ≐ succ zero] target
  falseSound : Contract [falseCheck ≐ succ zero] (target ⟶ Fm.bot)
  decision : Contract [] (target ⋎ (target ⟶ Fm.bot))

/-- A theorem-specific external truth certificate can be consumed without
requiring the canonical constructor. -/
structure CheckedTruthCertificate (n : Nat) (target : Fm PTm n) where
  checker : PTm n
  accepted : Contract [] (checker ≐ succ zero)
  sound : Contract [checker ≐ succ zero] target

namespace CheckedTruthCertificate

theorem conclude (c : CheckedTruthCertificate n target) : Contract [] target :=
  c.sound.trans (fun psi hpsi => by
    simpa using c.accepted)

end CheckedTruthCertificate

/-!
Implementation order for the fixed-syntax compiler:

* reflected equality/order atoms;
* conjunction and disjunction truth/falsity constructors;
* bounded universal truth tables and falsity counterexamples;
* bounded existential truth witnesses and falsity tables;
* canonical certificate constructors using checked bounded search;
* optional functional or DAG-compressed certificates;
* an axiom audit for the generated `StrategyInterface.decision`.
-/

end LeanProofs.ConciseIPRA.KIFCS
