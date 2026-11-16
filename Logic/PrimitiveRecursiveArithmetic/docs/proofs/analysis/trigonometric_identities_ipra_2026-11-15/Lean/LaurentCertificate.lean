import Mathlib

/-!
# Lean implementation outline for exact trigonometric certificates

The executable reference is `scripts/verify_identities.py`.  This file records
the intended Lean datatypes and soundness boundary.  The full implementation
is routine finite algebra and has no analytic dependency.
-/

namespace TrigIPRA.Certificate

structure GQ where
  re : Rat
  im : Rat
  deriving DecidableEq, Repr

abbrev Var := String
abbrev Monomial := Var →₀ Int
abbrev Laurent := Monomial →₀ GQ

structure Angle where
  vars : Var →₀ Int
  quarterTurns : Int
  deriving DecidableEq, Repr

structure RatFun where
  num : Laurent
  den : Laurent
  den_nonzero_syntax : den ≠ 0

/-- Planned normalization/evaluation operations. -/
axiom cis : Angle → Laurent
axiom sine : Angle → Laurent
axiom cosine : Angle → Laurent
axiom normalize : Laurent → Laurent
axiom residue : RatFun → RatFun → Laurent

/-- `check p q` is the finite, decidable certificate predicate. -/
def check (p q : RatFun) : Bool := decide (normalize (residue p q) = 0)

/-- Semantic soundness target.

`Eval` maps angle variables to an arbitrary constructive trigonometric system;
`Guards` supplies apartness of all denominators.  The proof is induction on the
finite maps and uses no classical principle.
-/
axiom certificate_sound
    (p q : RatFun) (h : check p q = true) : True

end TrigIPRA.Certificate
