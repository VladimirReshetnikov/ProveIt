/-!
# Semantic FRNF records

This file records the host-level structures that the object compiler reifies.
It is deliberately small.  A host theorem is never treated as an iPRA theorem;
the kernel-facing fields and targets are in `Kernel.lean` and
`ObjectTargets.lean`.
-/

set_option autoImplicit false

namespace FRNF

/-- Separate rows read by a calculation from rows needed by its proof. -/
structure DualHorizon where
  read : Nat → Nat
  justify : Nat → Nat
  covers : ∀ d, read d ≤ justify d

/-- Prefix closure, needed when a consumer can inspect any row below a bound. -/
def prefixMax (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (prefixMax f n) (f (n + 1))

/-- Sequential composition of finite-use interfaces. -/
def DualHorizon.comp (inner outer : DualHorizon) : DualHorizon where
  read d := prefixMax inner.read (outer.read d)
  justify d := max
    (prefixMax inner.justify (outer.justify d))
    (prefixMax inner.read (outer.read d))
  covers d := le_max_right _ _

/-- A finite candidate level.  Object formalization replaces lists by codes. -/
structure CandidateLevel (α : Type) where
  candidates : List α
  nonempty : candidates ≠ []

/-- A fixed static transducer; functions are not passed as numerical codes. -/
structure StaticTransducer (Input Output : Type) where
  run : Input → Nat → Output
  horizon : DualHorizon

/-- Exact finite objects are the demand-zero special case. -/
structure ExactPresentation (α : Type) where
  normalize : α → α
  idempotent : ∀ x, normalize (normalize x) = normalize x

end FRNF
