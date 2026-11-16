import IPRADerivations.Core.Search
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Pairing
import ScopedCertificate.Kernel

/-!
# SCR implementation blueprint

The declarations below are harmless host-side metadata.  The object-theory
milestones are deliberately written as comments rather than as unproved
declarations: this archive does not pretend that targets are proofs.

Proposed repository namespace:
`LeanProofs.IPRA.ScopedCertificate`.
-/

namespace LeanProofs.IPRA.ScopedCertificate

/-- Whether a certificate may occur in the externally visible output. -/
inductive EscapeClass
  | sealed      -- certificate eliminated by `Prf.exE`
  | observed    -- only a proved-invariant observation escapes
  | named       -- the certificate itself escapes; requires a selector
  deriving DecidableEq, Repr

/-- The provenance of a producer boundary. -/
inductive ProducerStatus
  | internalPrf
  | conditional
  | pointwiseSchema
  | absent
  deriving DecidableEq, Repr

/-- Machine-readable design metadata for one future proof node. -/
structure NodeSpec where
  name : String
  escape : EscapeClass
  producer : ProducerStatus
  notes : String
  deriving Repr

/-!
## Object-theory target families

The full signatures are spelled out, with scoping conventions, in the report.
They should be implemented in dependency order.

1. `Boolean.Atom` and a specialization-time compiler for fixed bounded
   formulas.  It produces a `PTm` bit and literal `Prf PRAAx` reflection
   derivations; it is not an object-level universal evaluator.

2. `Selection.leastAccepted`.  Given a reflected verifier `check(c,q)=0`, an
   explicit cutoff `B(q)`, and a derivation that some `c<B` is accepted, use
   `Search.search_found` to prove acceptance and minimality of `Search.mu`.

3. `Trace.prefixInvariant`.  Decode one bounded action at each stage, update a
   state and an accumulated failure bit by primitive recursion, and prove

       bad(q,tau,k)=0 -> inv(q,state(q,tau,k))=1

   by one quantifier-free induction on `k`.

4. `Strategy.reflect`.  For each fixed bounded quantifier-alternation shape,
   compile a finite strategy table and checker to fixed PR syntax and prove
   that an accepted strategy implies the bounded formula.

5. `Observer.exact` and `Observer.diameter`.  Eliminate arbitrary valid
   certificates when exact observations agree, or retain a quantitative cloud
   when all observations are within a supplied diameter.

6. `Boundary.collect`.  Convert a finite list of unresolved producer formulas
   into a context theorem and, optionally, a right-associated implication
   theorem.  Composition itself should remain `Prf.trans`/`Prf.exE`.

7. `IPRABridge.Open`.  Expose the already-general Concise-to-Foundation
   environment theorem for finite contexts; add the reverse finite-context
   transport and the Foundation round-trip comparison required for reflection.
-/

end LeanProofs.IPRA.ScopedCertificate
