# Lean artifacts

- `TrigAlgebra.lean` is the proposed Mathlib prototype for the unconditional,
  division-free algebraic core. It derives parity, shifts, multiple-angle
  identities, product-to-sum identities, and half-angle square identities from
  a minimal `TrigSystem` interface.
- `LaurentCertificate.lean` fixes the data model for the exact certificate
  checker. Its Python reference implementation verifies 227 identities.
- `IPRABridge.lean` fixes the representations and theorem interfaces for a
  direct implementation on top of ProveIt's `ConciseIPRA.PR` and
  `ConciseIPRA.EqArith` modules.

The artifact-building container did not include a Lean toolchain, so these
files were not compiled here. `IPRABridge.lean` and
`LaurentCertificate.lean` intentionally contain `axiom` declarations: they are
formalization blueprints, not claims of completed machine verification. The
article gives the proof obligations and an implementation order that removes
those declarations one by one.
