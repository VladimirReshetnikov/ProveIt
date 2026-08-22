# Analysis

Formal analysis developments.  The exact identity projects have paired Lean
and Coq proofs; the Fabius project is currently a Lean statement formalization.

- [`TrigonometricIdentities/`](TrigonometricIdentities/) contains the
  eleven-term arctangent-square identity and the golden-ratio sine identity.
- [`ExponentialIdentities/`](ExponentialIdentities/) contains the exact floor
  certificate for the five-level tiny-exponent tower.
- [`FabiusFunction/`](FabiusFunction/) defines the bounded Fabius function,
  its signed global extension, exact rational dyadic arithmetic, and the
  statements of every result in arXiv:1702.06487v3.  Proofs are the next
  formalization phase.

The Coq developments are mathematical ports rather than generated
translations. The tiny-exponent proof uses `coq-interval`; the trigonometric
proof derives the exact constants needed by the identity.
