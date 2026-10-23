# Source and scope

The fixed K215 transition table, the 943-tile language, and the native
layout are inherited from Vladimir Reshetnikov's ProveIt repository,
commit `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`, package
`36-small-tuple/coefficients/`. The initial builder was adapted from that
package's `build_coefficients.py`; its language reconstruction and exact
support-identity checks are retained. The new bounded-checksum clause
encoding, changed radix/circumference, padding, and actual-rank controller
are documented in `PROOF.md`.

This package supplies ordinary mathematical arguments and finite checks.
It does not claim an end-to-end Lean or Rocq verification.
Inherited licenses and attribution notices are retained in `licenses/`.
