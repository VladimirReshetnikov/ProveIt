# Independent audit of the free-J 95-gate model split

The independent artifact audit actually exited 0 in session 80309; its receipt
SHA-256 is `9fa181917cfd6246c4dc8f305d8ced81cc1c6baf628adc97d6e78e43ec42c706`.
A fresh bounded Lean replay in separate temporary paths actually exited 0 in
session 35994. Its replay, nested concrete, composed and base receipts are
retained here with hashes in `terminal-observation.json`. The original saved
replay is pinned. The fresh and original sources, generated objects and
successful diagnostic logs match by hash. An earlier independent receipt is
retained; the final audit additionally re-queries all six inherited modules'
direct imports and binds their source, object and log hashes to the separately
audited concrete replay.

An independent parser compares all 95 rows, the twelve variable slots and all
four symbolic integer-port slots with the pinned manuscript graph, checks the
exact exposed factor/output and auxiliary tuple, and rejects six mutations.
The first variable is free `J`, used directly in `qm=J*beta`; it is not the
restricted `J=6j+1` variable of the prior 100-row construction. The earlier
independent manuscript audit separately verifies the 96-to-95 graph identity
and exact degree 70 at its recovered fixed tuple; this graph check does not
itself establish checker calibration.

The source's exact theorem is checked for an `IΣ₁` ordered-ring model, arbitrary
integer ports and arbitrary valuation: an internal zero makes each of the
three specified signed factor pairs represent +1. It has no positivity or
fixed-port assumption. The seven named compiler reports include the three
factor bindings and the direct free-J factor split. Independently enumerating
all 256 modulo-four inputs confirms the polarized factor cannot be −1, while
removing its explicit factor four yields counterexamples. This supplements,
not replaces, the checked Lean proof.

The audit rechecks the source-declared 20-module historical parent closure,
all 20 output links and 180 absent companion paths, parent sources and logs,
provider and toolchain pins. It re-queries and hashes direct inputs for the
free-J module, all six nested compiled modules and the inherited residual.
The two deliberately failed residual attempts remain failures. The earlier
free-J source-check path error is reported in the original packet; it is not
promoted into a successful check.

This is a bounded single-author historical overlay, not a matched full-project
replay or complete package-transitive/dynamic dependency audit. It does not
prove compact44 checker calibration, the exceptional-factor/rank argument,
both consistency directions or an internal iPRA derivation. No inference is
made that all free-J zeros satisfy the old congruence condition. The selected
compact44 tuple and the older 2011 tuple are distinct. Between-observation
mutation and the Foundation provider's unobserved wrapper exit remain outside
this evidence.
