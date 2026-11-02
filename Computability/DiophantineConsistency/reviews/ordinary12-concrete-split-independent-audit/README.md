# Independent audit of the 100-row concrete factor split

The independent artifact audit actually exited 0 in session 93947; its receipt
SHA-256 is `d89fb87aec30f7986cf3fa25f265fd2d9e1b731bbde0402319cad8a057297b60`.
A fresh bounded Lean replay in separate temporary paths actually exited 0 in
session 48927. Its complete replay, composed and base receipts are retained
here, with hashes in `terminal-observation.json`. The original recorded replay
receipt is also pinned. The fresh and original sources, generated objects and
successful diagnostics match by hash. An earlier intermediate audit receipt is
retained; the final audit additionally re-queries the inherited residual's
imports and binds every compiled source copy to its original source file.

The source's duplicated parts graph is identical to the already independently
checked literal, including all 100 rows, 12 variable aliases and four symbolic
integer ports. The 12 exposed parts and three pattern bindings are checked,
and four independent binding mutations are rejected. The theorem statement is
checked exactly: for an `IΣ₁` ordered-ring model, any integer port tuple and
any valuation, an internal zero implies that each of the three specified
signed factor pairs represents +1. It introduces no positivity, fixed-port or
rank hypothesis. Lean's three definitional pattern bindings and the concrete
factor-split theorem are checked by the recorded compiler replay; this is a
model theorem, not an object-theory iPRA derivation.

As an independent finite cross-check, exhaustive enumeration of 64 first,
256 main and 256 ordinary modulo-four assignments found no negative unit.
Three corresponding factor/sign mutations each produced counterexamples.
This supplements the Lean checks; it does not substitute for them.

The audit re-queried direct Lean dependencies, hashed source copies, generated
objects and recorded diagnostic logs for all six composed/literal/pattern/
concrete modules, and independently checked the inherited residual attempt and
its imports. All 20 project seed links and 180 expected absent companion paths
are matched to the previously audited historical parent, with provider and
Lean toolchain pins. The two intentionally failed inherited attempts remain
failures. The original namespace-shadow failure and warning-bearing successful
attempt are preserved separately; the clean source changes only the local
unused-binding linter setting.

The result is a bounded single-author historical overlay, not a matched full
project replay or complete package-transitive/dynamic ancestry audit. It does
not establish compact44 checker calibration, rank or ordinary-norm recovery,
transport to the 95-gate free-`J` literal, both consistency directions, or an
internal iPRA proof. The `beta=2^590069−1` port tuple and the older 2011 tuple
must not be conflated. Between-observation mutation and the Foundation
provider's unobserved wrapper exit remain outside this evidence.
