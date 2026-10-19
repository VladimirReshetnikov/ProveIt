# Checked arithmetic fixed-point dependency

Foundation's unchanged 226-line `FirstOrder.Bootstrapping.FixedPoint` now
passes a fresh source check and a default-limit audit with **12 axiom probes
and 12 typed clients**. The [actual record](results/foundation-fixedpoint-verification.json)
binds the pinned Foundation source at `32e1a0956a8622fad067328ca1959729a7634428`.
All probes use only standard Lean axioms.

The checked interfaces cover represented numeral substitution at quoted
formulas, single and multiple fixed points, injectively padded fixed points,
positive Π-level preservation, and parameterized diagonal equivalences.
The underlying substitution functions operate in arbitrary IΣ₁ models;
the quoted formulas and finite arities are standard external syntax.
The diagonal theorems require IΣ₁ to be provably weaker than the theory in
question. Padding gives syntactically distinct formulas; it does not assert
that their truth values are mutually exclusive.

Source and audit took 22.448 and 4.366 seconds, sharing a 120-second deadline
with one compiler thread and 4,096 MiB. Both use default proof limits. The
source emitted 13 duplicated-namespace style warnings; the audit emitted
none. The exact warnings remain in the [source log](foundation-fixedpoint/source.log)
and [actual-evidence review](foundation-fixedpoint/actual-review.json).
All 37 recorded inputs, four fresh module artifacts and 188 namespace links
remained unchanged. The old cached target was explicitly excluded before
compilation, and the fresh first provider was captured before the audit.

The immediate dependencies remain explicit opaque cached boundaries.
`Bootstrapping.Syntax` uses the exact source/object pair recorded in the
earlier BindFree check; `Arithmetic.Basic.Model` has only a current cache
observation. Their companions are current observations, not new historical
captures. The earlier runner's version query, lack of a shared timeout and
lack of `-j1` remain disclosed. This check does not attest the whole linked
Foundation cache or freshly compile those dependencies.

The [publication](results/foundation-fixedpoint-publication.json) and
[history](foundation-fixedpoint/history.json.gz) preserve preparation,
source snapshots, guard, audit and actual execution. An
[independent source/API/guard review](foundation-fixedpoint/peer-review.json)
has its own [history](foundation-fixedpoint/peer-history.json.gz); the
subsequent actual-evidence review has a separate
[history](foundation-fixedpoint/actual-review-history.json.gz).

This completes the fresh FixedPoint step proposed in the frozen
[provider route](fixedpoint-template-route/README.md). It supports the later
`UniformStatement` check; it establishes neither an all-internal diagonal
scheme nor the final PA/binary-machine endpoint. As an external dependency,
it is additional to the original 88-project-module inventory.
