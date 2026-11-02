# Independent audit of the 100-row ordinary12 literal prototype

The independent artifact audit actually exited 0; its receipt SHA-256 is
`502e46198544f14868ee8e6e1732c256a8642ea3fe324c31253a0b5a31f06c02`.
A fresh bounded Lean replay in separate temporary paths actually exited 0 in
session 10429. Its complete replay and base receipts are retained here, with
hashes in `terminal-observation.json`. The original recorded replay receipt is
also pinned. The fresh and original literal sources, objects and successful
compiler diagnostics match byte-for-byte or by hash. An earlier intermediate
independent receipt is retained; the final audit adds complete parent-output
and absent-companion bindings and reruns the checks.

An independent parser compared all 100 rows, 12 variable aliases and four port
aliases against the pinned ordinary12 graph. It checked the exact exposed
factors `1+A0`, `1+A1`, `1+N` and their product-minus-one output, and rejected
six mutations spanning operations, variables, ports, factor aliases and output
sign. This is the 100-row graph with restricted `J=6j+1`; the later 95-row
free-`J` construction requires its separate arithmetic transport.

The checked Lean source states three distinct results: a definitional literal
factorization, its raw integer evaluation identity, and, for an `IΣ₁` model,
that an internal zero implies that the product of the three corresponding
signed pairs is equivalent to one. The audit checked the exact statement text,
the compiler's three named axiom reports and its source, object and diagnostic
hashes. It separately reran Lean's direct-dependency query for each replay and
hashed the resolved `Init` and `ArithmeticAdaptiveFactorMagnitude2011` input
objects. The recorded earlier failed prototype attempts remain failures; their
`sorryAx` diagnostics are not treated as successful proofs.

The bounded historical overlay's 20-module source-declared closure is bound
to the independently audited parent state, source snapshots, objects and
logs. All 20 parent links and all 180 expected absent companion paths are
checked against that state; the provider receipt and Lean binary are pinned.
This is not a complete package-transitive or dynamic dependency audit, nor an
independently matched full-project replay. Between-observation mutations and
the Foundation provider's unobserved outer wrapper exit remain outside scope.

The theorem does **not** establish the concrete three-factor exclusions needed
to split product one, compact44 checker calibration, rank recovery, an iPRA
derivation, or consistency equivalence. The four ports are symbolic in the
literal theorem, and the distinct compact44 tuple and its relation to the
fixed checker require their separate binding and calibration evidence.
