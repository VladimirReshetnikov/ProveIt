# Integration into ProveIt

The base snapshot is `b6c7087477e51c017003bd729e712c8969733223`.

The six files in `formal/reference/` are byte-identical context for standalone
reproduction. **Do not replace the repository's support modules with these
copies.** Use the existing modules from the checkout and verify compatibility
if it has advanced.

Place the six new Lean sources (`PositiveStutter`, `CM215Tables`,
`CM215Invariant`, `CM215Transfer`, `CM215CoreBridge`, `CM215Dense`) on the
project's module path, retaining their import names, or move them under an
agreed namespace and update the imports consistently. Add the supplied
`CM215Endpoint.lean` to the same build.

The wrapper composes the existing `KEndpoint215.blank_halts_iff_zfc_refutation`
with `CM215.CoreBridge.calibration_transfer`. It states the exact literal
CM215 blank-halting equivalence and its nonhalting counterpart, and prints
both assumption reports.

The new six-module extension and six support modules have a standalone
reproduction driver. The wrapper imports the full calibration and was not
included in that standalone build. Run it with the existing full project
closure and confirm the endpoint's dependency report retains the baseline
allowed axioms. No extra axiom is intended or required by the wrapper.

For a Rocq endpoint, port the three-clause invariant and two local blocks to
the existing tape model, instantiate `PositiveStutter.v`, and compose with
the existing dense K215 endpoint. Only the generic `.v` theorem has been
checked here (Coq 8.18.0 plus `coqchk`); a concrete CM215 Rocq endpoint is
future work.

