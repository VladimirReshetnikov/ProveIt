# Attribution and licensing boundaries

The new accelerator, periodic interpreter, exact arithmetic-DAG evaluator,
certificate orchestration, machine generator, documentation and TeX section
are supplied for incorporation into ProveIt under the MIT No Attribution
terms in `LICENSE`.

The helper `code/runtime252_short_gap.py` is retained from the prior
`zfc_consistency_research_2026-10-16` contribution imported in ProveIt. Its
provenance and exact hash are in `source_manifest.json`. The relevant
ProveIt license is retained as `vendor/LICENSE.ProveIt`.

The 252-state transition table is the known runtime fold of the prior
Mira-Cult/mira-emmy construction. It is not claimed as a newly authored
baseline. The new contribution is the explicit finite blank-bootstrap
calculation and the logical calibration described in the report. The
underlying construction also depends on Andrew James Wade's framework and
jeff87654's verification.

Selected unmodified upstream busy-beaver files are retained for precise
review and offline reproduction. No upstream-wide license was declared in
the inspected tree, and this package does not relicense those files. Their
paths, revision, original Git blob IDs and SHA-256 hashes are explicit in
the source manifest. No sources from the separately licensed busycoq or
undecidability libraries are included, and no blanket upstream license is
inferred from another component's license.

The archive contains no compiler binaries, repository metadata, generated
theorem-prover object files, or unrelated prior research caches.
