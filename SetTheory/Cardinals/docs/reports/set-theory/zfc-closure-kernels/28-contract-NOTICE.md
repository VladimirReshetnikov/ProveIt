# Authorship, provenance, and licensing

This package was prepared for Vladimir Reshetnikov's ProveIt research request.
Its new report text, new reference frontend/streaming code, integration driver,
and new experimental drivers are supplied for incorporation under the
MIT No Attribution license in `LICENSE` (ProveIt's convention).

This statement applies only to original work in this package. It does not
relicense retained third-party source, tables, or documentation.

## Existing work retained for reproduction

- The 254-state construction is attributed to **Mira-Cult**.
- The public 253-state reduction is attributed to **mira-emmy**.
- The accepted upstream formal verification layers are attributed to **Jeff
  and the upstream contributors**.
- The compiler/interpreter lineage uses **Andrew James Wade's** framework;
  its `LICENSE.wade` is retained beside the relevant vendored inputs.
- ProveIt helper source retains its MIT No Attribution license and pinned
  provenance in each experimental subset.
- Source19 and prior compiler inputs keep the original notices supplied with
  those research artifacts. A retained notice may describe a larger original
  archive; only the minimal referenced subset is included here.
- The optional EPSC2 projected wrapper is derived from the incoming
  `zfc_epsc2_proposal.zip`; its source is explicitly identified in the code,
  report, and source ledger. The CP/GIC calibration is the primary proposal.

The experimental READMEs give detailed source paths, immutable revisions,
source hashes, and packaging changes. The complete upstream Coq libraries are
not vendored here. Their upstream README notices and links remain available
at the pinned source, including busycoq and the Coq Library of Undecidability
Proofs.

No blanket license grant is asserted for an upstream research file for which
no such grant was supplied. Retaining source and attribution here is not a
claim of new authorship or a new machine record.

## Mathematical attribution

Generating finite transformations with permutations and a single elementary
rank-decreasing map is classical. The report cites Aird, Mitchell, and Whyte's
account of Aizenstat's 1958 presentation and the official GAP reference.
Equality-free closure theories, equality erasure, EPSC2, global closure rules,
quantified NAND, and parameter-free set-theory routes have prior sources
identified in the report. The new contribution is the explicit application,
proof-engine specification, bit-stream component, and recorded experiments.

## Verification

Independent review means mathematical and code inspection unless explicitly
identified as a formal kernel check. The new code has finite executable tests
and ordinary general proofs in the report. Upstream Coq CI evidence is recorded
separately from the local source-only and Python checks. No local Coq/Lean
rebuild, new small-machine compiler theorem, or serialized PA/ZFC proof is
claimed.
