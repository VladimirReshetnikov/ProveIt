# Repository audit and source provenance

## Snapshot and scope

This report uses ProveIt at
[47f3a3602946dfe48803a91a910c646e74637ac8](https://github.com/VladimirReshetnikov/ProveIt/commit/47f3a3602946dfe48803a91a910c646e74637ac8),
committed on **16 October 2026 at 20:03:37 UTC**. The audit covers the four
distinct requested commits, subsequent relevant implementation and intake
work, and all four unplaced incoming archives at that snapshot.

`source_manifest.json` supplies the full commit identifiers, immutable
source URLs, exact archive member names, archive and member hashes, and
verification boundaries. The hash repeated in the request identifies a
single commit.

The principal repository locations are:

| Location | Content |
|---|---|
| `Computability/BusyBeaver/Research/ZFC/` | Compiler experiments, theory notes, literal candidates, and status records |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` | New Lean closure, syntax, quotient, and machine lemmas |
| `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/` | Reconciled closure-kernel manuscripts, source assessments, and reproduction records |
| `lib/jeff-busy-beaver-zfc254/` | Attributed import of the published 254-state machine and verification |

## The requested commits and their continuations

| Commit | Role |
|---|---|
| `b07d1a27bbe2814f2fd84cc55feef71c4de5b2db` | Places the three original closure-kernel manuscripts as batch 143 |
| `83ef1da6b717338f710277c2744fb4ec644cedbc` | Reconciles their overlap, provenance, and verification scopes |
| `67086c8d8802ea7b3625a2fc0765d39e2181e335` | Imports Mira-Cult's 254-state machine and Jeff's verification |
| `6594795e9db81637c30959e42b3bcfc9eb77722f` | Develops Lean closure/coding results and reproducible machine-minimization experiments |

The important subsequent developments include the checked extensional
PSC/ZF comparison at `fa6fcaf096446ff5774f6d03570f030314bc7ad8`;
the frozen raw 252-state experiment at
`29efd22ed802c81f0ece48be0838ca48310983e6`; batch 144 placement and
reconciliation at `ac4287e5b590a87bb98d0627c608dbebf1150a37` and
`6d8bc7f1ba02c83e54757366f019f61b966ed0b7`; hereditary-saturation
formalization at `45a1b47c4d742b74def38121388509985a907d25`; and the
distinct PSC-only compiler experiment and logical obstruction at
`e7c4cadf9b180e4b1801755b09777a7572412360`.

## Established mathematical and formal results

The report builds on the following existing results:

- Pure subset local bounds can replace the earlier mixed
  membership/subset bounds.
- One-sided profile congruence suffices for the corresponding control
  theory.
- Extensionality plus subset-seeded PSC has the same sentence theorems
  as first-order ZF without Foundation or Choice. The repository checks
  this in its actual `BProv` calculus using model equivalence and
  first-order completeness.
- Equality-free PSC alone has an accepted ordinary mathematical
  consistency calibration with ZFC. Batch 144 source 08 gives the
  full-profile bootstrap, incoming-profile saturation, hereditary
  domain, purity cut, and transfer of the entire extensional PSC schema.
- The full PSC-only interpretation has not yet been connected end to
  end in Lean. Checked semantic hull-transfer components have explicit
  resource hypotheses; complete formula adapters and the final
  proof-predicate bridge remain.
- Equality can be erased from the ordinary CP/GIC source using full
  two-sided observational profiles. This comparison concerns a complete
  first-order calculus, not the reduced numerical calculus of the raw
  machine experiments.

The original arrival of source 08 is
[39409c8c921cccdbd6162c8767c84cfb7df65df1](https://github.com/VladimirReshetnikov/ProveIt/commit/39409c8c921cccdbd6162c8767c84cfb7df65df1).
Its archive is
[zfc_one_schema_research.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/39409c8c921cccdbd6162c8767c84cfb7df65df1/docs/incoming/zfc_one_schema_research.zip).
The repository's
[intake assessment](https://github.com/VladimirReshetnikov/ProveIt/blob/47f3a3602946dfe48803a91a910c646e74637ac8/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-144-source-08.md)
states the accepted proof and remaining formalization boundaries.

## The four latest incoming archives

All links below identify files at the audited immutable snapshot.
The source manifest records the exact members and hashes.

| Archive | Main reference members | Contribution |
|---|---|---|
| [zfc_small_machine_research.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/47f3a3602946dfe48803a91a910c646e74637ac8/docs/incoming/zfc_small_machine_research.zip) | `zfc_small_machine/report.tex`; `sections/machine_candidate.tex`; `sections/base3_codec.tex` under that root | 250-state raw C/G experiment, equality erasure, and base-three syntax |
| [zfc_small_machines_20261016.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/47f3a3602946dfe48803a91a910c646e74637ac8/docs/incoming/zfc_small_machines_20261016.zip) | `zfc_small_machines_20261016/report.tex` | 248-state original/dual-rho6 raw experiments and an independent register-machine compression certificate |
| [zfc_consistency_machine_research.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/47f3a3602946dfe48803a91a910c646e74637ac8/docs/incoming/zfc_consistency_machine_research.zip) | `zfc_machine_report/sections/countermodel.tex`; `code/equality_free_countermodel.py` under that root | Full-calculus finite-sort obstruction, benchmark evidence, and diagnostic repairs |
| [zfc_consistency_proposal.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/47f3a3602946dfe48803a91a910c646e74637ac8/docs/incoming/zfc_consistency_proposal.zip) | `zfc_consistency_proposal/report.tex`; `code/environment_tableau.py`; `code/refutation_search.py` under that root | PSC-only proposal, complete environment-tableau reference, fair enumeration, and full-logic compiler controls |

The 250- and 248-state reductions are measurements of the same reduced
raw C/G calculus. The newer finite-sort obstruction therefore supersedes
their suggested calibration programs unless the logical interface is
substantively repaired. Their register-level compression certificates
remain useful evidence about those transformations.

## Benchmark status: 254 and 253 states

Mira-Cult designed the 254-state machine and compact nonextensional
container/collection program. Jeff supplies the published Coq
verification at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`.

The attributed 253-state reduction is mira-emmy's
[upstream PR 20](https://github.com/jeff87654/busy-beaver/pull/20),
with source head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`.
The exact
[endpoint source](https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/coq/e2e/E2E253.v)
and
[literal table](https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm)
are separately pinned.

The incoming report preserves an observation and excerpt from the
[successful verification job](https://github.com/jeff87654/busy-beaver/actions/runs/38829452130/job/116744580063).
It reports Coq 8.20.1, 160 recursively checked module roots, and 194 closed
assumption reports, tested at synthetic merge
`26bd0b2beeed5c3dd88511e39acd604c235e2f1c`.
The exact archived evidence members are
`zfc_machine_report/evidence/upstream253-ci-observation.json` and
`zfc_machine_report/evidence/upstream253-ci-excerpt.txt`.

These records support the attributed external finite-refutation endpoint.
They are not a new local proof-assistant run, and they are distinct from
a delivered serialized internal PA/ZFC proof of the exact arithmetic
equivalence requested here. The comparison with ordinary Foundation and
Choice conventions must be kept explicit.

## The raw-calculus obstruction and its scope

The newest incoming countermodel assigns each variable label its own
finite domain. Those domains grow sufficiently rapidly to validate the
actual C/G bundle because the matrix's code also supplies a fresh
higher label. Both original and dual rho6, the logical rows, gated
membership vacuity, and all emitted collection/container instances are
valid, while the designated target is false.

Consequently the source proves nonhalting of the specified abstract raw
enumerator in ZFC. The present report strengthens this to PA using
primitive-recursive finite truth tables and an arithmetic
current/cache/stack invariant.

A conclusion about a **literal** 248-, 250-, or 252-state table remains
conditional on proving a suitable simulation into that abstract
enumerator. No unconditional nonhalting of these unaudited binary
implementations is asserted. Assuming ZFC consistent, a faithfully
implemented raw enumerator cannot also satisfy the desired
ZFC-provable equivalence with `Con(ZFC)`.

The primitive-Bottom PSC-only 252-state experiment at `e7c4cadf` is a
different artifact. Its reduced quantifier calculus has a separate
constant-true-quantifier counterinterpretation. Neither problem
refutes the ordinary first-order consistency calibration of PSC alone.

## Independent rerun and reproducibility

The inherited finite-sort regression was independently rerun with these
results:

| Family | Cases |
|---|---:|
| Full container formula | 312 |
| Collection with arbitrary binary matrices | 32,768 |
| Higher-label/lower-output collection cases | 440 |
| Colliding input/output collection cases | 392 |
| Total decoder support | 10,000 |

The unchanged source script is supplied as
`code/equality_free_countermodel.py`; its SHA-256 is
`cc6812d56a3f3c60f40c8eed5a263b6f30aa9e8c77d828f136fad889d47be75e`.
The independent rerun evidence is `data/countermodel_rerun.json`.
From the package root, run:

```sh
python code/equality_free_countermodel.py
```

This uses only the Python standard library, prints the result, and
writes `code/equality_free_countermodel_results.json`. Run without
`-O` or `-OO`, because the inherited script deliberately uses assertions
for its finite regressions. Full source attribution and the precise
scope are in `code/COUNTERMODEL_ATTRIBUTION.md`.

`data/countermodel_source_NOTICE.txt` is the unchanged notice from the
original incoming archive. It preserves that archive's attribution and
license boundaries; its references to other scripts, vendor directories,
and evidence describe the original archive, not the inventory of this
deliverable. The files supplied here are identified in
`data/source_manifest.json` and the package README.

The new clausal reference has separate source attribution, proofs of its
mathematical specification, finite checks, and results in
`code/CLAUSAL_TRACE_ATTRIBUTION.md`, `data/clausal_trace_proof.md`, and
`data/clausal_trace_results.json`. It has no measured binary machine
state count. No finite failed search or regression is presented as a
consistency proof.

