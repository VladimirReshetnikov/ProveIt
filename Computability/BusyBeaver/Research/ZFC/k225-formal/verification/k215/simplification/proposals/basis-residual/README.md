# K215 proof simplification: a shared basis and certified residual execution

Prepared for Vladimir Reshetnikov and the ProveIt project, 21 October 2026
(Pacific time).

**Recommendation:** adopt the shared implication basis first; review the
residual execution component as a separate change. Both preserve the concrete
215-state machine. Full production endpoint replays remain adoption gates.

Review baseline:
[`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`](https://github.com/VladimirReshetnikov/ProveIt/tree/57541fe0cfe3af62b4cb58747d8d1d7c16b338d5).

## Read first

- `article/k215_basis_residual.pdf`: the research report, including the complete
  two-MP argument, abstract interfaces, exact scope of verification, and
  integration gates.
- `article/k215_basis_residual.tex` and `article/measurements.tex`: editable
  report sources.
- `lean_basis/README.md`: shared Lean basis, synchronized producer, focused
  baseline/candidate checks, and public-interface audits.
- `rocq_basis/README.md`: the matching shared Rocq proof, both calculus
  adapters, exact-type clients, recursive component checks, and regeneration.
- `residual_sites/README.md`: semantic site contracts, exact decoder-port
  connection, finite residual certificates, and the separately marked
  endpoint integration proposal.
- `independent_review/`: a second source and evidence review within this
  collaboration, including an independently checked abstract two-MP theorem.

## Results and their scope

| Change | Before | Proposed | What is measured |
|---|---:|---:|---|
| Selected Lean logic sources | 42,454 bytes / 811 lines | 18,096 bytes / 411 lines | Both original developments versus all three replacement modules |
| Selected Rocq logic sources | 45,538 bytes / 1,399 lines | 17,647 bytes / 371 lines | Both original developments versus all three replacement modules |
| Shared Lean derivation nodes | 164 MP applications | 60 MP applications | Shared schematic proofs, excluding the unchanged one-MP lifting rule |
| Selected Lean runtime sources | 86,896 bytes / 1,321 lines | 103,551 bytes / 1,651 lines | Simulator interface, bridge, site batches and facade; audit client excluded |

The basis change removes duplicated mathematics. The runtime change adds a
reusable semantic proof and factors the common decoder prefix out of per-site
symbolic execution. Its current source is larger; no controlled whole-endpoint
speedup is claimed. All 4,751 primitive leaves and 6,176 guarded branch outcomes
are retained.

The common basis architecture and semantic-coverage interface are prior work
already present in the repository's proposal tree. The new local contraction
derives S from existing `d34`, `d55`, and `d57` with two additional MP steps
instead of the earlier extension's five. The synchronized adapters and the
checked residual connection make those interfaces concrete against the current
maintained sources. No global shortest-proof or machine-state reduction claim
is made.

The current maintained endpoint has 179 project modules. The Lean basis change
alone adds one small pure module while reducing source mass. Do not report this
change as a reduction in import-module count.

The report also recommends implementing the existing direct full-seed proposal
as a deeper next step. This could remove the first indiscernibility quotient
from Lean's lower consistency argument. Three exclusive old modules contain
15,508 bytes and 339 lines, but this is a gross candidate removal: the new
support and named-semantics lemmas have not been implemented or counted. It is
a reviewed research direction, not a checked patch in this packet.

## Reproduction

Use a checkout of the exact baseline commit and fresh output directories.
The proof drivers never modify that checkout. See the component READMEs for
their toolchain and normalization details.

```sh
python3 tools/verify_packet.py

python3 lean_basis/check_lean.py --repo /path/to/ProveIt \
  --lean /path/to/lean-4.32.0/bin/lean --out /tmp/k215-basis-lean
python3 lean_basis/compare_axioms.py --results /tmp/k215-basis-lean \
  --out /tmp/k215-basis-lean/axiom-comparison.json
python3 lean_basis/check_regeneration.py --repo /path/to/ProveIt \
  --out /tmp/k215-basis-generation

python3 rocq_basis/verify_bundle.py
python3 rocq_basis/check.py --compat-818 --out /tmp/k215-basis-rocq
python3 rocq_basis/check_regeneration.py --repo /path/to/ProveIt \
  --reference /path/to/pinned-k230-rocq --out /tmp/k215-rocq-generation

python3 residual_sites/replay.py --lean /path/to/lean-4.32.0/bin/lean \
  --repo /path/to/ProveIt --out /tmp/k215-residual-runtime
python3 residual_sites/adapt_sites.py --repo /path/to/ProveIt \
  --out /tmp/k215-residual-generation
```

The pinned K230 reference is
`elliotglazer/k230-rocq@3142e4dd980f0be12f4abb636c4ae2528afc17eb`.
The local Rocq checks used Coq 8.18.0, with explicitly recorded `Stdlib` to
`Coq` import and line-ending normalization. For the production environment,
omit `--compat-818` and pass matching `--coqc` and `--coqchk` paths. The
repository's Rocq 9.1.0 endpoint gate still has to run.

The runtime component's README gives its complete finite-check command and
lists its checked modules. The independent source audits can be reproduced
with their own `--help` options. The small discovery search can be rerun with:

```sh
python3 tools/find_s.py --out /tmp/k215-s-search.json
```

This is an untrusted search aid over a specified schema pool. Its output is
not a proof and its failure to find a shorter term is not a lower bound.

Build the report with a LaTeX installation providing the standard packages
listed in its preamble:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error k215_basis_residual.tex
```

## Integration

Each component supplies a repository-relative overlay and a reviewable patch.
Use `git apply --check` before applying a patch, and do not replace later
production work with this pinned snapshot merely to avoid a merge conflict.
The proposed endpoint adapter is explicitly named `endpoint-UNCHECKED.patch`:
its public statement types have been reviewed, but it has not been compiled
as part of the complete endpoint closure.

Before adopting these changes, regenerate maintained outputs, rebuild the
affected transitive consumers under the production toolchains, recompile the
original final typed clients, compare named axiom profiles, and perform the
repository's recursive Rocq endpoint audit. Retain the source/import/object
bindings for any authorized reuse. Do not replace production acceptance
receipts with this packet's focused component receipts.

The external endpoint remains the exact concrete-machine halting / formal-ZFC-
refutation equivalence, and its negated counterpart. This packet does not add
an internally arithmetized PA or ZFC endpoint or establish unconditional
nonhalting. The report explains this distinction without changing the project's
consistency-calibration goal.

## Evidence and attribution

`MANIFEST.json` binds the distributed payload by SHA-256. The integrity checker
detects changes to those files; it is not a kernel proof checker or a signature
from an external auditor. Compiler logs and structured records are included;
compiled proof objects and toolchain binaries are intentionally reproducible
outputs rather than payload.

`NOTICE.md`, `LICENSE.ProveIt`, the component notices, and
`source-provenance.json` preserve source attribution and exact pins. Suggested
repository location:
`k225-formal/verification/k215/simplification/proposals/two-detachment-residual/`.
