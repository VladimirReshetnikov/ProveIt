# K215 proof simplification: checked component proposal

Baseline: [VladimirReshetnikov/ProveIt at
57541fe0cfe3af62b4cb58747d8d1d7c16b338d5](https://github.com/VladimirReshetnikov/ProveIt/commit/57541fe0cfe3af62b4cb58747d8d1d7c16b338d5).
Prepared October 21, 2026.

**Read `report.pdf` for the mathematical argument, measurements, attribution,
and exact validation scope.** `report.tex` and `verified-metrics.tex` are its
complete editable sources. The three integration patches apply to the pinned
revision and leave the machine, source program, encoding, and public endpoint
statements unchanged.

## Recommendation

1. Share the six-goal implication derivation between the dominated numerical
   calculus and unrestricted named logic. Synchronize its maintained producer.
2. Construct the full seed directly from original-formula satisfaction, avoiding
   the preliminary indiscernibility quotient in the Lean endpoint proof path.
3. Share the Rocq enumerator's progress, prefix transport, and completeness
   argument at the common command boundary, preserving every existing helper API.

These ideas have antecedents in the repository. This packet implements the prior
direct-seed outline, integrates the preserved shared-basis work with the current
producer, and offers a conservative alternative to the prior Rocq seed-rank
proposal. It contributes checked current-source integrations and reproducible
evidence; it does not claim a new underlying axiom basis or a smaller machine.

## Measured results

| Scope | Before | Proposed | Change |
| --- | ---: | ---: | ---: |
| Two Lean implication files, lines | 811 | 401 | -410 |
| Two Lean implication files, bytes | 42,454 | 18,243 | -24,211 |
| Implication pair plus maintained producer, bytes | 52,651 | 28,760 | -23,891 |
| Direct-seed selected endpoint closure, modules | 179 | 178 | -1 |
| Direct-seed selected endpoint closure, bytes | 2,129,439 | 2,121,905 | -7,534 |
| Both Lean changes, selected endpoint closure, bytes | 2,129,439 | 2,097,694 | -31,745 |
| Two Rocq compiler/seed files, lines | 410 | 403 | -7 |
| Two Rocq compiler/seed files, bytes | 18,100 | 17,833 | -267 |

These are source measurements, not proof-term sizes or build-speed benchmarks.
Retaining the legacy semantic APIs grows the directly touched semantic production
files by 6,795 bytes; the direct-seed saving above is on the selected endpoint's
dependency boundary. The later tagged-domain quotient and well-founded model
construction remain in that proof.

## What was checked

- The delivered Lean reproducer freshly compiled **116 project modules** in one
  clean replay under **Lean 4.32.0**. It checked **26 exact selected assumption
  reports**. Added and modified proofs and audit clients have **zero warnings**;
  18 linter warnings occur in unchanged upstream sources. The pure implication
  basis is axiom-free; semantic reports use subsets of `propext`,
  `Classical.choice`, and `Quot.sound`.
- The generic `KEndpoint` and typed old-interface clients are included in that
  Lean replay. The literal machine-specific **`KEndpoint215` was not rebuilt**.
- Rocq baseline and candidate each freshly compiled **11 modules** under
  **Coq 8.18.0 / OCaml 4.14.1**, with 9 and 12 closed assumption reports respectively.
  Both recursive `coqchk` runs passed. All **46 original theorem headers** match.
  The full production **Rocq 9.1 machine endpoint was not rebuilt**.
- Source checks validate the pinned baseline, producer outputs, unchanged
  numerical adapter, generated Rocq namespace variants, template digests, and
  patch applicability. All 199 phase-twelve source bindings match the baseline.

The result is a checked component and generic-endpoint proposal. Production
adoption still requires the full machine-specific endpoint checks with the
repository's maintained toolchains and receipt procedure. This packet does not
add an arithmetized proof inside ZFC or PA; it improves the existing external
proof-assistant development.

## Archive contents

| Path | Purpose |
| --- | --- |
| `report.tex`, `report.pdf`, `verified-metrics.tex` | Complete report and editable LaTeX |
| `patches/01_shared_basis.patch` | Shared implication pair and maintained producer |
| `patches/02_direct_seed.patch` | Direct seed proof, shared interface, endpoint clients, typed audit |
| `patches/03_rocq_boundary.patch` | Maintained/generated Rocq sources and manifest entries |
| `patches/all.patch` | The same three patches concatenated in order |
| `lean/` | Self-contained 116-module joint source snapshot, reproducer, provenance, final logs and receipts |
| `producer/` | Maintained producer, pinned inert inputs, expected generated outputs, source metrics |
| `rocq/` | Baseline and candidate sources, maintained templates, reproducer, recursive-check logs |
| `audit/` | Independent baseline/closure/API and mathematical reviews |
| `Makefile` | Convenience targets for document and component reproduction |
| `MANIFEST.sha256` | SHA-256 of every delivered file except the manifest itself |
| `LICENSE.ProveIt`, `NOTICE.md` | Upstream license and attribution |

No compiled Lean or Rocq objects are distributed. The object hashes in the
receipts describe the completed local fresh checks; they do not require trusting
or reusing a received object. `lean/source_bindings.json` maps snapshot modules
back to their original repository paths and source hashes.

## Reproduce the component checks

Commands below run from the extracted archive directory. Use Python 3.11 or later
for all scripts, a POSIX environment for the Rocq build lock, and the stated
proof-assistant versions. No checkout or network access is required for these
component replays once the toolchains are installed.

First verify the distributed files and input-only checks:

```sh
sha256sum -c MANIFEST.sha256
make check-inputs
make check-producer
```

Then build every Lean object afresh:

```sh
python3 lean/reproduce.py \
  --lean /absolute/path/to/lean-4.32.0/bin/lean \
  --out /absolute/new/lean-output
```

The requested output directory must not exist. The script checks the exact
toolchain, inventory, source hashes, imports, proof-hole/assumption screening,
compiler exits, selected assumption profiles, and warnings in changed files.
It creates all project objects in the new output tree.

Reproduce the Rocq baseline and candidate checks:

```sh
python3 rocq/reproduce.py \
  --coqc /absolute/path/to/coqc \
  --coqchk /absolute/path/to/coqchk \
  --out /absolute/new/rocq-output
```

The output directory must again be new. Coq 8.18 build copies normalize only
`From Stdlib Require` to `From Coq Require`; the production snapshots retain their
original spelling. A different compatible Rocq toolchain produces new evidence
and is not the toolchain used for the supplied receipts.

To regenerate the PDF, install a standard TeX Live distribution with `pdflatex`,
Latin Modern, `microtype`, `needspace`, and the other packages listed in the TeX
preamble, then run:

```sh
make pdf
```

## Integrate into ProveIt

Use a clean isolated branch based on the pinned revision. In that checkout:

```sh
git switch -c k215-proof-simplification \
  57541fe0cfe3af62b4cb58747d8d1d7c16b338d5
git apply --check /absolute/path/to/packet/patches/all.patch
git apply /absolute/path/to/packet/patches/all.patch
python3 Computability/BusyBeaver/Research/ZFC/k225-formal/generate_dominated_implication_lean.py --check
```

Use either `all.patch` or the three numbered patches in order; do not apply both.
The supplied artifact preparation did not modify or push the upstream checkout.
The research packet itself can be placed under the repository's existing K215
simplification research directory; that documentation placement is separate from
the production patches.

Before labeling the integration adopted, regenerate the normal Rocq namespace
variants and manifest bindings, rebuild the actual machine-specific Lean and
Rocq endpoints, and compare their exact theorem types and assumption profiles.
Retain the new source/dependency/object receipts through the established workflow.
Unchanged machine certificates are reusable only under that workflow's exact
binding checks. Existing accepted receipts are left intact by these patches.

To reproduce the source-only baseline audit, use an unmodified checkout at the
pin with its referenced directories populated:

```sh
python3 audit/audit_current.py /absolute/path/to/ProveIt \
  --output /absolute/new/baseline-audit.json
```

This checks source identities and public declaration text. It makes no fresh
kernel-compilation claim. See the report's final section for further research:
shared bundle semantics, direct `FormSeed` construction, reusable primitive suffix
proofs, a general scheduler contract, and multi-goal proof-DAG optimization.
