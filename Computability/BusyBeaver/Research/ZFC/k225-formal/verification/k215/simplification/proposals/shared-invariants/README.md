# K215: shorter proofs through shared invariants and exact runtime contracts

Research and implementation packet for ProveIt, reviewed against:

`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`

Read `report.pdf` for the mathematical arguments, source analysis, validation
ledger, and recommended adoption order. `report.tex` and both included TeX
files reproduce the complete report. All proof and generator sources are
included or pinned to exact prerequisite bytes in the named checkout.

## Immediate recommendation

1. Adopt the new one-invariant `KDenseBridge.blank_iff` proof. It removes the
   second induction without changing imports or the public theorem type.
2. Adopt the repository's existing six-goal implication core and make
   `Lukasiewicz` its unrestricted instance. The packet freshly checks its
   current clients and supplies the accompanying producer/input update.
3. Integrate the completed exact decoder-prefix/residual component through
   semantic coverage. All 4,751 leaves and 6,176 guarded outcomes, plus its
   source/table equivalence, have passed Lean checking; its 51-module ledger
   records the resumed component build separately from full endpoint integration.
4. For Rocq, prioritize the existing smaller implication sources and
   production generator wiring. Adopt common transports where multiple
   actual clients justify their source overhead.

The first two changes reduce the **three selected Lean files** from 1,004
to 571 physical lines and from 50,581 to 25,566 UTF-8 bytes. These are
43.1% and 49.5% reductions in that selected scope. The complete current
endpoint source closure is 179 project modules and 2,129,439 bytes, so
the selected byte saving is about 1.17% of that closure. Generator,
documentation, audit, and optional infrastructure files are outside the
three-file comparison.

## Contents

| Directory | Role |
| --- | --- |
| `shared-basis/` | Two-file proof patch, producer-wiring patch, full 16-module component, derivation/renderer, successful logs and interface review |
| `lean-bridge/` | Recommended small patch; separate optional terminal-drain implementation; fresh component drivers, audit clients and logs |
| `decoder-residual/` | Exact role selector, all-occurrence residual certificates, semantic source/table facade, source pins and validation ledger |
| `rocq-components/` | Checked standalone finite-cleanup theorem, optional family relabeling experiment, adoption map and existing implication patch |
| `subtree-abbreviation/` | Separate uncompiled proposal to write each finite-check path once, with exact static rewrite and measurement |
| `evidence/` | Pinned current closure and source measurements, review records |

Each component README is authoritative for its exact validation scope.
The unchanged 215-state machine and the existing consistency-equivalence
statement are preserved. No fresh complete machine-to-ZFC endpoint build,
internally encoded PA/ZFC derivation, or unconditional non-halting proof is
claimed.

## Apply the immediate changes

In a clean checkout of the pinned revision, substitute the absolute path
where this packet was extracted:

```bash
git apply --check /path/to/k215-proof-simplification/shared-basis/shared-basis.patch \
  /path/to/k215-proof-simplification/shared-basis/producer-wiring.patch \
  /path/to/k215-proof-simplification/lean-bridge/minimal.patch

git apply /path/to/k215-proof-simplification/shared-basis/shared-basis.patch \
  /path/to/k215-proof-simplification/shared-basis/producer-wiring.patch \
  /path/to/k215-proof-simplification/lean-bridge/minimal.patch
```

The combined `--check` succeeded during preparation; no production file
was modified. The `terminal-drain.patch` alternative also changes
`KDenseBridge`; do not apply it together with `minimal.patch`.
The optional cleanup experiment and the residual architecture also use
different `KSim` replacements; their isolated build variants are not a
single stack of patches. Combining them requires an explicit integration.
Follow the component instructions, then run the repository's full endpoint
gates after integration. Do not treat old receipts for different source
hashes as proof of the final production build.

## Reproduce and inspect

- Lean: 4.32.0, matching the repository pin. See each component's build script.
- Coq component validation: 8.18.0. Production Rocq adoption needs its 9.1.0 gate.
- PDF: run `make report`; the source uses ordinary pdfLaTeX packages.
- File integrity: run `python3 verify_integrity.py`.

No compiler binaries or compiled project objects are distributed. Receipts
bind source, output, and log hashes; a hash is an identity check, not a proof.
Local timings are descriptive observations, not a controlled whole-endpoint
speed comparison.

The independent subtree-abbreviation proposal removes 18,803 bytes of repeated
statement text across nine existing batch files; its 238-byte shared helper
leaves a net source saving of 18,565 bytes across ten selected files.
That is a source-only result; it is not part of the three-file checked saving
and does not claim fewer finite checks or faster evaluation.

See `NOTICE.md` for prior-work attribution and `LICENSE` for MIT No Attribution
terms.
