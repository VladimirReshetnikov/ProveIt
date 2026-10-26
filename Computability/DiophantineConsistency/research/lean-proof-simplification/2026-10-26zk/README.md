# Four further Lean proof simplifications for DiophantineConsistency

Prepared 26 October 2026 against ProveIt commit
`9f35798db4a63c25e435fca14d75931144657d7e`.

Read `report/report.pdf`; its complete XeLaTeX source is `report/report.tex`.

## Contributions

1. **A — Shared Jones finalizer evaluation.** Export five existing concrete
   evaluation lemmas and remove their duplicate implementation. Candidate
   reduction: 49 physical lines; executable definitions unchanged.
2. **B — Affine reflection for the thirteen-coordinate carrier.** Prove one
   integer positivity lemma and reuse it through `(m,G,y) -> (-m,-G,2-y)`.
   Candidate reduction: 13 lines, including the helper and its documentation;
   original public signatures and witness are preserved.
3. **C — Direct homogeneous enumeration.** Replace the filtered `Fin 5`
   Cartesian enumeration by `List.Nat.antidiagonalTuple`. Candidate reduction:
   42 lines, provided three unused public helpers are retired. This changes
   the emitted expression tree and needs a syntax-compatibility decision.
4. **D — Weaker fixed-controller facts.** Replace four uses of exact fixed
   multiplicative orders by fixed-power or annihilation facts. Candidate
   reduction: one line, including the iterator. Exact-order declarations and
   the necessary auxiliary prime-power orbit argument are retained.

The four proposals were screened against 23 filed packets and five incoming
ZIPs. `audit/novelty-audit.md` records the exclusions and exact limits of that
screen. Novelty is relative to that source corpus, not mathematical priority.

## Verification scope

The four standalone Lean files under `lean/` passed Lean 4.32.0 using the
recorded mathlib version. Their complete final logs are included. No successful
core relies on `sorry`, `admit`, `sorryAx`, or `native_decide`.

The four patches are candidate repository edits. They pass applicability
checks against exact baseline fixtures, and A/B have separate audits that
executable definitions are unchanged. There is **no claim of a clean build of
the entire pinned ProveIt dependency closure**. The optional whole-module
Thirteen attempt was stopped; it is recorded as incomplete, not successful.

The per-patch line counts include helper code and comments. They are not
compile-time measurements or kernel proof-term reductions. A and C edit
separate blocks of the same file; review them as separate decisions.

## Reproduce

With Lean/Lake available on PATH and an existing checkout containing the pinned
dependencies:

```sh
python3 scripts/replay_lean.py /absolute/path/to/ProveIt
python3 scripts/check_patches.py
bash scripts/build_report.sh
```

Report build prerequisites: XeLaTeX, `fontspec`, `fvextra`, Latin Modern fonts,
and DejaVu Sans Mono. The compiled PDF is included.

The replay script compiles only the four standalone files. It does not apply
patches. The patch check is read-only and uses the included baseline fixtures.

To review or apply an individual patch in the actual pinned repository:

```sh
git apply --check /absolute/path/to/patches/A-jones-shared-evaluation.patch
# Apply only after reviewing its documented scope and integration gate.
git apply /absolute/path/to/patches/A-jones-shared-evaluation.patch
```

No changes have been pushed to the upstream repository.

## Contents

- `report/`: complete report source and compiled PDF.
- `lean/`: successful standalone proofs and final compiler/axiom output.
- `patches/`: four independent candidate diffs.
- `baseline/`: exact target source fixtures for reviewing/applying those diffs.
- `audit/`: novelty ledger, independent review, source hashes, metrics,
  applicability, data-preservation evidence, validation scope, source maps.
- `scripts/`: reproduction and inspection commands.
- `lean-toolchain`, `lake-manifest.json`: upstream dependency version evidence.
- `SHA256SUMS.txt`: archive contents checksums, excluding this checksum file.

Upstream source fixtures retain their original project provenance. The upstream
repository's license remains authoritative for those fixtures.
