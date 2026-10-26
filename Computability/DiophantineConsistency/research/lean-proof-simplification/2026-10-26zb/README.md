# Additional Lean proof simplifications

Four direct edits and two optional interfaces for
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt),
`Computability/DiophantineConsistency`. Review date: 26 October 2026.

Start with **report/report.pdf**. Its complete editable source is
**report/report.tex**, including **report/validation-summary.tex**.

## Results

| ID | Target / idea | Complete module before → after | Net lines removed |
|---|---|---:|---:|
| A | Helical row-zero theorem as a period-one orbit | 147 → 136 | 11 |
| B | Coprime cancellation for combined divisibility | 180 → 173 | 7 |
| C | Geometric estimate from the exact geometric identity | 150 → 145 | 5 |
| D | Positive quadratic margin as a linear interval | 141 → 133 | 8 |
| | **Four direct patches** | **618 → 587** | **31** |
| E | Finite signed-prefix quotient and remainder contract | Additional module | Not claimed |
| F | Exact native-rank comparison through C + qF | Additional module | Not claimed |

The five existing theorem headers and all executable definitions in the four
patched modules are unchanged. One explicit geometric-sum import is added and
included in the line counts. E and F add code; adopt them when enough clients
benefit. No performance improvement or whole-repository line reduction is claimed.

## Source pins and exclusion baseline

The patches and compiler validation target commit:

`29936089835c0c55cca81edc86b4fb0c70ce34d5`

The initial exclusion audit covers all 21 placed packets a–u, including ideas in
notes and prototypes, and `docs/incoming` at that commit. Earlier suggestions are
treated as applied, even if their implementation was deferred. The machine-readable
exclusion ledger has 120 entries, supported by manuscript anchors and a corpus
manifest. The 1,143-file inventory is a provenance record, not an idea count.

A final freshness check used commit:

`45ac0dfc366f798d4686070a89d66e8dafdb6879`

It adds packet **v**. The supplemental audit in
`evidence/late-packet-v-audit.md` checks that packet separately and brings the
exclusion coverage to **22 packets, a–v**. The four patched target files are
unchanged at this later commit. Some dependencies changed, so the compiler results
are deliberately attributed only to the original tested pin. The supplemental
freshness receipt records the exact comparison and its scope.

The novelty claim is relative to the supplied prior-proposal corpus. It is not a
claim that periodicity, coprime cancellation, Euclidean division, or affine order
comparison is new mathematics.

## Archive contents

- `report/`: PDF and XeLaTeX source.
- `patches/`: four independent unified diffs and `all-four.patch`.
- `baseline/DiophantineConsistency/`: exact original target files.
- `proposed/DiophantineConsistency/`: complete proposed replacements.
- `lean/`: optional actual-source APIs and compact proof/axiom examples.
- `evidence/`: source hashes, line counts, exclusion audit, version manifests,
  compiler receipts, and review notes.
- `logs/`: full focused replay output, with the separate endpoint audit.
- `scripts/check_sources.py`: source, statement-header, line-count, and patch checks.
- `scripts/replay.py`: focused compilation in an isolated object overlay.
- `SHA256SUMS`: SHA-256 checksums for every other distributed file.

No compiled Lean objects, toolchain binaries, dependency caches, or full historical
proposal snapshots are bundled.

## Check the files without compiling

Use Python 3.10 or newer. From the extracted archive directory:

```bash
python3 scripts/check_sources.py
sha256sum -c SHA256SUMS
```

For a checkout of the exact source pin, also check that the original files match
and that the combined patch applies without changing the checkout:

```bash
python3 scripts/check_sources.py --repo /absolute/path/to/ProveIt
```

The script deliberately rejects a different checkout HEAD. That makes a later
port an explicit review task rather than an accidental change of validation scope.

## Reproduce the Lean checks

Prerequisites: Lean 4.32.0, the repository's pinned `lake-manifest.json`, and a
working dependency cache or a normal source build. The exact manifest and toolchain
file are included under `evidence/`. Mathlib is pinned to
`81a5d257c8e410db227a6665ed08f64fea08e997`.

In a separate checkout of ProveIt, check out the tested revision:

```bash
git checkout 29936089835c0c55cca81edc86b4fb0c70ce34d5
```

Run the repository's usual dependency setup. Then build the baseline modules
needed by the replay (from that checkout):

```bash
lake build \
  DiophantineConsistency.WangTiles942HelicalQuotient \
  DiophantineConsistency.RatioReparameterization \
  DiophantineConsistency.PolynomialRangeBounds \
  DiophantineConsistency.MarginSeparation \
  DiophantineConsistency.SparseBorrowCarry \
  DiophantineConsistency.NativeRankVariation
```

From this archive, with the correct Lean executable on PATH, run:

```bash
python3 scripts/replay.py \
  --repo /absolute/path/to/ProveIt \
  --work-dir /absolute/path/to/a-new-empty-directory
```

The script invokes Lean from the repository directory, checks its version, and
uses the repository's `.lake/build/lib/lean` and package object directories.
`--lean /path/to/lean`, `--objects /path/to/baseline/objects`, and
`--packages /path/to/.lake/packages` allow explicit locations. This was used for
the included receipt, with freshly rebuilt project objects and a matching pinned
external package cache.

The script writes only to the new work directory. It compiles the four proposed
modules, compares the five changed theorems' axiom reports, compiles the existing
helical checks and ratio-margin finalizer, and compiles the two optional interfaces
plus two compact examples. A nonempty work directory is refused. Successful runs
produce `records.json` and `logs/` there. A full build of every repository module
is outside this focused check.

To adopt the reviewed direct changes later, the combined diff is:

```bash
git -C /absolute/path/to/ProveIt apply /absolute/path/to/this-archive/patches/all-four.patch
```

Alternatively, apply the four individual patches independently. This archive does
not apply any patch automatically. E and F remain separate research modules.

## Rebuild the PDF

Install XeLaTeX with the packages declared in the preamble and the fonts
Bitstream Charter, Latin Modern Sans, and DejaVu Sans Mono. From `report/`:

```bash
xelatex -interaction=nonstopmode -halt-on-error report.tex
xelatex -interaction=nonstopmode -halt-on-error report.tex
```

The second pass resolves the table of contents. Both TeX input files are required.
The delivered PDF was rendered and visually inspected after the final text change.

## Verification scope

The dependency receipt contains 62 project modules rebuilt from the tested source
pin, plus one mathlib module rebuilt from the pinned package source. Other external
package objects were reused from a matching cache. All compiled objects were
nonempty. All four complete replacement modules and both existing focused clients
passed. Baseline and replacement axiom reports for the five changed proofs were
identical. The optional modules import the production definitions; they do not
validate lookalike copies in place of the actual interfaces.

The work changes intermediate proofs and proposes optional specifications. It does
not solve the project's remaining global controller, mutation-existence, equation
completeness, or foundational consistency obligations.
