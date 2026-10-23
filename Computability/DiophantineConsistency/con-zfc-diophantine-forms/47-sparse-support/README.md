# Sparse support packing for explicit Diophantine consistency equations

Prepared for Vladimir Reshetnikov and ProveIt, 23 October 2026.

Read **`report/report.pdf`** or its complete editable source
**`report/report.tex`** first. This is a new research contribution relative to
ProveIt snapshot `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.

## Results

Each equation has fixed, completely specified integer coefficients. Its
lack of solutions in the stated domain is equivalent in ZFC to Con(ZFC),
using the inherited compiler theorem and the arithmetic dependencies
identified in the report. Intermediate circuit registers introduce no
additional quantified variables.

| Domain | Construction | Exact total degree | Live binary operations |
|---|---|---:|---:|
| 9 positive integers | Package 45 baseline | 129,875,980 | 788 |
| 9 positive integers | New, maximum weight 239 | 25,936,016 | 651 |
| 9 positive integers | New, maximum weight 220 | 23,878,392 | 670 |
| 10 unrestricted integers | Package 40 baseline | 237,520,456 | 782 |
| 10 unrestricted integers | New, maximum weight 239 | 71,151,176 | 662 |
| 10 unrestricted integers | New, maximum weight 220 | 65,506,504 | 675 |

The nine-nonnegative-variable versions have the same degrees and cost 655
and 674 operations. These are separate, correctly shifted input circuits.
The nine-positive equation must not be interpreted over unrestricted
integers. Each binary addition, subtraction and multiplication costs one,
including multiplication by a fixed constant. Fixed leaves and reuse are
free, and all fixed powers are expanded into multiplication gates.

The main new idea is to separate only the **71 monomials used by the fixed
quadratic source** from the **528 possible quadratic expansion monomials**.
Two unused monomials may collide. This weaker sufficient condition admits
explicit certified weight vectors of maximum 239 and 220, instead of 799.
For nine variables, the former large additive base constant can instead
multiply a square; this lowers variable degree without increasing the
fixed coefficient payload. Removing one empty target position supplies a
further small improvement. The report gives the extraction, carry,
positivity, finalizer and exact-degree proofs.

The two weight vectors represent different degree/operation tradeoffs.
No globally simplest polynomial or optimal weight vector is claimed.
The repository's 67-operation higher-variable construction and its
quartic alternatives remain separate comparison points.

## Contents

- `report/`: the article in LaTeX and PDF, with the complete nine-variable
  definition and the unrestricted-integer supplement.
- `construction/`: literal polynomial DAGs, all coefficient payloads and
  recipes, source certificates, generators, independent audits, mathematical
  proof and optional discovery search.
- `minima/`: a secondary 15-positive-variable, degree-44 minimum-norm
  refinement, including 75- and 76-operation forms. Its historical comparison
  and inherited signed-recovery dependency are stated separately.
- `evidence/`: exact pinned source proofs, the native coefficient builder
  with literal machine/tiles, and the repository's formalization-status
  documents. Upstream files are retained with their original statements;
  they are not rewritten to assert the new result.
- `verification/`: recorded release checks and visual-PDF review record.
- `SOURCE_PINS.json`: immutable provenance for included evidence files.
- `RELEASE_HASHES.json`: SHA-256 manifest of all release files except itself.

Licenses and notices for inherited material are in
`construction/licenses/`, `minima/licenses/`, and the copied source tree.
New material is supplied for incorporation in ProveIt. No third-party
license is overridden. See `NOTICE.md`.

## Reproduce

Python 3.10 or later, with only its standard library:

```sh
python3 verify_release.py
python3 -O verify_release.py
```

The release driver checks every file hash and source pin, copies the
package to a temporary directory, verifies all six principal circuits,
reproduces the native coefficient tuple from the literal transition and
tile data, and checks the secondary minimum-norm circuits. The supplied
release is unchanged. The construction audit regenerates the finite
artifacts and requires byte equality. Optional weight search is not run
and is not needed to verify the result.

The nine-variable degree audit expands the two equivalent finalizers in
an abstract polynomial ring, compares all 232 terms exactly, and proves
the nonzero leading coefficient symbolically. The ten-integer audit finds
a nonzero coefficient at the propagated degree bound modulo each of two
primes; that is an exact nonvanishing certificate, not a probabilistic
degree estimate. Modular evaluations are additional transcription checks.

To rebuild the PDF with a normal TeX Live installation:

```sh
make pdf
```

No shell escape or external bibliography download is required. The supplied
PDF was compiled and all its pages were visually reviewed.

## Meaning and verification boundary

The main transfer theorem preserves the exact 31-positive-variable,
22-quadratic-residual source system with the coherent native four-port
tuple. The connection of that system to ZFC refutability is the inherited
ordinary compiler theorem and calibrated K215 endpoint. The nine-variable
arithmetic bridge is the Jones ratio theorem; the ten-integer construction
also retains the repository's reliance on Sun's 2026 preprint.

This package supplies ordinary mathematical proofs and executable finite
checks. It does not claim a new end-to-end Lean/Rocq build or a newly
exported object-language ZFC derivation. Those proof-assistant obligations
remain as documented in the pinned repository. No consistency assumption
is used, no search is claimed to decide whether a zero exists, and no
test result is presented as a proof of Con(ZFC).

The incoming-report index was read at the same pin. Its wave-5 queue
summary lags the actual wave-6 files; the comparisons use packages 40 and
45 themselves. This delivery is one self-contained manuscript package;
it does not assign itself a repository source number or modify the repo.
