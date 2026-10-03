# Research Report 38

## First Revisit Detection and Exact Pattern Queries for Finite Defect Periodic Turmites

The article proves that first-position revisit is in P for an explicit cyclic
L/R rule and explicit periodic tile, with binary finite defects and starting
coordinates. It returns the exact first repeated arrival or a global no-revisit
certificate, using polynomial-size affine lanes even for exponentially late
revisits. A separate complete standard-library implementation computes exact
first hits of finite unions of heading, coordinate-congruence, finite head-site,
and head-relative colour-stencil clauses. No polynomial bound is asserted for
that observation compiler's Boolean expansion.

The board is observed before departure. On a repeat-producing run the query
domain is time zero through the first repeated arrival, inclusive. On a
certified no-revisit run it is all nonnegative times. Finite head-relative
observations are eventually periodic, but whole-board translation periodicity,
physical halting, a completed literal two-visit universal atlas, and a sharp
one/two threshold are not claimed. The report makes no novelty assertion.

## Read

- `Research_Report38.pdf`: the complete mathematical article, with full proofs,
  explicit bit bounds, exact huge examples, a checked static diagram, evidence
  scope, and focused open questions
- `Research_Report38.tex`: the editable self-contained LaTeX source
- `evidence/source-packet/`: all 31 frozen source files, byte-for-byte, including
  historical boundary context, active code, original logs and independent reviews
- `INTEGRITY.md`: trust model, exact source identity, execution allowlist,
  output restrictions, reproducibility assumptions and maintainer procedure
- `verification/`: exact source lineage, stable expected outputs, replay plan,
  article-byte approval, and any curated release review records

## Trust before execution

Authenticate the complete ZIP using its independently supplied SHA256 and a
trusted external hashing tool before running any packaged helper. An
unauthenticated verifier cannot authenticate itself. Do not reseal a received
release merely to make it pass. `MANIFEST.json` inventories the payload;
`SHA256SUMS` records exact final file digests, including the verifier's actual
bytes. `INTEGRITY.md` explains the single normalized self-pin line.

The frozen source manifest SHA256 is:

`7dfd4f270ad7bf667bc123aace7bd97fd13b992949a9dfc8e3dca3f8105cea62`

The enclosing verifier pins this manifest and all six approved active Python
files. The packet's own verifier and every historical boundary-context program
remain inert. No upstream repository code or arithmetic schedule is executed.

## Offline replay

From the authenticated release directory, using Python 3.10 or later:

```
python -I -B verify_release.py --verify-only
python -I -B verify_release.py --replay --workdir ../report38-replay-normal
python -I -B -O verify_release.py --replay --workdir ../report38-replay-optimized
```

Choose external work directories outside the release. Every full
replay executes both normal and optimized Python modes for the 16 author test
groups, seven independent test groups and the exact example. Test exit codes
are checked explicitly. Stable outputs must match the frozen scientific
results; only the unittest elapsed-time field is normalized. Original logs and
their original timings are preserved unchanged. All fresh output is external.

The verifier stages only the six pinned active source files, rejects release
internal output paths including symlink resolutions and hostile temporary
settings, and checks original/copy/runtime bytes, modes and mtimes. These are
execution-allowlist and preservation checks, not an OS sandbox for arbitrary
malicious programs.

## Rebuild the PDF

A local TeX Live pdfLaTeX installation with the article's listed standard
packages and fonts is required. No installation or network is attempted.

```
python -I -B build_pdf.py --output ../report38-pdf-build --check-packaged
```

Three no-shell-escape passes use fixed dates and external caches. The rebuilt
PDF must equal the packaged PDF byte-for-byte. Reproducibility assumes the same
installed TeX engine, packages and fonts. Do not edit the release concurrently
with a build or replay; preservation checks intentionally reject that change.

## Rebuild and validate the ZIP

```
python -I -B archive_release.py --create ../Research_Report38_rebuilt.zip
python -I -B archive_release.py --check ../Research_Report38_rebuilt.zip --sha256 DIGEST --replay
python -I -B tamper_regression.py
python -I -B archive_regression.py --archive ../Research_Report38_rebuilt.zip --sha256 DIGEST
```

Replace `DIGEST` with an independently computed SHA256 of the intended archive.
ZIP construction fixes order, metadata and compression. Checking validates every
member against the verified local tree before manually extracting only matched
regular files into an external moved directory. Traversal, absolute paths,
duplicates, symlinks, bad modes, changed/missing/extra files and other hostile
members are rejected. `--replay` runs complete normal/-O replay from the moved
copy. The regression helpers keep their temporary mutation probes external.

## Practical scientific entry point

For application use, `observations.solve` constructs the path and query from
the same inputs. The lower-level `first_hit` requires an unmodified certified
result belonging to the same rule, tile, defects, start and heading; it does not
independently authenticate arbitrary supplied result objects. Clause fields are
materialized once to immutable tuples, so one-shot iterables are safe to reuse.

The illustrative no-defect RL checkerboard query asks for heading north,
x divisible by 10^100, current colour zero, and colour one at offset (-1,-1).
Its exact first hit is 2*10^100 at (10^100,10^100), represented by four lanes.
Adding a colour-one defect at (10^100,10^100) instead gives an exact first
revisit at 2*10^100+2, represented by six lanes.

Finite tests corroborate the proof; finite prefixes cannot alone establish
infinite nonoccurrence. The article states the exact proof and test boundaries.
