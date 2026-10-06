# Report 125: A279571 leading equivalent and threshold inverse

This reader package contains a standalone proof, its editable LaTeX source,
exact integer data, and offline finite checks. The main theorem is

    a_n ~ C_A 9^n n^(-kappa),
    kappa = 1 + pi / arccos(2 / sqrt(7)),  0 < C_A < infinity.

The amplitude is characterized by Brownian-normalized forward and reversed
killed harmonic functions and an absolutely convergent positive endpoint
series. Original-time strong approximation, explicit two-order color
correctors, a deep entrance argument, side-uniform Brownian limits,
last-window smoothing, and endpoint domination are fully included.

The inverse threshold N(y) has real center

    v(y) = [log y + kappa log log y - kappa log log 9 - log C_A] / log 9

and satisfies ceil(v-epsilon) <= N(y) <= ceil(v+epsilon), with a positive
existence envelope epsilon(y) tending to zero. Near integers this does not
imply an unconditional exact ceiling identity. The proof also includes the
unique convergence-circle singularity at 1/9 and non-D-finiteness over C(z).

No fitted amplitude digits, effective onset, quantitative coefficient
remainder rate, correction series, transseries, local complex Delta-domain
expansion, or general finite-state cone theorem is asserted. Prior numerical
estimates by Vaclav Kotesovec (OEIS, 13 January 2026, after Nicholas Beaton)
and Britt and Beaton (version 3) are credited in the report.

## Read

- `report125.pdf`: complete standalone proof, with exact hypotheses and limits
- `report125.tex`: editable source; no downloaded source papers are needed
- `checks/README.md`: exact finite-check ranges, design, and fixture provenance
- `data/verification_results.json`: authoritative exact checker output
- `data/negative_results.json`: deterministic mathematical/schema mutation output

Finite algebra and enumeration are independently replayable. They do not
prove analytic uniform estimates or an asymptotic theorem by themselves.
The latter are established by the mathematical arguments in the report.

## Quick verification

Python 3.10 or newer is required. The authoritative finite checker uses the
standard library, without network access or an installation step. Run:

    python3 -B integrity.py
    python3 -B checks/verify.py --output ../report125-results.json
    python3 -B checks/negative_tests.py --output ../report125-negative.json
    python3 -B test_integrity.py

The guards remain active under optimized Python (`python3 -B -O`). Both the
checks subtree and the complete package have closed inventories: extra files
or directories, missing files, altered bytes, and symlinks are rejected.
Inventories are integrity records, not cryptographic signatures. They cannot
protect against simultaneous malicious replacement of a verifier and its
inventory.

## Complete immutable replay

    python3 -B reproduce.py --output ../report125-replay.json

This verifies the outer inventory, runs exact checks in normal and optimized
Python, compares result bytes, runs independent mathematical/schema mutation
tests and outer inventory mutation tests, and rebuilds the PDF twice in clean
external directories. It then creates a deterministic ZIP, extracts it into
a fresh directory, reruns both check modes, rebuilds the PDF twice, and requires
byte-identical ZIP repacking. The original package is checked again at the
end. All work products remain outside the reader directory. Without TeX:

    python3 -B reproduce.py --skip-pdf --output ../report125-checks-only.json

Checks-only replay retains the exact checks and fresh ZIP replay but records
that PDF reconstruction was omitted. A complete replay can take several minutes.

## PDF build

Requires pdfTeX/pdflatex plus geometry, fontenc, Latin Modern, amsmath, amssymb,
amsthm, mathtools, booktabs, microtype, hyperref, and enumitem.

    bash build.sh
    python3 -B build.py --output ../rebuilt-report125.pdf

The default destination is `../build/report125.pdf`. The builder creates a
fresh TeX format in temporary directories and runs three passes in each of
two clean builds. It rejects overfull boxes and unresolved references and
requires byte equality. It never overwrites the delivered source PDF.
Exact PDF bytes are checked for the versions in `build-environment.txt`;
other TeX distributions may yield equivalent content with different bytes.

## Deterministic packaging

    python3 -B repack.py ../report125_reproducibility.zip

The ZIP has a single `report125/` directory. Member order, timestamps,
permissions, and compression settings are fixed. Compressor versions may
affect bytes, so the zlib version is recorded. No intermediate renders,
logs, downloaded papers, fitted diagnostics, or private development notes
are included.

After an intentional author-side edit, regenerate the outer inventory with
`python3 -B integrity.py --write`. This is not validation of an unexpected
change. Changes inside `checks/` also require its separately reviewed
closed inventory to be updated.
