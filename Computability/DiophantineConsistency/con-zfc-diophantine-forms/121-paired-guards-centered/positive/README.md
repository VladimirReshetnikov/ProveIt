# Auxiliary-powered coprime Pell fusion

Six explicit polynomials in ten strictly positive integer variables:

| Chart | Center | Live binary operations | Exact degree |
|---|---|---:|---:|
| X=qw | none | 89 | 288 |
| X=qw | (A+1)DE | 91 | 283 |
| X=qw | ADE | 92 | 278 |
| X=q+x | none | 94 | 262 |
| X=q+x | (A+1)DE | 96 | 258 |
| X=q+x | ADE | 97 | 254 |

All six rows are Pareto tradeoffs under these two metrics. Fixed coefficient ports are not extra variables. Every multiplication by a fixed numeral counts. The exact polynomial is the final register N of the relevant JSON file.

The new combination removes the transport majorant using the already encoded auxiliary Pell solution. Its index is at least five before transport, giving b>8Q. This works even with the fused first/strong radical. The direct graph also reuses q^3*q(q-1), removing a redundant q^4 gate. Fusion, upper/sharp centering and the auxiliary index estimate are separately credited to the retained prior and incoming packets; this packet does not relabel those ingredients as new discoveries.

Both directions of the unbounded arithmetic proof, explicit positive canonical witnesses, exact top homogeneous forms and an honest calibration boundary are in PROOF.md and standalone.pdf. section.tex is ready to include in a larger report. The source61/native/compiler calibration is retained in source/. No new machine-checked Lean endpoint, consistency proof, global optimality claim or nine-variable construction is asserted.

## Replay

Only Python 3's standard library is required for all algebraic and circuit checks:

    python -B build.py --check
    python -B check.py
    python -B check_ordinary.py
    python -B -O build.py --check
    python -B -O check.py
    python -B -O check_ordinary.py

The receipts include whole graph audits, live-gate counts, coefficient payload hashes, universal free-polynomial identities, exact integer univariate expansions, actual-coefficient modular leading forms, independent literal formula controls and finite Pell-period checks. These are transcription checks, not replacements for the unbounded proof.

A standard TeX installation can rebuild standalone.pdf with two pdflatex runs; render.sh does this. The supplied PDF is four pages. It was rendered and visually inspected, with no clipping, missing glyphs or overfull boxes detected.

## Provenance and coherent coefficients

The coefficient directory is copied unchanged from the prior fused96/266 package and contains the complete original compact44 tuple. It is NOT the different BFS tuple used by some incoming artifacts. build.py preserves this original binding in every ordinary and direct JSON. The uniform semantic proof permits the complete original tuple; individual ports are never exchanged.

SOURCE_PINS.json records the exact source archive Git blobs and local source hashes. The upstream head reviewed is45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6. No remote repository was changed.
