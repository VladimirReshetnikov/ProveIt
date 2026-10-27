# Rectangular contraction, streamed conditioning, and precision barriers

Prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific time).

Start with **report.pdf**. Its complete source is **report.tex** and the files
in **sections/**. The report is compiled from this source.

## Completed results

The closing review covers **20 refinement packets and two primary
manuscripts** at ProveIt commit
dde01c4a63b822c25b8eb345299346c36f837b49. It incorporates the newest
sat_adaptive_contraction packet and verifies the earlier four incoming
packets against their placed copies.

Write E(s) = s / sqrt(ceil(log2(s))) for the common normalized Boolean
wire budget. Polynomial factors and uniform lower-order exponent terms
are omitted in this table.

| Method | New time coefficient on E(s) | Space | Comparison |
|---|---:|---|---|
| Multistage streamed conditioning | 53.9775311981 | Polynomial | Previous explicit 55.7094783189; stronger compatible composition 55.4046659066 |
| Rectangular cached contraction | 33.9938908592 | Coefficient 33.9937208906 on E(s) | Previous explicit generic cached time 35.3545880584 |

**54 is an eventual polynomial-space time coefficient. 34 is an eventual
cached time and space coefficient.** The cached space use is subexponential.

These are smaller exponential upper-bound certificates. They retain the
s/sqrt(log s) contraction scale. No smaller unrestricted SAT logarithmic
order, completed n/log n interface, practical SAT speedup, or complete
fast SAT solver is claimed.

The exact cached constants are

    C_space = (pi/ln(2)) * sqrt(2812500/49997)
    C_time  = (1 + 1/200000) * C_space.

The polynomial-space constant is the explicit convergent sum in
report equation (4.2), also computed exactly by code/check_streamed.py.
Use the equation label eq:streamed-new-coefficient in the source if
numbering changes during integration.

The report also proves:

- Arbitrary asymmetric Hermite node multiplicities cannot improve the
  leading independent-jet precision certificate. The exact finite real
  optimum is given by a backward rational recurrence; integer rounding
  costs less than two normalized units; the leading six remains optimal.
- An inventory barrier incorporating adaptive integral Smith separation,
  with a large exact-weight-list consequence for explicit table methods.
- Carefully scoped fixed-tree, adaptive-tree, and streamed-profile
  limitations in the existing entropy/packing certificate model.

The barriers concern specified models, not SAT complexity lower bounds.

## Reproduce

Python 3.10 or newer, standard library only:

    python3 verify_manifest.py
    python3 run_checks.py

The second command runs all four mathematical checkers in normal and
optimized Python, compares their deterministic JSON output, and rewrites
the results. Verify the delivered manifest before replaying.

To rebuild the PDF, install pdfLaTeX and the packages in the preamble:

    python3 build_report.py

The build disables shell escape, makes three passes, and rejects overfull
boxes and unresolved references. It does not download sources or run any
upstream repository scripts. The _build directory is disposable.

## Files

- report.tex, sections/, report.pdf: complete article and compiled PDF.
- code/: exact schedule, Hermite, Cauchy-minor, and inventory checks.
- results/: reproducible certificate JSON and build evidence.
- audit/: independent mathematical review, source classification, and
  investigation notes, including the closing twentieth-packet addendum.
- provenance/: initial and closing commit records, source Git blobs and
  SHA-256 identities, and the 180-file placement identity check.
- PROOF_STATUS.json: new results, inherited assumptions, and unresolved goals.
- INTEGRATION.md: proposed repository placement and summary rows.
- MANIFEST.sha256.json and verify_manifest.py: archive integrity checks.

The main comparison is on identical generic input premises: at most s
Boolean wires, initial precision and truncation length at most s,
maximum degree at most ceil(s^(9/10)), and the stated entry-oracle
interface. Wire coefficients cannot be substituted directly for
coefficients per SAT variable. Existing lower-degree and lower-memory
branches remain part of the portfolio under their own premises.

## Verification scope

All new arithmetic certificates passed normal and optimized Python.
The Hermite checker covers 2,318 exhaustive multiplicity profiles and
112 finite minimax cases. The inventory checker covers 4,699 minor
valuations, 94 direct rational determinants, 768 parameter cases, and
324 explicit binary tuples. Independent reviewers checked the main
new proof steps.

The source deformation, SAT reductions, packing, Cauchy modes, newest
separator identity, and external field-multiplication bounds remain
explicit imported results. No Lean/Rocq build or independent end-to-end
verification of the underlying ETH manuscript was performed.
