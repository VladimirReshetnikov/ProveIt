# Affine horizons and centered certificates for Diophantine consistency

Research prepared for Vladimir Reshetnikov, 26 October 2026 (UTC).

This release supplies explicit equations, complete fixed coefficients, ordinary
proofs, constructive witness maps and reproducible finite checks. In each stated
domain, the proof establishes in ZFC that absence of solutions is equivalent to
syntactic Con(ZFC), at the explicitly retained logical calibration. Neither
consistency nor existence of a solution is asserted.

## Results

- Integer quartics: 215 variables and 152 rows, with 14,578 terms and height
  16,866, or 34,700 terms and height 4,512. The sparse equation improves the
  matched incoming 216-variable quartic in variables, rows, support and height.
- Natural quartics: 202 variables and 154 rows, with 9,353 terms and height
  1,854,167, or 16,927 terms and height 416,488. Sparse 203- and 204-variable
  companions are also supplied.
- A separate natural equation has 200 variables and degree eight. It is not
  a 200-variable quartic.
- Ten positive integers: 89 operations at degree 210, or 90 at degree 206.
  These trade extra operations for lower degree against late source 172 at 87/214.
  Earlier scaled-chart87/228 and88/224 controls are retained, not headline
  operation/degree frontier claims.
- Fourteen unrestricted integers: degree 85 at 110 operations, or degree 87
  at 108 operations, improving the matched 86/112 and 88/110 constructions.
- Full Start-marker4177 specializations use the credited incoming coherent
  four-port tuple: 98,219 raw bytes, largest port 196,790 bits. Its physical
  zero-weight marker, native proof and Pcs certificate are separately checked.

Operation counts use live binary addition, subtraction and multiplication with
integer leaves; squares and fixed scalar products are charged, reuse is free.
Each variable count includes every independent quantified coordinate. No global
minimum, bit-complexity claim or new encoding priority is asserted.

## Read first

- report/main.pdf and report/main.tex: integrated article and editable sources.
- integer/PROOF.md: the affine horizon, strengthened frame and exact consumer maps.
- natural/PROOF.md: natural gate-chart bijection and octic restoration.
- positive/late172/PROOF.md: final free-quotient centering, soundness and positive maps.
- positive/PROOF.md: the retained scaled-chart method controls.
- positive/start_marker4177/: entire separately calibrated current-source tuple.
- roots/PROOF.md: signed even trace, unweighted roots and fresh-witness restoration.
- reviews/: independent AI-assisted mathematical and finite-check evidence.

The main comparison snapshot is ProveIt commit
5274bc751a1566879ddc028a2d2a2af3c031654a. Matched comparisons and incoming versus
placed status are recorded in reviews/BASELINE.md. Component methods already
present in sources are credited explicitly. All historical source trees remain
unchanged. No repository publication or remote write was performed. A bounded late comparison
stops at 09764940c289c493aa573530eda86dd75f319787; its 213/214-variable
quartics have far larger heights, so 215 is not the smallest inspected dimension.
Its maintained 4027 tuple uses 94,689 raw bytes. Our 4177 specialization remains
explicitly frozen and separately calibrated.

## Replay the complete release

Use Python 3.10 or later, with only its standard library:

    python3 -B verify.py

The top-level replay authenticates the complete inventory, creates independent
temporary copies and runs the listed stages in normal and optimized Python.
Optimized mode is propagated to child checkers. It includes actual retained
parent rebuilds, exact expansions, gate/certificate checks, readable-residual
round trips, fixed coefficient reconstruction and deliberate corruption checks.
All sealed bytes must remain unchanged. The extracted final ZIP is also replayed
before delivery. FINAL_REPLAY.json records the performed release replay.

    python3 -B verify.py --mode normal
    python3 -B verify.py --mode optimized

No Diophantine zero search or consistency decision is run. The inherited formal
calibration is not recompiled. The optional independent roots review oracle
under roots/review/ uses SymPy; it is not called by this standard-library replay.
Its separate receipts are corroboration, not an undeclared runtime requirement.

The original upstream current-page gzip rebuild has a documented compression
header portability mismatch (OS byte 03 versus ff). It is not falsely recorded
as a successful compressed-byte rebuild. Original blobs are authenticated, all
raw mathematical integers reconstruct exactly, and the new emitted graphs
rebuild exactly. See the baseline and positive provenance for the precise scope.

## Literal files and article

Every selected direct equation has equation.json, expanded_polynomial.json and
readable residuals. The compact equations give every live binary gate and the
complete numeral payloads with their finite definitions. No proof-only variable
exponent, factorial, binomial, Pell predicate or unspecified coefficient remains
inside a final polynomial.

To compile the article with a normal TeX Live installation:

    sh build_report.sh

PDF metadata and bytes can change on recompilation. The delivered PDF was
rendered and every page reviewed. Mathematical JSON and coefficient data are
controlled independently of later PDF builds.

Reviews are separate checks within an AI-assisted workflow, not outside human
endorsements. Ordinary unbounded proofs and finite replay have different roles.
No new end-to-end kernel certificate, encoded object-ZFC derivation, global
simplicity minimum or consistency assertion is claimed.
