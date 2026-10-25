# Shift-free descending certificates: direct quartics over naturals

Three selected, explicit single quartic equations are supplied. Every coordinate
ranges independently over **N={0,1,2,...}**. All residuals and full collected
coefficients are literal JSON; the complete residual lists also appear in TeX
and plain text. The ordered coordinate names are in variables.tsv.

| Endpoint | Variables | Quadratic rows | Quartic terms | Coefficient height |
|---|---:|---:|---:|---:|
| balanced229 | 229 | 179 | 5,607 | 65,892,965 |
| low_height228 | 228 | 178 | 9,522 | 560,804,902 |
| sparse228 | 228 | 178 | 7,512 | 2,445,412,949,744 |
| projected229 (pre-row-basis control) | 229 | 179 | 6,596 | 83,879,378 |

The equation is P=sum_j R_j²=0. A term [c,[i,j,...]] means c*x_i*x_j*...;
[] denotes a constant. No factorial, floor, binomial, variable power or Pell
primitive remains in these polynomials. Every coordinate occurs.

The new mathematical step removes the artificial shifts on F and B in the
incoming descending factorial certificate. A natural n satisfies n+1=F²;
the existing exact-power modulus excludes n=0 before interpreting powers.
The floor and remainder rows then force B>F>=2, enough for the carry-free
bootstrap. Combining this with the Round17 strict x-budget and cofinal anchor
reduces the direct graph. Natural-certified contractions and 42 reversible
row shears give the selected final endpoints.

With the explicitly retained ordinary C222/ZF/ZFC refutation calibration,
each polynomial has a natural zero iff there is a finite syntactic ZFC
refutation. Thus ZFC proves its no-zero sentence equivalent to Con(ZFC).
This is not a proof of consistency, global optimality, or a newly kernel-
checked end-to-end logical endpoint.

## Reproduce offline

Python 3.10+ and its standard library suffice. From any directory:

    python3 -B /path/to/natural/verify.py --rebuild
    python3 -B -O /path/to/natural/verify.py --rebuild

The verifier is read-only except for an explicitly requested --output receipt;
reconstruction uses temporary directories. It checks every gate, affine
restoration, exported row, semantic interface, natural contraction, collected
coefficient, row-basis forward/inverse map, and literal rendered TeX row.
Deliberate corruptions are rejected. All 17 selected source/endpoint files
rebuild byte-identically. Successful finite checking does not replace the
unbounded ordinary number-theoretic proofs.

## Files and proof boundary

- report_section.tex: the complete new ordinary argument, ready to include in
  the enclosing report; PROOF.md gives the corresponding prose proof.
- source/: shared raw semantic graph and exact quadratic source.
- portable/: the retained self-contained compiler closure and exact C222
  numerical source JSON. SOURCE_MAP.json records imported paths/hashes and
  identifies the two modified compiler modules.
- proofs/: retained ordinary dependencies; inherited/calibration/ contains
  the named C222/ZF/ZFC Lean inputs and their pins. Historical proofs describe
  their own predecessors, not the new endpoint metrics.
- balanced229/: final row-reduced 229-variable endpoint.
- projected229/: immediate 229-variable natural contraction and certificate.
- low_height228/, sparse228/: fixed-priority natural contractions, certificates,
  and literal priority permutations bound to the exact shared source.
- row_operations.json, row_basis_certificate.json: the final zero-set-preserving
  change of residual basis, never a natural-coordinate projection.
- verify.py and independent check_*.py: finite algebra and semantic-interface
  verification without importing the producer.

The inherited calibration files are retained inputs, not a claim that their
entire transitive Lean development was rebuilt here. All new unbounded steps
are ordinary mathematics. No script searches for a contradiction or solves
one of these equations.
