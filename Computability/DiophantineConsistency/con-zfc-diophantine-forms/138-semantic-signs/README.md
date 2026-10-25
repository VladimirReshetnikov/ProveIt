# Semantic sign recovery and cofinal bounds

Explicit Diophantine forms of Con(ZFC), prepared with AI assistance for
Vladimir Reshetnikov and ProveIt, 24 October 2026.

**Main result:** a literal quartic in **286 unrestricted integer variables**,
with **196 quadratic residuals**, **6,607 collected monomials**, and
**coefficient height 128,446**. ZFC proves that this polynomial has no integer
zero if and only if Con(ZFC). The complete ordinary argument composes the
new arithmetic lemmas with the retained, explicitly identified calibration
of the numerical proof calculus C222. It uses no K215 simulation, Jones
universal polynomial, or Sun reduction.

Start with [the 27-page report](report/report.pdf). Its LaTeX source is
[report/report.tex](report/report.tex); Appendix A prints every residual of
the principal polynomial, and Appendix B gives the complete fixed-constant
recipe for the ten-positive-variable companions.

## Exact equations and tradeoffs

For each direct endpoint the polynomial is the sum of the squares of the
listed residuals. No extra unknown is introduced by the sum-of-squares
notation. The domains in this table are part of the theorem.

| Component | Domain | Variables | Degree | Residuals | Monomials | Height |
|---|---|---:|---:|---:|---:|---:|
| `integer286/principal/centered` | All integers | 286 | 4 | 196 | 6,607 | 128,446 |
| `integer286/generated/centered` | All integers | 319 | 4 | 207 | 5,779 | 128,446 |
| `natural235/equations/natural235` | Nonnegative integers | 235 | 4 | 184 | 22,185 | 90,911,633 |
| `natural235/equations/natural236_sparse` | Nonnegative integers | 236 | 4 | 185 | 15,645 | 88,233,865 |

Each directory contains `equation.json` and `expanded_polynomial.json`.
In their sparse terms, `[c, [i, j, ...]]` means coefficient `c` times the
product of the indicated coordinates; an empty index list means a constant.
Ordered variable lists, raw systems, exact restoration certificates, and
source bindings are included.

The matched package-131 integer parent has 324 variables, 208 residuals,
5,808 monomials, and height 128,446. The principal result saves 38 variables
(11.73%) and twelve rows, at the cost of 799 additional monomials. The
319-variable companion improves dimension, rows, and support together.
The matched package-133 natural parent has 237 variables, 185 residuals,
69,710 monomials, and height 133,499,131; the 235-variable result improves
every varying metric in that comparison.

Five compact polynomial circuits are also supplied:

| Equation JSON | Domain | Variables | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `positive10/equation_83_436.json` | Strictly positive integers | 10 | 436 | 83 |
| `positive10/equation_81_560.json` | Strictly positive integers | 10 | 560 | 81 |
| `positive10/equation_80_750.json` | Strictly positive integers | 10 | 750 | 80 |
| `integer11/parity_saturated11_native.json` | All integers | 11 | 924 | 107 |
| `integer11/parity_saturated11_short.json` | All integers | 11 | 840 | 108 |

Every live binary addition, subtraction, and multiplication counts,
including squares and multiplication by fixed numerals. These are operation
counts for the supplied circuits, not lower bounds on arithmetic complexity.
The fixed coefficients are specified by full finite recipes and exact
compressed payloads. The largest positive-branch numeral has 592,884 bits;
the signed branch uses a different six-number tuple. Both compact branches
retain their inherited native/K215 calibration. Do not mix these tuples.

The 83-operation form improves the 84-operation parent at unchanged degree
436. The 80- and 81-operation points trade higher degree for lower cost.
The 107- and 108-operation forms save two operations from their respective
109- and 110-operation parents, without changing their degrees. The
repository already has equations with different, smaller variable counts
and much larger coefficient encodings. No global minimum or literature-wide
priority claim is made.

## New mathematics

1. **Recover signs from existing power certificates.** Orienting the Pell
   abscissas makes negative exponent indices impossible when the encoded
   output is integral and the base is at least two. A size estimate upgrades
   the relevant modular identity to an integer identity. Nine CRT signs and
   a front-variable sign can then be recovered, with an explicit acyclic
   proof that also handles zero representatives and a provisional zero
   exponent. This deletes many independent nonnegativity witnesses.
2. **Use a compatible even frame and odd anchor.** Pell doubling supplies
   the abscissa as `2*a^2-1`; a two-adic calculation permits the anchor
   quotient `2*(2*e+1)` with unrestricted `e`. These changes save five
   variables before the larger sign reduction.
3. **Sharpen the cofinal modulus.** With `F=t!` and `V=(F^2+1)^t`, a padded
   finite proof's accumulators already lie below `V-1`. Thus the beta modulus
   can be `y=V-1` instead of `V*(V-1)`. This removes a multiplication and
   combines with the one-row natural cap.
4. **Remove an unnecessary compact-coordinate shift.** An absolute-value
   transport proof permits a free positive auxiliary coordinate. A q-cube
   quotient coordinate and absorbed padding remove three more gates in
   the normalized forms. A stronger norm estimate permits the intermediate
   81-operation, degree-560 point.
5. **Combine parity and saturation.** In the eleven-integer branch, a
   congruence modulo sixteen replaces a scaled nonsquare guard by the
   budget minus four. An exact finalizer identity saves a second operation.

The report proves these statements and both directions of the resulting
equivalences. Component proof files give additional source-facing details.

## Reproduce offline

Python 3.10 or newer and its standard library suffice:

```sh
python3 -B verify_all.py --rebuild
```

This authenticates the release manifest and endpoint catalog, checks the
literal manuscript appendix, and runs all four components in both normal
and optimized Python. It copies components to temporary directories so
that checkers which produce receipts cannot modify the sealed release.
The `--rebuild` option adds deterministic producer replays; for the signed
circuits it compares both equations and metrics byte for byte. The script
uses no network and needs no original checkout. Add `--receipt /path/out.json`
to retain a new receipt. `VERIFICATION_ALL.json` is the delivered run.

To rebuild the PDF separately, with a standard pdfLaTeX installation:

```sh
bash build_report.sh /path/to/rebuilt-report.pdf
```

The script compiles in a temporary directory, rejects unresolved references
or overfull boxes, and leaves the frozen sources intact. The mathematical
verification does not require TeX.

Individual components have their own README and check commands. The direct
components also include exact evaluators; they evaluate candidate tuples,
not consistency or unsolvability.

## Proof and verification boundary

The claim is an ordinary mathematical proof formalizable in ZFC, using the
named inherited calculus/CRT/Pell calibration. This packet does not supply
a newly compiled end-to-end Lean or Rocq development or a sealed syntactic
ZFC derivation. The included Lean declarations are source evidence for the
identified existing interfaces, not a complete build closure.

Finite checks certify literal transformations, coordinate restoration,
complete quartic expansions, coefficient reconstruction, operation counts,
degree certificates, and rejection of deliberately corrupted artifacts.
They do not prove consistency or replace the unbounded arithmetic proofs.
Independent review here means separate agents checking the arguments in
this AI-assisted workflow, not outside human refereeing.

## Provenance and integration

All current comparisons use ProveIt commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`, including packages 127–133.
`SOURCES.json` gives the component ledgers and comparison paths;
`ENDPOINTS.json` gives exact endpoint paths, metrics, domains, and hashes.
Older commits inside retained parent manifests describe those inherited
files and do not replace this comparison snapshot.

`INTEGRATION.md` describes suggested placement. The original repository
was not modified. New material follows the MIT No Attribution terms in
`LICENSE`; inherited material retains its own licenses and notices.
