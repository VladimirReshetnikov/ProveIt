# Reciprocal pooling and integral projections for Con(ZFC)

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.
AI-assisted research, with separately assigned mathematical and finite-algebra reviews.

Start with **report/report.pdf**. The complete editable LaTeX source is
**report/report.tex**, with its generated inputs in the same directory.

## Completed equations

All coordinates range independently over **unrestricted integers**.

| Equation | Variables | Residuals | Exact degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Retained direct parent | 225 | 162 | 4 | 7,867 | 128,446 |
| **Principal quartic** | **218** | **155** | **4** | **34,984** | **113,304** |
| **Reciprocal companion** | **215** | **152** | **10** | **99,914** | **113,304** |

The maximum absolute coefficient of an individual residual is 240 for both
new equations. Every declared coordinate occurs in the collected polynomial.

For each equation, the ordinary proof composed with the retained direct
C222/ZF/ZFC refutation calibration establishes in ZFC:

> The polynomial has no integer zero if and only if Con(ZFC).

This is syntactic consistency for the effective ZFC presentation named in the
retained calibration. It asserts an equivalence, without deciding consistency
or solvability. The source encodes the numerical proof calculus directly;
neither K215, Jones's universal polynomial, nor Sun's reduction is used.

The quartic removes seven variables and seven residuals at unchanged degree,
and lowers coefficient height by about 11.8%, compared with its actual parent.
Its expanded support is larger. The companion removes three further variables
at the cost of degree ten and larger support. These are measured tradeoffs
within the direct small-coefficient branch, not global minimality claims.

## The new arithmetic idea

For two blocks of canonical signed Pell power requests at nonzero consecutive
bases `n0=q` and `n1=q+1`, put

    Tj = 2*A*nj - nj^2 - 1,
    Hj = sum_i Yi*(mi-Xi),
    Sj = sum_i ((mi-Xi+A*Yi)^2-Yi^2),
    Ej = Sj-2*nj*Hj.

Replace the four old private pool coordinates and their four quadratic rows
by one integer `z` and the quintic residual

    E0*T1 + E1*T0 - z*T0*T1.

Under the unchanged parent frame, this is equivalent to all fourteen exact
power requests. Its proof makes a rational sum of squared errors an integer,
clears every signed index, and bounds the resulting integer sum in absolute
value by a number strictly below one. The two denominators have the same sign,
so errors cannot cancel. No coprimality between the denominators is required.

The full theorem, signed and unit-base cases, constructive inverse witnesses,
and the noncircular bootstrap are proved in the article and `proofs/`.

## Complete finite definitions

- `equations/quartic218/equation.json`: all 155 literal quadratic residuals.
- `equations/decic215/equation.json`: 151 retained quadratic residuals and the
  literal replacement quintic.
- Each `expanded_polynomial.json`: every collected coefficient of the single
  sum-of-squares polynomial.
- `report/residuals218.tex`: every principal residual, printed in the PDF.
  The PDF also gives the complete companion as an explicit formula in those
  residuals with four coordinates set to zero.

A term `[c,[i,j,...]]` means `c*x_i*x_j*...`, with zero-based indices. An empty
index list means a constant. All sums are finite. No variable exponent,
factorial, binomial operation, or unspecified coefficient remains in the final
equations.

## Verify offline

Python 3.10 or later and its standard library suffice:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild
```

The default verifier is read-only. To save a fresh receipt separately:

```sh
python3 -B verify.py --receipt /tmp/conzfc-fresh-verification.json
```

The independent checker imports no producer or optimizer. It verifies every
projection map and inverse, all protected integer row operations, the literal
pool replacement, every expanded coefficient, and 25 deliberate corruptions.
It also checks the parent frame and all actual power atoms, the separate
arithmetic fixtures, and the displayed LaTeX residuals. The `--rebuild` run
reconstructs 20 inherited parent JSON files, four lattice-chart files, and four
final reciprocal files byte-for-byte in temporary directories.

Actual successful receipts are `verification/FINAL_NORMAL.json`,
`FINAL_OPTIMIZED.json`, and `FINAL_REBUILD.json`. The arithmetic fixtures
supplement the unbounded proof; they do not prove it by testing examples.

## Evaluate one tuple

```sh
python3 -B code/evaluate.py quartic218 point.json
python3 -B code/evaluate.py decic215 point.json
python3 -B code/evaluate.py decic215 point.json --residuals
```

The input must be a JSON list of exactly 218 or 215 integers. The evaluator
computes the polynomial at that tuple. It is not a consistency decision
procedure or a root search.

## Rebuild the article

The delivered generated inputs are sufficient to compile:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

To regenerate and independently check the mathematical appendix from the
coefficient data, run from the package root:

```sh
python3 -B code/export_report.py
python3 -B code/check_report.py
```

The report uses standard TeX Live packages listed in its preamble. PDF bytes
can differ across TeX installations because of fonts and build metadata.
The mathematical JSON data, frozen certificates, and parsed TeX formulas are
the stable definitions.

## Provenance and proof boundary

The comparison snapshot is ProveIt commit
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`.

The immediate source is `158-pooled-powers`; projection methods and utilities
come from `159-quadratic-projection-234`. The original parent source and its
ordinary proof closure are retained under `inherited/parent225/`. Original
licenses and notices remain. The omitted deduplicated parent dependencies were
restored from the original pinned archives and checked against their recorded
hashes. `provenance/SOURCES.json` and `proofs/PARENT_PROVENANCE.md` identify them.

The logical bridges are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, with the inherited
signed-Pell interface. The new work is an ordinary mathematical proof
formalizable in ZFC plus exact finite verification. It is not a newly compiled
end-to-end Lean/Rocq proof or an emitted object-language ZFC derivation.
The separately assigned AI reviews are not external human peer review.

The artifact is ready for additive intake into ProveIt. See `INTEGRATION.md`.
The new equations and coefficients are self-contained; no upstream write was
needed to prepare the submission.
