# Pell growth from divisibility: an explicit quartic for Con(ZFC)

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

## Principal result

This package supplies the complete literal equation

\[
P_{210}(x_0,\ldots,x_{209})=\sum_{j=0}^{149}R_j(x_0,\ldots,x_{209})^2=0,
\qquad \boldsymbol x\in\mathbb Z^{210}.
\]

Every residual is an explicitly listed integer polynomial of degree at most
two. The resulting single polynomial has **exact degree 4**, **5,282 collected
nonzero monomials**, and **coefficient height 2^40 = 1,099,511,627,776**.
The maximum coefficient of a residual is 2^20. All 210 variables are
unrestricted integers; positivity is proved where the decoding needs it.

The ordinary mathematical proof, composed with the identified inherited
numerical-calculus/ZF/ZFC calibration, establishes

\[
\mathrm{ZFC}\vdash
\left(\neg\exists\boldsymbol x\in\mathbb Z^{210}\;P_{210}(\boldsymbol x)=0\right)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

Here consistency means absence of a finite syntactic refutation in the fixed
effective presentation used by that calibration. The assertion is internal
to ZFC and does not restrict proof codes to externally standard numbers.
The construction does not prove consistency, inconsistency, or existence of
a zero. It supplies the stated equivalence.

**Read `report/main.pdf` for the mathematical proof and all 150 literal
residuals.** Its complete editable source is `report/main.tex`, with
`compact_section.tex`, `residuals.tex`, and `metrics.tex` beside it.
The authoritative principal specification is
`equations/principal210/equation.json`. Every collected quartic coefficient
is in `equations/principal210/expanded_polynomial.json`.

## Measured comparisons

The inspected repository snapshot is
`ef0c534c1ae1e312c61a2a9a5a3f18f5516fd42b`. The incoming archive named
`ConZFC_CRT_Index_Anchor_215_2026-10-25.zip` contains 213- and 214-variable
companions as well as its recommended 215-variable equation. The comparison
therefore uses the actual 213-variable endpoint, not just the archive name.

| Equation | Integer variables | Quadratic squares | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Incoming balanced | 215 | 154 | 4 | 5,660 | 91,679 |
| Incoming companion | 214 | 153 | 4 | 5,486 | 1,099,511,627,852 |
| Incoming count minimum | 213 | 152 | 4 | 5,402 | 2,417,851,639,242,452,488,945,685 |
| New balanced companion | 214 | 153 | 4 | 5,699 | 91,679 |
| **New principal** | **210** | **150** | **4** | **5,282** | **1,099,511,627,776** |

The principal improves variable count, row count, collected support and height
relative to both incoming 213 and 214, while keeping degree four. The incoming
215 still has much smaller coefficients. The new balanced 214 applies only
the affine-radix change to that balanced source, retaining its old growth
certificate: it saves one variable and one square at unchanged height, with
39 more collected monomials. This is a tradeoff, not dominance.

The principal does not simulate K215 or instantiate Jones' universal
polynomial. It uses the repository's directly calibrated numerical calculus
C222. No claim of global minimality or historical priority is made.

## The two principal changes

### 1. Replace an exact power by a divisibility-forced Pell ordinate

Keep `t = 16 + 4*z^2`. Instead of requiring `F = t^(2^20*t)`, use three
quadratic equations in three new coordinates:

\[
Z=tF,\qquad X^2-16Z^2-8ZF=1,\qquad F=2^{19}t(2u+1).
\]

They imply the Pell equation with center `a=4*t+1`. For its standard ordinate
sequence `Y_n(a)`, the congruence `Y_n(a)=n mod (a-1)` and the exact valuation
`v2(Y_n(a))=v2(n)` force `n >= 2^19*t`. A depth-19 constructor majorant gives

\[
L=8^{2^{19}-1}t^{2^{19}},\qquad |F|\ge L^t.
\]

This is the growth actually needed for weighted-label product separation.
The five private coordinates of the old exact-power request become three.
The obsolete growth index is removed from the shared square frame, and the
old principal pair's norm, wire, orientation term and cap term are removed.
The certificate records every coefficient change. The existing output
coordinate F remains a frame atom.

F is initially signed. Retained endpoint and exact-power equations recover
its positive sign later, without adding an inequality witness.

Completeness needs more than a lower bound. The proof shows that `s -> Y_s(a)`
permutes residues modulo every power of two when `a=1 mod 4`. Cofinal horizons
`z=0 mod 2^12` permit a positive Pell ordinate with
`F=2^23 mod 2^ell`, for `2^ell>t`. Its binary support is disjoint from t, so
`binom(F+t,t)` is odd. Only prime support, rather than the stronger old
condition `t! | y`, is needed for the beta CRT. This distinction is necessary
because the chosen F has fixed 2-adic valuation 23.

### 2. Obtain the radix from the existing dominant CRT representative

The source already has the even CRT representative C, a cap making it the
largest nominal Pell index, and the divisibility `B*eta=C+F+1`.
Use the affine base

\[
D=2(C+F+1),\qquad q=D^x.
\]

The actual affine expression is substituted into every certificate, including
the square frame. Once signs are recovered, `D>2*C` bounds all binomial digits,
while `B | D` gives `B^x | q`. This removes one multiplication coordinate and
its defining row. The choice order in completeness is C, then D and the true
power outputs, then the shared Pell frame.

The changed source has 216 variables and 156 rows. Five certified integral
common-Hessian projections and one affine projection give 210 variables and
150 rows. Finally, 79 invertible integer coordinate and residual-row
operations reduce the support to 5,282 monomials. A change of residual basis
need not preserve the polynomial itself; it preserves its integer zero set.

## Separate compact companion

`compact11/` contains another complete equation with **11 strictly positive
integer variables**, **exact total degree 174**, and **104 live binary
arithmetic operations**. It is not an eleven-unrestricted-integer claim.
Its entire fixed coefficient tuple is supplied; the largest constant has
592,884 bits.

The new step uses fixed dilation 210 to clear the denominators of a third-order
inverse Lucas polynomial, and retains an independently integral projector
quotient. Its circuit uses only integer constants and addition, subtraction,
and multiplication. All named registers are polynomial abbreviations, not
extra quantified variables. The report calls one input Y; the circuit retains
the historical name `s` for that same input.

The complete proof, literal circuit, deterministic coefficient reconstruction,
all coefficient bytes, retained calibration, and independent finite checker
are included. The final unit product is part of the degree count. The explicit
nonzero coefficient

\[
[J^{49}w^{25}Y^{57}i^{10}\eta^{32}\kappa]P
=192\cdot210^{37}\beta^{49}>0
\]

proves that degree 174 is attained after the fixed constants are substituted.

Source115 has 11 positive variables / degree 211 / 107 operations, but a
different K0, so that comparison is on domain and size. Source172 has the
same entire tuple and 10 positive variables / degree 214 / 87 operations;
it remains better on variable and operation counts. This companion retains
its native/K215/compiler/refutation ancestry and is separate from the direct
C222 construction.

## Verify offline

Python 3.10 or later is recommended. All construction and finite checking use
only the Python standard library, with no network access and no root search.

From the extracted directory:

```bash
python3 -B verify.py
python3 -B -O verify.py
```

The verifier checks the full preserved parent, both new quartic branches,
their exact expansions, the printed residuals, the compact circuit and fixed
coefficient reconstruction, and a fresh build of every new quartic stage.
It rejects 22 targeted corruptions of the principal chain, 17 of the balanced
chain, 13 for each printed residual list, and all 208 single-operator changes
to the compact circuit. It propagates `-O` into subprocesses; substantive
checks do not disappear when Python assertions are disabled.

To retain a receipt outside the frozen package:

```bash
python3 -B verify.py --receipt /tmp/conzfc210-replay.json
```

To reconstruct the new coefficient stages into an empty directory:

```bash
python3 -B code/rebuild.py --output-dir /tmp/conzfc210-rebuilt
```

This rebuilds and byte-compares 37 JSON files across nine stages. Producer
replay and independent finite verification are separate checks. The exact
residual TeX can be regenerated with `python3 -B code/export_equations.py`.
The inherited strict TeX parser verifies every printed coefficient back
against the literal source. To rebuild the report, run `pdflatex main.tex`
twice from `report/` with a normal TeX Live installation.

`evaluate.py` accepts an explicitly supplied integer tuple and evaluates the
quartic. It performs no search. For example, `python3 -B evaluate.py point.json`
expects a JSON list of 210 integers, and rejects floats and booleans.

## Files and proof boundary

| Path | Role |
|---|---|
| `report/` | PDF, editable LaTeX, and complete principal residual appendix |
| `equations/principal210/` | Literal principal rows, collected polynomial, metrics, charts, readable residuals |
| `equations/balanced214/` | Corresponding balanced companion artifacts |
| `stages/` | Seven exact intermediate source/projection stages and certificates |
| `code/` | Producers, independently implemented coefficient checks, reconstruction, exports |
| `compact11/` | Self-contained positive-variable companion and retained proof dependencies |
| `proofs/` | Detailed proof notes and separate mathematical/algebraic reviews |
| `inherited/anchor/` | Unchanged complete incoming parent package |
| `provenance/SOURCES.json` | Pinned repository and archive identifiers |
| `verification/` | Reproducible finite-check receipts and auxiliary modular examples |
| `INTEGRATION.md` | Suggested repository integration and terminology |
| `SHA256SUMS` | File-integrity manifest |

The ordinary proof uses the inherited named logical endpoints
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, together with the
retained square-shell recoding and Pell/binomial-CRT theorems. These are
identified in the report and frozen dependency audit. The selected logical
sources in the parent are not a complete compilable Lean dependency closure.
No new end-to-end Lean/Rocq proof is claimed. The computational checks prove
finite polynomial identities and source bindings; the unbounded Pell, CRT,
Horn-flow and logical arguments are the ordinary mathematical proofs.

The eight modular Pell examples are tests of an auxiliary residue construction.
They are not zeros of the full consistency polynomial.

Principal equation JSON SHA-256:

```text
20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a
```

Balanced equation JSON SHA-256:

```text
f351ebddacc0515984a00617a8bd7c318a24beaa48b5ad4bfff5aa99f6c383b6
```
