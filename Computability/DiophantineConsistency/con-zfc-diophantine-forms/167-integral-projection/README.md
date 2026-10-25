# Two smaller direct quartics for ZFC consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

Start with **report/ConZFC_Integral_Projection.pdf**. The editable article is
**report/report.tex**, with both generated mathematical appendices alongside it.

## Results

Each displayed equation is an ordinary integer polynomial with fixed literal
coefficients. Every unknown ranges independently over all integers.

| Construction | Variables | Quadratic residuals | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Pinned pooled-power parent | 225 | 162 | 4 | 7,867 | 128,446 |
| **Balanced equation** | **220** | **157** | **4** | **7,793** | **45,161** |
| **Fewer-variable equation** | **218** | **155** | **4** | **14,410** | **5,023,040** |

The balanced equation improves its exact parent in variables, rows, collected
support, and coefficient height. The 218-variable equation removes two more
variables, with an explicit support/height tradeoff. No global minimum is claimed.

The equations are

```text
P220(x0,...,x219) = sum(Si(x)^2, i=0,...,156) = 0,
P218(x0,...,x217) = sum(Ri(x)^2, i=0,...,154) = 0.
```

Every residual is printed in the PDF and supplied in JSON. Their names introduce
no extra quantified variables. Complete collected quartics are supplied too.

The ordinary proof, composed with the explicitly identified inherited calibration,
establishes in ZFC, for each equation:

```text
There is no integer solution  <=>  Con(ZFC).
```

The new algebraic result is an unconditional integral zero-set bijection from the
exact authenticated 225-variable parent. The parent's unbounded arithmetic and
C222/ZF/ZFC calibration are imported mathematical dependencies. Neither construction
assumes consistency, proves consistency, or supplies a new end-to-end Lean/Rocq build.

## What this iteration contributes

Five common-Hessian directions in the pooled-power source allow exact integer
projections. Two affine relations exposed by those projections allow further
contraction. Integral centering and reversible row operations give the two final
forms. The general projection method is credited to report 159; the new contribution
is the application and resulting explicit composition, not a claim to have invented
that general elimination method.

For the 218-variable residual list, a complete degree-three Macaulay matrix has
33,945 rows, 137,911 occurring columns, and full row rank modulo the checked prime
1,000,003. Thus no nonzero affine-multiplier combination of these residuals is affine
over Q. This rules out one precisely bounded class of further eliminations; it is
not an arity lower bound.

## Files

- `variants/220/equation/`: recommended balanced equation, full expansion, metrics.
- `equation/`: 218-variable alternative, full expansion, metrics.
- `certificate.json` and `variants/220/certificate.json`: every integer coordinate
  map, row operation, restoration expression, and continuous stage hash chain.
- `build.py`, `verify.py`, and corresponding files under `variants/220/`:
  construction and separately implemented exact verification.
- `verify_rank.py`: rigorous modular Hessian/Macaulay rank computation.
- `verification/`: fresh receipts, including the independently rebuilt parent.
- `report/`: 21-page article, both complete equation appendices, and native TeX.
- `export_equations.py`: exporter with an independent parser checking every printed
  mathematical coefficient against the literal data.
- `evaluate.py`: exact arithmetic evaluation at a supplied integer tuple.
- `proofs/`: independent AI-assisted reviews and inherited-proof audit.
- `inherited/ConZFC_Pooled_Powers_2026-10-25.zip`: unmodified authenticated parent,
  preserving its complete runnable construction and proof-source closure.
- `inherited/calibration_review/`: selected actual logical-calibration sources and
  the internalization audit; this is not the entire transitive Lean project.
- `provenance/`, `NOTICE.md`, `LICENSE`, `INTEGRATION.md`, and `SHA256SUMS`.

## Reproduce

Python 3.10 or newer, standard library only:

```sh
python3 -B build.py
python3 -B verify.py
python3 -B variants/220/build.py
python3 -B variants/220/verify.py
python3 -B verify_rank.py
python3 -B export_equations.py
```

The construction programs regenerate the literal data. The independent verifiers
do not import the builders. Their checks remain active under `python3 -O`.
The primary verifier checks 2,426 symbolic identities; the sibling checks 1,948.
Both reject four deliberate certificate/coefficient corruptions.

The original 225-variable archive was freshly rebuilt in both normal and optimized
Python: all 20 generated stage JSON files reproduced byte for byte. Its immediate
245-variable parent also passed a fresh rebuild. These finite checks do not replace
the unbounded mathematical proof or the identified logical calibration.

To evaluate a specified tuple:

```sh
python3 -B evaluate.py --variant 220 --values tuple.json
python3 -B evaluate.py --variant 218 --values tuple.json --residuals
```

To rebuild the PDF after exporting its appendices, run twice from `report/`:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
  -jobname=ConZFC_Integral_Projection report.tex
```

This uses standard TeX Live packages. Recompilation may change PDF metadata;
equation identities are controlled independently.

## Comparison scope

The exact parent is report 158 at repository commit
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`, equation SHA-256
`fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56`.
Later report arrivals 160-165 were also checked for comparison, as recorded in the
late-arrival note. Their smaller natural-domain counts are not unrestricted-integer
counts. Lower-height and smaller-variable constructions with other architectures
remain available. No repository files were changed by this submission.

Independent reviews in this release are separate tasks in an AI-assisted research
workflow, not external human peer review. Further research questions are in Section 7
of the report.
