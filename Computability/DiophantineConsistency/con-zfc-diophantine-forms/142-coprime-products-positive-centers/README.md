# Coprime product certificates and positive Pell centers

Research prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026,
with AI assistance. Comparison snapshot:
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`.

The archive constructs fixed ordinary integer polynomials for which ZFC
proves that the absence of solutions, in the stated domain, is equivalent
to `Con(ZFC)`. The ordinary proofs compose the new arithmetic reductions
with explicitly identified inherited ProveIt calibration theorems.

Start with **`report/report.pdf`**. Its editable source is `report/report.tex`.
The report contains full proofs of the new mechanisms, the entire finite
recipe for the compact constants, and all 172 residuals of the principal
quartic. Component proof files give further implementation-level details.

## Preferred endpoints

| Component / equation | Domain | Variables | Binary operations | Exact degree |
|---|---|---:|---:|---:|
| `products/equation_14_raw.json` | positive integers | 14 | 70 | 189 |
| `products/equation_14_reduced.json` | positive integers | 14 | 71 | 157 |
| `products/equation_13_anchored.json` | positive integers | 13 | 72 | 433 |
| `compact_xy/equation_76_626.json` | positive integers | 10 | 76 | 626 |
| `compact_xy/equation_77_464.json` | positive integers | 10 | 77 | 464 |
| `compact_xy/equation_80_382_partial.json` | positive integers | 10 | 80 | 382 |
| `natural/equations/natural221/equation.json` | nonnegative integers | 221 | — | 4 |
| `natural/equations/natural222/equation.json` | nonnegative integers | 222 | — | 4 |

The name `equation_14_raw.json` denotes the preferred staged recovery graph,
not the superseded degree-233 intermediate. For the compact equations, each
listed gate is a polynomial abbreviation: only the listed witnesses are
unknowns. The four authentic constants are fixed, fully supplied integer
leaves. Binary addition, subtraction and multiplication each cost one;
squares and fixed scalar multiplications are counted. These are evaluator
costs, not lower bounds on intrinsic arithmetic complexity.

The quartics are the sums of squares of the complete residual lists.
Their fully collected coefficients are in `expanded_polynomial.json`.

| Direct quartic | Residuals | Collected monomials | Coefficient height |
|---|---:|---:|---:|
| 221 variables | 172 | 9,536 | 83,954,186 |
| 222 variables | 173 | 6,821 | 83,954,028 |

Strict positivity is essential to the compact proofs. Do not reinterpret
their witness lists as unrestricted integers, or allow zero, without a
separate domain encoding. The natural quartics use `{0,1,2,...}`.

## Main ideas

1. **Recover the square before the unit sign.** A coprime product equation
   forces the first radicand to be a square; only then is the remaining
   strong factor a Pell norm whose negative unit can be excluded. This
   replaces two square witnesses by one, saving one positive coordinate
   for four extra operations over P66.
2. **Use two existing quantities to force coprimality.** The main Pell base
   and abscissa are inserted into a freely chosen strong multiplier. Their
   residue identities recover two square roots from one product witness,
   yielding the thirteen-variable equation.
3. **Reuse the product `XY` as a congruence carrier.** Authenticate the
   bounded first Pell index before claiming full denominator divisibility.
   A signed proof permits an unshifted auxiliary quotient. A degree-382
   variant delays a further factor of `q` until after semantic recovery.
4. **Choose a positive polynomial comparison center.** The single
   expression `C=A+(4Y+1-A)U^2`, with `V=2Y^2(e+1)` in an auxiliary Pell
   pair, supplies two old congruences and restores their nonnegative
   quotients. Composed with proved remainder pools and one bootstrap-bound
   deletion, it gives the direct 221-variable quartic.

The first three routes retain the indexed943/radix67 native/K215
calibration. The fourth is the direct C222 proof-calculus route and uses
neither K215 nor Jones's universal polynomial.

## What improves, and what does not

The fourteen-variable 70/189 and 71/157 forms improve the inspected 73/342
and 76/191 endpoints in both operation count and degree. The thirteen-variable
72/433 form improves the inspected minimum cost of 83, at higher degree than
the 83/114 construction. The ten-variable 76/626 and 77/464 forms improve
the incoming 78/630 and 79/468 forms in both coordinates. The direct quartic
improves the incoming 226-variable, 175-residual, 10,314-term,
height-87,839,583 form in all four metrics; the sparse companion similarly
improves the 227-variable, 176-residual, 7,905-term form.

Existing nine-positive-variable forms still use fewer variables. The
maintained fifteen-variable 66/157 form is still cheaper to evaluate than
our product forms. There is no metric-independent global minimum here.
No literature-wide priority claim, proof of consistency, or new end-to-end
formal-kernel proof is made. Independent review in this archive means a
separate review within the assisted workflow, not outside human peer review.

## Reproduce

Python 3.10 or later, using only the standard library:

```sh
python3 -B verify.py --rebuild
python3 -O -B verify.py --rebuild
```

The default is read-only. `--rebuild` regenerates the twelve direct JSON
artifacts in a temporary directory and compares them byte for byte.
The component graph builders also reconstruct their compact outputs in
memory. The top-level run checks the coefficient recipe, all component
checks, agreement with the independent graph review, every printed direct
residual, and the distribution manifest. To check only distribution bytes:

```sh
python3 -B verify.py --integrity-only
```

The actual final run receipts are in `verification/`. More narrowly scoped
component receipts are retained alongside their code. Finite algebra checks
authenticate the literal artifacts; the unbounded ordinary proofs establish
the mathematical implications, and the retained source theorems establish
the final proof-calculus calibration.

Compile the report with pdfLaTeX from its directory:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

No external repository checkout or network is required for the Python
reproduction. TeX compilation uses ordinary TeX Live packages. `PROVENANCE.json`
pins the audited repository and all six incoming archives. `INTEGRATION.md`
suggests a self-contained intake arrangement without assigning a repository
package number or modifying upstream files. Upstream notices and licenses
are retained; new material uses the top-level MIT No Attribution license.
