# When Dougall Tails Terminate

**A rationality classification, Stieltjes cancellation, and an all-depth harmonic–polylogarithmic sum formula**

Prepared for Vladimir Reshetnikov's ProveIt programme, 11 October 2026.

Repository pin: `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.

## Principal results

The article proves a complete classification of rational and finitely terminating centered Gamma quotients at all integral resonances of the stated positive-parameter Rogers–Dougall family. The only terminating loci are the short-positive-integer polynomial loci and a symmetric exceptional Laurent-polynomial locus. A rational difference equation upgrades formal asymptotic termination to an exact identity.

It also constructs analytic families with zero summed remainder but nonrational summands. This distinguishes infinite cancellation from term-by-term termination.

A symmetric resolvent identity then gives all fixed-order convergent polygamma moments. Its boundary version displays generalized Stieltjes constants explicitly; taking the resolvent difference cancels them at every order. A normalized half-center Gamma generator evaluates weighted harmonic-composition sums at every weight and depth in ordinary zeta values and log(2). The article gives linear through quartic examples, a dilogarithmic integral, a signed level-two multiple-polylogarithm formula, Euler primitives, and zero-safe derivatives.

The classical Rogers–Dougall summation and the earlier repository all-resonance continuation are antecedents, not new claims. Global literature priority is not established. The S6 conjecture is not resolved. The contents of the five incoming ZIP archives could not be inspected; their metadata was inventoried only. No remote repository files were changed.

## Contents

| File | Purpose |
|---|---|
| `article.pdf`, `article.tex` | Complete article with proofs, examples, nine further questions, and bibliography. |
| `code/dougall_tail.py` | Exact Gamma-shift divisor matching and finite coefficient engine. |
| `code/verify_exact.py` | 21,009 finite exact regression assertions. |
| `code/verify_numeric.py` | 28 independent 40-digit numerical diagnostics, runnable in three parts. |
| `results/exact_checks.json` | Exact assertion counts and tested environment. |
| `results/numerical_checks.json` | Every numerical parameter, value, residual, and method. |
| `results/numerical_part*.json` | Individual diagnostic-part records. |
| `results/coefficient_table.json` | Exact expressions for m=0,…,5 and k=1,2,3. |
| `results/document_preflight.json` | PDF build, page, reference, and render checks. |
| `identity_index.json` | Machine-readable result index and domain restrictions. |
| `integration/manuscript_addition.tex` | Compact three-page additive insertion with separate labels. |
| `integration/preview.pdf`, `integration/preview.tex` | Compiled preview and its wrapper. |
| `integration/README.md` | Suggested placement and review cautions. |
| `notes/SOURCE_AUDIT.md` | Inspected sources, pin, and explicit access limits. |
| `notes/CORRECTIONS_AND_SCOPE.md` | Necessary distinctions and novelty limitations. |
| `requirements.txt`, `Makefile` | Dependencies and reproducible commands. |

## Reproduce

Tested environment: Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0, pdfLaTeX.
Only that Python environment is claimed to have been executed.

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py --part 1
python code/verify_numeric.py --part 2
python code/verify_numeric.py --part 3
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The numerical parts can take a few minutes, depending on the machine. Omitting `--part` runs all three. Run tests on a working copy: they rewrite the result records. The combined numerical report is regenerated once all three part reports exist.

An exact coefficient example:

```python
import sys
sys.path.insert(0, "code")
from dougall_tail import gamma_coefficients, harmonic_sum_coefficient

coefficients = gamma_coefficients(max_u=5, max_t2=3)
print(harmonic_sum_coefficient(m=4, k=1, coefficients=coefficients))
```

`L` denotes log(2), `Zr` denotes zeta(r), and the coefficients are ordinary Taylor coefficients, not derivatives. The result above evaluates the sum of C_4(n)/(2n+1)^3, where C_4(n) = (2 H_n^4 + 4 H_n H_n^(3))/3. It does not evaluate H_n^4 alone.

## Evidence status

All central results have analytic or algebraic proofs in the article. The exact checks validate finite implementations; they are not proof-assistant formalization. The numerical checks use a finite head plus an Euler–Maclaurin tail, and one independent quadrature. They are not rigorous interval enclosures. At 40 working digits, all 28 checks passed the scaled-residual threshold 1e-28; the maximum observed scaled residual was approximately 5.511e-40. This observation does not certify forty correct digits.

The most important guards are: rationality is over the real coefficient field; a zero summed remainder is not termination; a zero Gamma-factor value need not have zero derivatives; and the all-depth theorem evaluates a weighted composition/color sum, not every individual multiple-zeta value.
