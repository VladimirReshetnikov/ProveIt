# Thue–Morse Mellin Renormalization

**Fabius-controlled derivative asymptotics, positive dyadic solutions,
and gamma-tower uniqueness**

Research article prepared on 4 September 2026 as an extension to the
ProveIt Thue–Morse atlas supplied in the request.

## Contents

- `thue_morse_mellin_and_gamma.pdf`: the compiled, 24-page article.
- `thue_morse_mellin_and_gamma.tex`: self-contained LaTeX source, including
  its bibliography. No external figures or bibliography files are required.
- `verify_results.py`: reproducible exact and high-precision numerical checks.
- `results_48.json`: 60-digit computations with 48 quadrature nodes.
- `results_80.json`: 80-digit computations with 80 quadrature nodes.
- `SHA256SUMS.txt`: checksums of the other files in this directory.

## Main results

Section 4 proves an all-orders expansion for normalized derivatives at the
negative-integer zeros of the shifted Thue–Morse Dirichlet function, with
finite coefficient formulas, a uniform dyadic q-Gevrey remainder, and an
optimal-truncation bound. The same section also derives the exact order
and type of this entire function.

Section 6 classifies all completely monotone solutions of the basic dyadic
equation by positive measures on one multiplicative period. Section 7
shows that distinct positive normalized towers can have the same full
formal integer-order expansion, with a quantitative beyond-all-orders
bound on their discrepancy. Section 8 gives a boundary condition that
uniquely selects the canonical solution and its entire differential tower.

## Compile the article

Use a standard TeX Live or MiKTeX installation providing the packages
listed in the source. With latexmk:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error thue_morse_mellin_and_gamma.tex
```

Alternatively run `pdflatex` on the source three times to settle the table
of contents and cross-references. No shell escape or network access is
required for compilation.

## Reproduce the calculations

The computations supplied here used Python with mpmath 1.3.0 and SymPy
1.14.0. An environment matching those package versions can be prepared with:

```sh
python -m pip install mpmath==1.3.0 sympy==1.14.0
python verify_results.py --dps 60 --nodes 48 --output results_48.json
python verify_results.py --dps 80 --nodes 80 --output results_80.json
```

The script itself needs no network access. It checks coefficient identities
through degree 12 with exact rational symbolic arithmetic. It evaluates
C_rho from its original Q-integral, separately from the claimed asymptotic
expansion, and compares the results to successive truncations. The JSON
reports also include phase-dependent solutions and functional-equation
residuals. Runtime fields naturally vary between machines.

## Scope of the claims

The article contains mathematical proofs, but has not undergone peer review
or Lean formalization. The numerical calculations are high-precision
floating-point checks, not interval-certified enclosures. Historical
priority of the candidate research contributions has not been exhaustively
established. The article separates classical ingredients, new derivations,
numerical observations, and proposed further work. Its source audit also
records an early potentially relevant preprint whose linked full text could
not be retrieved. No original repository files were modified.
