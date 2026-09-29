# Entropic Edgeworth Expansions for Geometric Uniform Laws

A proof of the explicit ProveIt entropic Edgeworth conjecture, with positive-order
Renyi extensions and uniform finite-prefix asymptotics.

Research manuscript prepared with ChatGPT, 28 September 2026.

## Main result

For independent U_j uniform on [-1,1], set

    X_q = (1-q) sum_{j>=0} q^j U_j,
    Z_q = X_q / sqrt(Var(X_q)),  epsilon = 1-q.

The article proves, for every fixed N >= 2,

    D(Z_q || N(0,1)) = sum_{n=2}^N d_n epsilon^n + O_N(epsilon^(N+1)).

In particular,

    d_2 = 3/100,
    d_3 = 33/500,
    d_4 = 427297/4410000.

The result resolves the statement labeled `conj:entropic-edgeworth` in the
inspected ProveIt manuscript. It does not settle the separate global entropy
monotonicity conjecture. The paper also proves uniform expansions for every
fixed positive Renyi order and for finite prefixes with q^(2m) bounded away
from one. Exact coefficients are supplied through order eight.

These are conventional mathematical proofs, not Lean-checked theorems.
General entropic Edgeworth theory is credited to the primary literature.
Priority for the exact extensions has not been exhaustively investigated.
See SOURCE_AUDIT.md and VERIFICATION.md.

## Package contents

- `article.pdf`: compiled 20-page article.
- `article.tex`: full LaTeX source with embedded bibliography.
- `figures/*.pdf`: the two vector figures required for compilation.
- `code/coefficients.py`: exact Shannon and Renyi coefficient generation.
- `code/test_exact.py`: independent low-order and finite-prefix checks.
- `code/numerics.py`: floating-point Fourier diagnostics, not enclosures.
- `code/plots.py`: regenerate figures from the CSV.
- `data/exact_coefficients.json`: exact coefficients, intermediate polynomials,
  and Gaussian product moments.
- `data/coefficients.txt`: readable coefficient output.
- `data/numerical_checks.csv`: numerical diagnostics and grid-refinement data.
- `data/test_results.txt`: the recorded four-test regression run.
- `requirements.txt`: the tested Python package versions.

## Compile

The vector figures are already included; no Python execution is necessary.
Use a TeX installation with latexmk, the Libertinus package, and the standard
packages listed in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

No external BibTeX database is required. The source uses relative paths and
should be compiled from the package root. Font programs are not distributed
with this package; use the normal TeX package installation.

## Reproduce calculations

Tested with Python 3.13.5. Install the optional calculation dependencies with:

```sh
python -m pip install -r requirements.txt
python code/coefficients.py --order 8 --output data
python code/test_exact.py
python code/numerics.py --output data
python code/plots.py
```

The exact coefficient calculation needs only SymPy. Orders 2 through 14 are
accepted, although high orders can be expensive. The supplied numerical
comparison expects coefficient data through at least order eight. Run without
Python's `-O` flag, which disables the coefficient program's internal assertions.

The scripts modify only their output files. They do not read credentials,
connect to the internet, or modify the ProveIt repository.

## Mathematical and computational boundaries

The uniform analytic remainder is proved in the article; no numerical result
is used as a hypothesis. The symbolic checks validate finite algebra only.
The numerical script truncates a sinc product, uses floating-point FFTs, clips
small negative reconstructed values, and restricts sufficiently wide supports
to [-9,9] for the information integral. It is not an interval-arithmetic
implementation. Grid agreement is not a certified error bound.

The all-orders series is proved asymptotic, not convergent. Constants in the
remainder theorem are not optimized or made numerically explicit. Renyi
uniformity is on compact subsets of (0,infinity), not for growing order or
infinite order. Finite-prefix uniformity excludes q^(2m) approaching one.

Nine further research questions and a suggested Lean formalization plan are
included in the article.
