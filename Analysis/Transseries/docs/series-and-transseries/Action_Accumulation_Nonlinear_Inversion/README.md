# Action Accumulation and Nonlinear Inversion

**A Laplace–measure calculus, hidden oscillations, and limits of Hardy-field realization**  
Research manuscript, 29 September 2026.

## Contents

- `action_accumulation_and_inversion.tex`: standalone, editable article source.
- `action_accumulation_and_inversion.pdf`: 28-page compiled article with proofs, numerical tables, bibliography, a formalization roadmap, and eight further research directions.
- `verify.py`: executable symbolic and high-precision numerical checks.
- `verification_results.json`: results from the recorded successful run.
- `SOURCE_NOTES.md`: repository snapshot, inspected documents, primary references, and retrieval limitations.
- `build.sh`: minimal reproducible PDF build.
- `requirements.txt`: the dependency versions used for the recorded checks.
- `SHA256SUMS.txt`: checksums for the packaged files other than the checksum list itself.

## Results developed in the article

The paper proves a composition and inversion calculus for exponentially weighted complex action measures, including accumulating supports with no positive action gap. It gives an explicit inverse measure, uniform truncation bounds, a compact-support rooted-tree majorant, and positivity and stability consequences.

The example A(x) = sum_{j>=1} j^(-2) exp(-x/j) has an exact Poisson–Bessel resolution. Its difference from 1/x has infinitely many zeros despite being smaller than every inverse power. The paper proves explicit finite-mode error bounds and a refined asymptotic location of the zeros, and derives Hardy-field and o-minimal obstructions. It then analyzes nonlinear inverses and exact zero transport. In the zero-gap, parameter-free example y = x + A(x), the inverse has a convergent Catalan asymptotic expansion but cannot belong to a Hardy field containing the identity germ.

Theorems are supported by human-readable mathematical proofs. They are not Lean formalizations. No exhaustive historical-priority claim is made, and no named general conjecture is represented as settled. The repository comparison is targeted, not a full audit of the large consolidated transseries volume.

## Build the article

A standard TeX Live installation with pdfLaTeX, Latin Modern, amsmath, hyperref, xurl, and the other packages named in the source is sufficient. No external images, private macros, or BibTeX run are needed.

```sh
sh build.sh
```

Or run `pdflatex -interaction=nonstopmode -halt-on-error action_accumulation_and_inversion.tex` three times.

## Reproduce the checks

Requires Python 3.10 or later, `mpmath`, and `sympy`.

```sh
python -m pip install -r requirements.txt
python verify.py --output verification_results.json
```

The recorded environment was Python 3.13.5, mpmath 1.3.0, and SymPy 1.14.0. The script uses 120 decimal digits globally and 65 digits for the exact Bessel evaluations. It rejects a global precision below 110 digits because the independent Hurwitz-zeta evaluation is cancellation sensitive.

Checks include the core coefficient formula through coupling degree six, Catalan normalization through degree twelve, Bessel coefficients through degree eight, three independent Poisson–Bessel comparisons, finite and accumulating atomic inverse enclosures, a finite-measure composition test, and three finite-mode zero sign-bracket tests. All assertions passed in the recorded run.

**Numerical qualification:** these are high-precision floating-point consistency checks, not outward-rounded interval proofs. The analytical truncation inequalities are proved in the paper. Fully certified numerical endpoints would additionally require interval enclosures for all function evaluations and rounding errors. Finite numerical checks do not replace the proofs of the infinite statements.
