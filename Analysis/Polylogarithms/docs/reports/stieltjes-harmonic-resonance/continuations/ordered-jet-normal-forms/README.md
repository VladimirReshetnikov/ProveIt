# Ordered Harmonic Jets

**Exact orientation ranks, Stieltjes commutators, and depth-four Hurwitz finite parts**  
ProveIt research continuation · 10 October 2026

The article supplies ordinary mathematical proofs of an all-depth formal linear normal form, the complete depth-four finite part, all-index convergent Stieltjes commutator identities, ordinary polylogarithmic Mellin formulas, and a Gamma-weighted antiderivative family whose integrals over [1,2] equal the ordinary Stieltjes constants.

## Main results

The rational linear orientation quotient at word length j and logarithmic degree r has dimension binomial(j+r-1,r)-p_{<=j}(r). The complete set entering a transverse depth-d finite part has quotient dimension 2^(d-1)-p(d). The quotient is described equivariantly by orbit augmentation spaces. This answers the formal depth-four organization question in the inspected *Ordered Hurwitz Germs at Every Depth* report and extends it to every depth.

At depth four, the three orientation channels are D, Theta, and Omega_2. Three positive rays recover them through an exact matrix with determinant -1/144. Single-letter closure occurs precisely for equal inner slopes, relative to the stated universal stuffle algebra.

The analytic identities provide explicit absolutely convergent series, ordinary Mellin integrals involving polylogarithm order derivatives, and all-index Gamma-weighted primitives. No bounds or inequalities are the main research target; convergence estimates are included only where needed for proofs.

## Scope

The rank is a **rational linear quotient dimension**, not arithmetic independence, transcendence degree, or a module rank after scalar extension by single-letter values. Classical quasi-shuffle, symmetric-sum, Gamma-generating, and Hurwitz continuation inputs are attributed. No proof-assistant formalization or exhaustive priority claim is made. The broader arithmetic reduction of orientation constants is not proved. No remote repository files were changed.

The complete predecessor TeX and selected repository text were inspected. Incoming archives were inventoried by visible metadata, not exhaustively unpacked. See `PROVENANCE.json` and `CORRECTIONS_AND_SCOPE.md`.

## Contents

- `manuscript/article.tex`, `manuscript/article.pdf`: self-contained research article with proofs, examples, eight further research topics, and three appendices.
- `code/verify_exact.py`: integer quasi-shuffle and rational symbolic certificates.
- `code/harmonic_em.py`: floating-point harmonic constant-term evaluator.
- `code/verify_numeric.py`: 83 reproducible numerical regressions.
- `data/`: exact and numerical output in JSON and text; PDF quality record.
- `integration/`: namespaced manuscript fragment and integration guidance.
- `requirements.txt`, `Makefile`, `PROVENANCE.json`, `SHA256SUMS`: reproducibility and provenance.

## Reproduce

Use Python 3.10 or later and a TeX installation with newtx, amsmath, amsthm, microtype, geometry, mathtools, booktabs, enumitem, fancyhdr, hyperref, and bookmark. The recorded run used Python 3.13.5, mpmath 1.3.0, SymPy 1.14.0, and pdfTeX 1.40.26.

```sh
python3 -m pip install -r requirements.txt
make check
make pdf
```

`make clean` removes TeX build intermediates and Python cache files, not the PDF or recorded results. The exact checker verifies 146 symmetric-sum instances, 81 contact coefficients, eight Gamma-bridge word identities, the rank table, and the displayed quartic algebra. These checks supplement the proofs; finite tests are not extrapolated into all-depth theorems.

The numerical program uses 80 decimal working digits and compares (N,M)=(48,32) and (64,40). Its output is **not interval arithmetic**. Nested representations share the recursive Euler–Maclaurin code; separate one-variable calls and finite-difference checks have distinct dependencies. All residuals and tolerances are preserved. Increasing the asymptotic order at a fixed cutoff is not asserted to converge.

## Integration

Suggested destination: `Analysis/Polylogarithms/docs/reports/ordered-jet-normal-forms/`. The insertion fragment can be included in the integration/differentiation part of the main manuscript after editorial review. Its labels use the `ojnf:` prefix. See `integration/INTEGRATION.md` for the exact status update and exclusions.
