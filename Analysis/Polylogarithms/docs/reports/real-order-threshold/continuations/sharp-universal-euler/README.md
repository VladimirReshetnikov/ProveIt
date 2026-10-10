# The Sharp Universal Euler Constant for Harmonic Polylogarithms

Research continuation for the ProveIt project, 10 October 2026.

**Read `article.pdf`; rebuild from `article.tex` and `sections/`.** The report is based on commit `3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f` of VladimirReshetnikov/ProveIt. The remote repository was not modified.

## Main result

For `g(a,b) = Im Li_{a,b}(i,1)` and the finite Euler transform defined in the article, the following holds for every `a,b > 0`:

- `0 < E_N - g < (9/8) 2^(-N)` for every `N >= 2`.
- The least constant uniform in all positive orders and `N >= 1` is `C_* = max_{b>0} [beta(b) + 2^(-b) eta(b)]`.
- Exact arithmetic proves `1.3021 < b_* < 1.3023` and `1.1365611033 < C_* < 1.1365611046`.

The first-truncation Gaussian maximum was already proved in the source manuscript. The new kernel theorem controls **every later truncation**, which identifies that inherited maximum as the universal Euler constant. No priority claim is made for the classical Euler transform or positive-kernel methods.

The article also proves a generating function for all errors, exact all-order binomial-moment identities, and `Im Li_{s,b}(i,1) < 0` for all real `s >= -1`, `b > 0`. The latter is an analytic-value statement, not a claim of convergence of the boundary series or an Euler bound at negative outer order.

## Reproduce

Python 3.10 or later is sufficient for the dependency-free exact replay:

```sh
python code/verify_exact.py
python -O code/verify_exact.py
```

Both check 1542 positive rational Bernstein coefficients, 282 exact integer power brackets, three axis enclosures, polynomial and finite Euler identities, and a counterexample to universal scaled-error monotonicity. The check regenerates its polynomial data and compares it with the frozen JSON. Its checks remain active under `-O`.

For independent symbolic checks and numerical diagnostics:

```sh
python -m pip install -r requirements.txt
python code/verify_sympy.py
python code/numerical_checks.py
```

SciPy is used only for optional nonrigorous optimization. Numerical discrepancies and optimizers are **diagnostics**, not interval proofs. The numerical script regenerates `data/numerical_diagnostics.json`; the exact verifier is read-only.

Intentional certificate regeneration is separate:

```sh
python code/generate_certificates.py
python code/verify_exact.py
```

The generator uses decimal arithmetic only to propose integer root brackets. Their acceptance depends on exact integer inequalities, never on the proposed decimal approximation alone.

Build the article with a standard TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Files and evidence

`data/bernstein_certificates.json` contains all 1542 coefficients on 82 cells, not just the minimum. `data/axis_certificates.json` contains all root brackets and exact interval endpoints. `reports/` contains the executed replay outputs and build/render review record. `CLAIM_STATUS.json` distinguishes new results, inherited results, diagnostics, and open problems. `PROVENANCE.json` pins the source sections. `integration/` contains proposed manuscript insertion and editorial instructions. `SHA256SUMS` records delivered file hashes.

The main result is a computer-assisted ordinary proof with two independent finite-algebra replay routes. Analytic steps are proved in the article, not formalized in a proof assistant. It has not undergone external peer review.

## Limits

This was a targeted continuation of the real-order Euler material, not a complete audit of all 375 source pages. No false theorem in the inspected canonical source sections is alleged. The main editorial change is to promote the formerly open universal Euler problem, while retaining sharper restricted-domain bounds. The `S_6` period-reduction conjecture, the global integer normalized-radius conjecture, and numerical period-independence questions remain unresolved by this report. See `CORRECTIONS.md` and `integration/INTEGRATION.md`.
