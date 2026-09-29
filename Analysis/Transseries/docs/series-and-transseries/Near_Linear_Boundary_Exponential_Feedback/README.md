# The Near-Linear Boundary of Exponential Feedback

**A self-consistent Lambert law, coefficient large deviations, and a cascade of Borel-growth resonances**

Research article prepared for Vladimir Reshetnikov's ProveIt program, 29 September 2026.

## Main results

The paper extends the explicit “near-linear transition” question in ProveIt's `Exponential_Feedback_Regularity_Classification/article.tex`.

For the formal equation

`U(q) = sum_{j>=1} c_j q^j exp(lambda_j U(q))`,

with admissible slopes `lambda_j = j L(j)` and exponentially controlled positive amplitudes, it proves

`u_n^(1/n) ~ c_1 exp(b_n)`, where `b_n exp(b_n) = L(n/(1+b_n))`.

The hypotheses require a positive nondecreasing C1 profile, unbounded L, elasticity `x L'(x)/L(x) -> 0`, and convexity of `x L(x)`. The result also permits any nonnegative slope perturbation bounded in absolute value by `Cj`. Amplitudes satisfy `exp(-D(j-1)) <= c_j/c_1^j <= exp(D(j-1))`.

A length large-deviation theorem has rate `r - 1 - log(r)`. A separate maximum-term theorem gives the positive-ray growth of every factorial-normalized entire Borel transform. These transforms are entire but grow too rapidly for positive-direction standard Borel–Laplace summation of any finite Gevrey order.

The stretched-logarithmic family `L(j) = exp((log j)^gamma)` yields a finite explicit power–logarithmic expansion at each `0 < gamma < 1`, constants `exp(1/m)` at `gamma = 1 - 1/m`, and a proved uniform double-scaling profile through each fixed resonance. Another example shows that replacing the moving-argument equation by `W(L(n))` may lose a constant factor or an unbounded correction.

## Files

- `near_linear_feedback.pdf`: compiled article, with complete proofs and ten further-research directions.
- `near_linear_feedback.tex`: main source; the two small TeX tables in `data/` are its only local input dependencies.
- `code/verify.py`: independent exact coefficient checks, finite bounds, reversion identities, and numerical normalizer diagnostics.
- `data/verification.json`: full recorded results, including rational coefficients through order 24 and moving-parameter diagnostics.
- `data/run_output.txt`: recorded verification output.
- `data/envelope_table.tex`, `data/resonance_table.tex`: generated tables used in the paper.
- `SOURCES.md`: repository snapshot, primary references, and comparison boundaries.
- `requirements.txt`, `Makefile`: reproduction instructions.
- `SHA256SUMS.txt`: checksums for the archive contents other than this ledger itself.

## Reproduce

Python 3.10 or later is recommended. Install the numerical dependencies and run:

```sh
python -m pip install -r requirements.txt
python code/verify.py
pdflatex -interaction=nonstopmode -halt-on-error near_linear_feedback.tex
pdflatex -interaction=nonstopmode -halt-on-error near_linear_feedback.tex
```

`make verify` reruns computation; `make pdf` performs three LaTeX passes. A normal TeX Live installation with Latin Modern, AMS packages, microtype, geometry, hyperref, and fancyhdr is sufficient. No fonts or repository-local macros are included or required.

The recorded run passes **467 exact finite checks**, with the feedback recurrence evaluated through order 24. Exact arithmetic uses Python's standard `fractions.Fraction`. NumPy/SciPy calculate the finite logarithmic envelope table; mpmath calculates the resonance normalizers at 75 decimal working digits and the moving-parameter normalizers at 100 digits.

## Proof and numerical status

The limit theorems have conventional proofs in the article. No new Lean formalization is claimed. The exact arithmetic checks are independent finite tests, not a formal proof of the asymptotic statements.

The coefficient result is an equivalent for the nth root, **not** a multiplicative equivalent for `u_n` itself. The transform results concern **logarithms** of Borel transforms, not multiplicative equivalents for the transforms. Composition-length concentration does not establish a largest-action law or a central limit theorem.

Floating-point tables are **not outward-rounded interval certificates**. Resonance diagnostics evaluate the proved implicit asymptotic normalizer, not the infinite Borel function. Moderate-size envelopes can converge very slowly. The positive-ray obstruction does not rule out useful summation in other directions or a separately constructed compatible acceleration.

The work answers the inspected repository question under the stated hypotheses. External publication priority has not been established by an exhaustive literature search. No repository branch was modified.
