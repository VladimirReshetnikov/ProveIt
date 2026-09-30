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
- The delivered checksum ledger `SHA256SUMS.txt` was verified in full on filing (batch 47) and not kept; the delivered archive remains in the repository history (see `docs/incoming/README.md`, batch 47 row).

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

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 47 (see `docs/incoming/README.md`). The
following changes were made after filing; everything else is as delivered.

- `near_linear_feedback.tex`: an unnumbered "Editorial note (ProveIt,
  2026-09-29)" environment was added to the preamble. Editorial notes were
  added after three further-research questions: "Growth away from the
  positive Borel ray" (partly answered, for unit amplitudes, by the later
  negative-ray package, where this class has `A = 0`, and by the
  sectorial-summability package for every order `k > 1`), "Compatible
  acceleration and optimal truncation" (its uniform-remainder part answered by
  the sectorial-summability package; acceleration and optimal truncation
  still open) and "Inversion and parameter limits beyond fixed resonances"
  (a cross-link to the weighted-type package's zero-loss theorem, which does
  not settle it; its limsup part is settled, by an editorial deduction,
  through the batch-52 exact-type package, and a root limit remains open;
  see below). In Appendix A the first pinned identifier, which the
  delivered text called a "repository root tree", is now called a commit,
  with an editorial note recording the correction. Every change is marked in
  the source by a `% ed. (2026-09-29)` comment. No label, theorem or number
  changed.
- `near_linear_feedback.pdf`: rebuilt from the amended source (26 pages; the
  delivered PDF had 25). `data/build_report.json` describes the delivered
  build and was not updated.
- `SOURCES.md`: the same identifier is labelled as a commit.
- `README.md`: the retired checksum ledger is no longer listed as a package
  file (see "Files").
- `code/verify.py`: the JSON and table writers emit LF line endings on every
  platform. A rerun on a copy reproduced `data/verification.json` and both
  tables byte for byte. The program rewrites the two tables the article
  inputs; run it on a copy.

### Batch-52 cross-reference notes (ProveIt, 2026-09-29)

Added when batch 52 was filed; marked in the source by
`% ed. (2026-09-29, batch 52)` comments.

- `near_linear_feedback.tex`: at "Inversion and parameter limits beyond
  fixed resonances", the last clause of the existing editorial note ("so
  the question stays open") now points to a new editorial note: by
  `../Exact_Weighted_Type_Beyond_Log_Convexity/` (batch 52; its
  `thm:classificationintro` and `cor:scalarscaling`), log-convexity is not
  needed. Lemma 4.1 (`lem:b`) makes `b` eventually nondecreasing with
  `b = o(log x)`, so the weight `e^(m b_m)` is admissible
  (`V_n = exp(n max_{m<=n+1} b_m)` is a supermultiplicative representative),
  and Theorem 2.3 (`thm:main`) then gives
  `limsup |q_n|^(1/n) e^(-b_n) = 1` for the inverse coefficients. Whether
  `|q_n|^(1/n) e^(-b_n)` converges remains open. The deduction is editorial;
  it was re-derived on filing and is stated in neither article.
- `near_linear_feedback.pdf`: rebuilt with `latexmk -pdf` (26 pages,
  unchanged; no errors, undefined references, multiply defined labels,
  duplicate destinations or overfull boxes). `data/build_report.json` still
  describes the delivered build.
