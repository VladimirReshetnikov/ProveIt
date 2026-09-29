# Quadratic Exponential Feedback after Reversion

**Cancellation, finite-core universality, and sharp Borel growth**  
Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Contents

- `article.pdf`: 24-page article, with complete conventional proofs and a research agenda.
- `article.tex`: standalone editable LaTeX source; bibliography is included in the source.
- `verification/verify.py`: exact integer-normalized inverse and marked-core recurrences,
  independent partition-formula and rational-substitution checks, and decimal diagnostics.
- `verification/results_a1/`: completed a=1 run, pure coefficients and cores through degree 240.
- `verification/results_a2/`: completed a=2 run, pure coefficients and cores through degree 180.
- `provenance/sources.json`: pinned repository source, bibliography, and dependency boundaries.
- `provenance/validation.json`: actual computational and PDF-build checks.
- `requirements.txt`: the decimal-diagnostic dependency. Exact arithmetic uses the standard library.
- `SHA256SUMS.txt`: checksums for the packaged files (excluding the checksum file itself).

## Main result

For U(q) = sum_{j>=1} q^j exp(a j^2 U(q)), a>0, write its compositional
inverse as V(z) = sum v_n z^n. Define r_n > 0 by

    r_n (1+r_n) exp(2 r_n) = a n,

and put

    S_n = exp(n r_n (1+2 r_n)/(1+r_n)) / sqrt(1+4 r_n+2 r_n^2).

The article proves

    v_n ~ -S_n exp(-(1+1/a) r_n).

This is Conjecture `conj:quadratic-inverse` in the pinned ProveIt research
manuscript identified in `provenance/sources.json`. The proof controls the
missing signed multiple-tail remainder, rather than merely re-deriving the
already known exact one-tail response.

Additional results include finite-perturbation universality; a sharp
first-omitted-action error for every fixed core with at least two actions;
the constant produced by a slope perturbation of size kappa*j/log(j); and
a sharp entire-Borel positive-ray equivalent, including its prefactor.

## Build the PDF

A TeX Live installation with the standard packages listed in `article.tex`
is sufficient. Run from this directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times. No external BibTeX database, images, or font files are required.

## Reproduce the completed checks

Python 3.10+ is required. The recorded environment was Python 3.13.5 and
mpmath 1.3.0. Install the diagnostic dependency with:

    python -m pip install -r requirements.txt

Run each of the following as a single command:

    python verification/verify.py --a 1 --order 240 --cores 2 3 --out verification/results_a1
    python verification/verify.py --a 2 --order 180 --cores 2 3 --out verification/results_a2

The exact routines work in the normalization c_n = n! [z^n]V. In each core
record, `linear_marker` equals -n! A_{n,M}, not +n! A_{n,M}. JSON integers
are stored as decimal strings to avoid limitations of floating-point JSON
consumers. The modified model changes lambda_2 to 4a+1 and w_3 to 2; it is
computed through degree 120 and keeps mu=lambda_1+w_2 fixed.

The two recorded runs pass 134 assertions each, 268 in total. Independent
finite comparisons are through the ranges stated in article Section 9;
the full degree-240/180 outputs are not claimed independently certified
through every degree. Decimal ratios use 70-digit mpmath, not intervals.
Wall-clock timings in audit reports depend on the runtime and may differ
on rerun.

## Scope and dependencies

The main inverse theorem, sharp core error, borderline slope constant, and
inverse Borel theorem are proved independently of the earlier manuscript's
nontrivial forward asymptotic theorem. The forward/inverse Borel ratio in
Corollary 8.2 additionally uses that forward theorem; this dependency is
explicit in the article.

This is an AI-assisted mathematical research draft, not a Lean-verified or
peer-reviewed development. The theorem targets and novelty claims are
specific to the inspected repository snapshot; literature-wide originality
and publication priority have not been established. The finite computations
are checks of formulas, not proofs of asymptotic limits.

All parameters and core cutoffs are fixed in the asymptotic theorems. No
numerical universal starting index, growing-core uniformity, all-direction
summability theorem, or evaluation of the divergent positive-argument
feedback kernel is asserted. Eventual negativity is not negativity at
every low order: for a=1, v_3=1/2.
