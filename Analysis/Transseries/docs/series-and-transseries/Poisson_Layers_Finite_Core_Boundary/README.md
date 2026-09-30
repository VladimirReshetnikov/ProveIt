# Poisson Layers at the Finite-Core Boundary of Exponential-Feedback Transseries

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Contents

- `poisson_feedback_layers.pdf`: the 20-page article, with proofs, references,
  a proof-dependency audit, and eight further research directions.
- `poisson_feedback_layers.tex`: self-contained LaTeX source; no external
  bibliography, figures, or repository notation files are required.
- `verification/verify.py`: exact rational coefficient checks and positive
  log-domain numerical diagnostics.
- `verification/results/`: recorded JSON and CSV outputs.
- `verification/run_log.txt`: the recorded full verification run.
- `requirements.txt`: numerical dependency versions used in the recorded run.
- The delivered checksum ledger `SHA256SUMS.txt` was verified in full on
  filing (batch 48) and not kept; the delivered archive remains in the
  repository history (see `docs/incoming/README.md`, batch 48 row).

## Main mathematical result

For the formal feedback equation

    U(q) = sum_{j>=1} q^j exp(a j^p U(q)),   a>0, p>1,

let w[n,M] count configurations with exactly one primitive action above M.
Let u[n](s) mark each occurrence of action M+1 by s. In the range
(M+1)(p-1)>1, uniformly on compact parameter sets with a strict margin,

    u[n](s) = w[n,M] exp(s nu[n,M]) (1+o(1)),
    nu[n,M] = n r/(1+r) exp(-M p r),
    r(1+r)^(p-1) exp(p r) = a n^(p-1).

The result allows bounded nonnegative changes to the actions within the core,
with the first amplitude fixed at one. The error after taking the logarithm
of the coefficient ratio is o(1), even when nu diverges.

At p=1+1/M, the missing factor is exp(r^(M+1)/a^M). A finite Poisson window
appears at

    p = 1 + 1/M + ((M+1) log log n + theta)/(M log n),

with parameter exp(-theta)/(a^M (M+1)^(M+1)). The article also proves
bounded-intensity total-variation convergence, diverging-intensity Gaussian
and large-deviation laws, fixed-count relative probabilities, and joint
independence from the Gaussian giant-action fluctuation.

## Scope and status

This is an AI-assisted research draft with conventional proofs, not a
Lean-verified development. Global originality and publication priority have
not been established. It continues specific first-omitted-action and critical
boundary questions in the repository manuscript named below.

The positive coefficient identity, strict finite-core reduction, and
finite-core saddle method are inherited from that manuscript and are
re-established here in the compact-uniform form needed for the extension.
The uniform marked comparison, scalar intensity, complete boundary factor,
shifted transition window, and joint distributional consequences are the
proposed contributions.

The article does not claim to solve the signed quadratic inverse conjecture,
the general regularly varying-tail problem, a growing-core limit, or an
analytic summability problem. It does not claim a full total-variation
Poisson approximation at diverging intensity.

## Repository provenance

Inspected commit:

    0c973d8f5e7ef4550f4df1bf486d890037fd9f14

Main predecessor:

    Analysis/Transseries/docs/series-and-transseries/
    Finite_Core_Universality_Exponential_Feedback/article.tex

Its blob:

    c2b6faf623003111e9d9e6bbb162a67429f3ce42

Relevant predecessor research subsections: "Regularly varying feedback and
critical logarithmic boundaries" and "Joint laws for the finite background
cloud". The source and literature references are given in the article.
No repository branch or file was modified to produce this bundle.

## Build the PDF

From this directory, run the following command three times:

    pdflatex -interaction=nonstopmode -halt-on-error poisson_feedback_layers.tex

A usual TeX Live or MiKTeX installation with the packages listed in the
preamble is sufficient. The recorded final build produced 20 A4 pages,
without undefined references or overfull/underfull box warnings. The PDF
was visually inspected, including its main equations, table, and references.

## Reproduce the checks

The recorded environment was Python 3.13.5, NumPy 2.3.5, and SciPy 1.17.0.
Install the numerical dependencies in a suitable Python environment:

    python -m pip install -r requirements.txt

Run all checks and diagnostics:

    python verification/verify.py --output verification/results

Run just the fast exact checks and their floating-point crosschecks:

    python verification/verify.py --exact-only --output verification/quick_results

The `--exact-only` mode omits the larger coefficient and critical-window
tables; it still imports NumPy/SciPy and runs the 32 floating crosschecks.
No network access is used during verification.

Recorded checks: 288 exact rational assertions passed, comparing the
triangular recurrence with independent integer-partition enumeration through
degree 16 for slopes j^2 and j^3, several markers, and several cutoffs.
All 32 floating crosschecks passed; their maximum absolute logarithmic
discrepancy was 7.105427357601002e-15.

The coefficient diagnostics at n=80,160,320 use ordinary floating-point
arithmetic. They demonstrate finite-size behavior and slow convergence;
they are not interval-certified enclosures or proofs of the asymptotic
claims. The large-n critical-window table evaluates saddle quantities only,
not coefficients of orders as large as 10^48. All asymptotic results are
proved in the article independently of these computations.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 48 (see `docs/incoming/README.md`). The
following changes were made after filing; everything else is as delivered.

- `poisson_feedback_layers.tex`: an unnumbered "Editorial note (ProveIt,
  2026-09-29)" environment was added to the preamble. An editorial note after
  the abstract states the scope of the title: at the boundary `p = 1 + 1/M`
  the missing factor diverges, consistently with the finite-core package's
  cutoff theorem, and the finite Poisson limit occurs only in a moving window
  above the boundary, outside that package's fixed-parameter theorem; it
  records that the article sharpens that package (its intensity equals the
  finite-core one-occurrence scale term by term) and that the
  microscopic-condensation package proves the total-variation Poisson law at
  diverging intensity for `lambda_j = j^2`. Short notes after the remark
  "What is not a consequence here" and after the further-research questions
  "A full local Poisson approximation at diverging intensity" (answered for
  `M = 1`, `p = 2`, `a = 1` by the microscopic-condensation package) and "The
  signed quadratic inverse conjecture" (claimed proved, independently and
  unreviewed, by the two batch-49 quadratic-inverse packages) give the
  cross-references. Every change is marked in the source by a
  `% ed. (2026-09-29)` comment. No label, theorem or number changed.
- `poisson_feedback_layers.pdf`: rebuilt from the amended source (still 20
  pages).
- `README.md`: the retired checksum ledger is no longer listed as a package
  file (see "Contents").
- `verification/verify.py`: the CSV and JSON writers emit LF line endings on
  every platform. A rerun on a copy (`--output verification/results`)
  reproduced `exact_checks.json` and `critical_window_saddles.csv` byte for
  byte; `coefficient_diagnostics.csv` differed only in the last digits of two
  floating values (NumPy/SciPy on Windows). `--output` is relative to the
  working directory, and the default rewrites the recorded
  `verification/results/`; run it on a copy. `verification/run_log.txt` is
  recorded program output and is written by no script.
