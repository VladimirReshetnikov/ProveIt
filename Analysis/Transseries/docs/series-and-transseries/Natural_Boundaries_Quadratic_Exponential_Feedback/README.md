# Natural Boundaries of Quadratic Exponential Feedback

**An exact obstruction to angular Borel summation, analytic-curve rigidity,
and a rational-amplitude dichotomy**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.
The compiled article is 23 A4 pages.

## Main result

For the formal feedback equation

    U(q) = sum_{j>=1} q^j exp(j^2 U(q)),

let Q be its formal compositional inverse, realized on a small left half-disc
by the literal equation

    sum_{j>=1} Q(u)^j exp(j^2 u) = u.

The article proves that every point of the imaginary interval |Im u| < 1/32
is a natural-boundary point of the literal inverse Q, although Q is smooth
up to that interval. The integrated Borel transform of the formal Q is entire
and exponentially bounded on every fixed-width tube around the negative
Borel ray. Its negative-direction Laplace integral recovers Q. Nevertheless,
no open angular neighborhood of the negative ray admits an exponential bound.
Thus neither the inverse formal series nor the forward formal series is
angularly 1-summable in direction pi.

This answers the explicit open-arc question in the repository's
Negative_Ray_Summation_Exponential_Feedback/article.tex, in the subsection
"Angular summability of the quadratic model".

The generalization covers a rational amplitude generating function
A(z) = sum c_j z^j, c_1 != 0, and real slopes that are eventually
alpha*j^2 + beta*j + gamma, alpha > 0. Within this class, finite action
support, convergent inversion, analytic continuation through zero, and
angular negative-direction 1-summability are equivalent. Nonpolynomial
rational amplitudes give a smooth natural boundary. Infinite support alone
is NOT an obstruction for unrestricted, rapidly decreasing amplitudes.

## Proof mechanism

The central technical result concerns a meromorphic heat expansion evaluated
along an arbitrary analytic curve a(t). Each nearest pole retains a nonzero
factor exp(-a'(0)*s/2), where s is its displacement from a(0). Distinct squared
pole displacements prevent persistent cancellation. At rational imaginary
feedback times, periodic Fourier decomposition produces precisely such pole
data. An analytic implicit inverse would force a factorially divergent heat
jet to be analytic, which is impossible.

Other proved results include the nowhere-real-analytic geometry of the
forward branch's boundary curve and exponentially accurate finite-action
approximation, including every fixed number of derivatives. Nine specific
further-research directions are proposed.

## Contents

- `article.pdf`: compiled article.
- `article.tex`: main editable LaTeX source, with embedded bibliography.
- `heat_table.tex`, `oscillation_table.tex`: table inputs used by the source.
- `verify.py`: exact algebra and high-precision numerical diagnostics.
- `exact_checks.json`, `numerical_checks.json`: recorded outputs.
- `verification_output.txt`: captured program output.
- `PROVENANCE.md`: pinned repository sources and primary literature.
- `VALIDATION.md`: build, inspection, and verification record.
- `requirements.txt`: Python numerical dependency.
- `build.sh`: optional build helper.
- The delivered checksum ledger `SHA256SUMS` was verified in full on filing
  (batch 49) and not kept; the delivered archive remains in the repository
  history (see `docs/incoming/README.md`, batch 49 row).

## Reproduce

Use Python 3.10 or newer. Install the pinned numerical dependency:

    python -m pip install -r requirements.txt
    python verify.py

Exact arithmetic uses Python's standard-library fractions.Fraction.
The default complete run also needs mpmath for numerical diagnostics.
The script makes no network requests. Its default exact degree is 16.
Use `--max-order N` with 8 <= N <= 20 to change the degree; independent
composition enumeration has exponential cost. `--output-dir PATH` places
outputs in a different directory. Since the editorial amendment of
2026-09-29 (below) the default output directory is `rerun/` beside the
script; `--output-dir .` regenerates the recorded files, including the two
tables the article inputs, in place.

The supplied tables already exist, so Python is not needed merely to compile
or read the article. With a standard TeX Live or MiKTeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

On Unix-like systems, `sh build.sh` performs the three compilation passes.
The source requires its two table inputs in the same directory. It does not
require a local ProveIt checkout, external font files, or downloaded figures.

## Status and limits

These are conventional mathematical proofs. They have not been checked in
Lean or independently refereed. No Lean build was attempted. The finite
exact tests are reproducible consistency checks, not formal verification
of the analytic theorems. The 120-digit diagnostics are not outward-rounded
interval certificates. The explicit action-truncation bound applies to
exact functions; it does not include floating-point rounding error.

The main proposed contribution is the implicit natural-boundary obstruction
and its rational-amplitude extension, not the classical heat, Fourier,
Lagrange, or general summability tools. Publication priority has not been
established. The article does not determine every individual admissible
Borel ray or the exact growth in shrinking angular neighborhoods.

An entire Borel transform is endlessly continuable in the finite plane.
Accordingly, failure of angular summability here must not be paraphrased as
failure of resurgence without specifying an additional growth convention.
No repository files or branches were modified.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 49 (see `docs/incoming/README.md`). The
following changes were made after filing; everything else is as delivered.

- `article.tex`: an unnumbered "Editorial note (ProveIt, 2026-09-29)"
  environment was added to the preamble, and an editorial note at the end of
  Section 1.1 relates the article to packages filed after its snapshot: the
  sectorial-summability package
  (`Sharp_Negative_Direction_Summability_Exponential_Feedback/`) leaves the
  quadratic case `k = 1` open, and Theorem 2.3 here settles it negatively in
  the angular sense (and so the regularity article's directional question in
  that sense); the inverse coefficients of the two batch-49 quadratic-inverse
  packages at `a = 1` agree with those computed here through degree 16. The
  change is marked in the source by a `% ed. (2026-09-29)` comment. No label,
  theorem or number changed.
- `article.pdf`: rebuilt from the amended source (still 23 pages).
  `VALIDATION.md` describes the delivered build.
- `README.md`: the retired checksum ledger is no longer listed as a package
  file (see "Contents"), and "Reproduce" describes the new default output
  directory.
- `verify.py`: the default `--output-dir` is now `rerun/` beside the script,
  so a default run no longer rewrites `exact_checks.json`,
  `numerical_checks.json` or the two tables the article inputs; every writer
  emits LF line endings on every platform. A default rerun on a copy wrote
  four files into `rerun/` that are byte-identical to the recorded ones, left
  the recorded files untouched, and printed the text of
  `verification_output.txt` (the captured standard output, written by no
  script).

### Batch-50 cross-reference notes (ProveIt, 2026-09-29)

Added when batch 50 was filed; marked in the source by `% ed. (2026-09-29)` comments.

- `article.tex`: an editorial note after the research question
  "Higher-degree and nonpolynomial slopes": answered for integer `d >= 3` by
  `../Natural_Boundaries_Survive_Nonlinear_Feedback/` (batch 50; its
  `thm:main`), which also re-proves `d = 2` independently; noninteger powers
  stay open.
- `article.pdf`: rebuilt (23 pages, unchanged; no errors, undefined
  references, multiply defined labels or duplicate destinations).
