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
- `SHA256SUMS`: checksums of the delivered files except itself.

## Reproduce

Use Python 3.10 or newer. Install the pinned numerical dependency:

    python -m pip install -r requirements.txt
    python verify.py

Exact arithmetic uses Python's standard-library fractions.Fraction.
The default complete run also needs mpmath for numerical diagnostics.
The script makes no network requests. Its default exact degree is 16.
Use `--max-order N` with 8 <= N <= 20 to change the degree; independent
composition enumeration has exponential cost. `--output-dir PATH` places
outputs in a different directory.

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
