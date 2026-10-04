# Critical Stokes Reversion and q-Gamma Cores

**Exact Mellin–Borel completion, q-Pochhammer summability, and ramified inverse transseries**  
Research article prepared for Vladimir Reshetnikov, 4 October 2026.

## Files

- `critical_stokes_q_reversion.pdf`: the 32-page article.
- `critical_stokes_q_reversion.tex`: self-contained LaTeX source, including its bibliography.
- `verify.py`: exact symbolic checks and high-precision numerical diagnostics.
- `results.json`: recorded results from a successful verification run.
- `verification.log`: console output of that run.
- `proof_review.md`: internal scope, sign, and proof-dependency review.
- `requirements.txt`: versions of the two Python dependencies used for the recorded run.
- `build.sh`: two-pass PDF build, using a standard TeX installation.
- `SHA256SUMS.txt`: checksums of the other delivered files.

No repository modification was performed. No external graphics, custom fonts, or
external bibliography files are needed to compile the article.

## Main results

The article proves an exact lateral Borel reconstruction formula for the moving
q-factorial log((exp(-a*h); exp(-h))_infinity), initially for real 0<a<1 and
Re(h)>0, and continues it locally in the parameter. The proof uses Mellin
inversion, the functional equations of the Hurwitz and Riemann zeta functions,
and an explicitly controlled principal-value kernel. Section 7 translates the
formula into the statement labeled Conjecture 5 in Fantini–Rella,
arXiv:2506.08265v2. Its complete antisymmetric-weight criterion also proves
the statement labeled Conjecture 1 there.

The inversion results distinguish the original function from a selected sum of
its formal expansion. They include a convergent ramified inverse construction
at order-r critical points, a moving-fold chart, higher inverse coefficients,
and a cancellation rule for the effective fractional action. Applications
include parameter inversion of q-gamma, inversion of the moving q-factorial
with respect to h=-Log(q), and a particularly explicit reflected q-gamma
product with no Stokes jump but nonzero flat inverse splitting.

Section 14 contains ten proposed research directions. Appendix A records the
proof dependencies and scope boundaries; Appendix B collects the sign conventions.

## Research status

This is an unrefereed research article with conventional mathematical proofs.
The claimed implications for the two specified published conjectures have not
been independently refereed or formalized. No worldwide first-priority claim
is made, and the source comparison is not an exhaustive literature review.
Classical ingredients, including resurgent closure and the analytic Morse
construction, are explicitly credited rather than claimed as new.

There is no claim of a universal, globally single-valued inverse for every
complex transseries. The formal algebra, sectorial realization, summation
convention, and inverse sheet must be specified. Arithmetic averaging is used
only for the scalar logarithmic summation problem; it is not silently substituted
for an algebra-compatible Écalle median under nonlinear operations.

## Rebuild the PDF

Run from this directory:

```sh
sh build.sh
```

Equivalently, run the following command twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error critical_stokes_q_reversion.tex
```

The delivered PDF was built with pdfTeX 1.40.26. The final build has no undefined
references, missing citations, overfull boxes, underfull boxes, or LaTeX warnings.
The PDF was rendered and inspected, including the displayed formulas and tables.

## Run the checks

Python 3.10 or later is sufficient. Install the dependencies in an environment
of your choice and run:

```sh
python -m pip install -r requirements.txt
python verify.py --output results-new.json
```

The recorded run passed **144 exact SymPy assertions** and used **110 decimal
digits** for mpmath calculations. The typical runtime in the preparation
environment was about 22 seconds. Exact checks cover displayed finite algebraic
identities; they do not prove the analytic theorems. The floating-point tests
are diagnostics, not outward-rounded interval certificates.

The summability checks evaluate the original product independently of an
accelerated Borel-kernel sum. Critical roots are solved in normalized coordinates,
using the original q-gamma function. Reported reconstruction residuals range
from approximately 10^-51 to 10^-112 in the selected examples; their precision
must not be confused with a certified error bound for all parameters.

## Source boundary

Repository documentation was inspected at:

`b484725c893a7a9bde856151988996aef6965cb0`

The prior user-library report *Complex Transseries Reversion at q-Cusps* was
consulted in its fixed-parameter, jump-transport, and research-question sections.
It is distinguished from the repository snapshot in the bibliography. Public
primary sources were checked on 4 October 2026. The Fantini–Rella comparison is
to version 2 dated 1 April 2026, including formulas (60a)–(60b) and their stated
median convention.
