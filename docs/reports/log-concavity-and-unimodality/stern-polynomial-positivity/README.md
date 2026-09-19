# A sum-of-squares proof of Ulas's real-zero conjecture

This archive contains a self-contained mathematical research note and
reproducible checks for a particular family of Stern polynomials.

## Main result and status

Let B_0(t)=0, B_1(t)=1, B_(2m)(t)=t B_m(t), and
B_(2m+1)(t)=B_m(t)+B_(m+1)(t). Set

    a_n = (4^n - 1)/3
    h_n = 2*(4^n - 1)*(2*4^n + 1)/3 + 1
    A_n(t) = B_(a_n)(t)
    W_n(t) = B_(h_n)(t).

The note proves, for every integer n >= 0 and real t,

    W_n(t) = (A_(n+1)(t) - t*A_n(t)/2)^2
             + 3*t^2*A_n(t)^2/4 > 0.

The target is Conjecture 4.4 in Maciej Ulas's
arXiv:1909.10844v1 (24 September 2019). The adjacent-polynomial quadratic
identity used in the proof was already present in that source; it is not
claimed as a newly discovered identity. An independent derivation is given.

Targeted searches did not identify a later resolution. The final journal
PDF was not accessible through the available subscription route. Therefore
this archive does NOT certify that the conjecture remained open in the
final publication, or that this is the first proof. It does provide a full
proof of the precisely stated assertion and several consequences.
The note has not been externally peer-reviewed or formalized in Lean.

Further proved results include:

* All complex zeros of W_n lie strictly to the left of Re(t)=-1/4, with an
  explicit n-dependent disk enclosure.
* The ordinary generating function in n is rational.
* If 2n+1=3^r*v, with 3 not dividing v, then W_n reduced modulo 3 has
  degree 3^r*(v-1) and is monic. In particular W_n == 1 (mod 3) exactly
  when 2n+1 is a power of 3.
* W_((3^r-1)/2) is irreducible over Q for every r >= 1, by reciprocal
  Eisenstein at 3. The forward congruence was already a result of Ulas.
* Explicit asymptotics construct conjugate root pairs whose real parts
  grow quadratically in n and imaginary parts linearly in n.

## Files

- `stern_conjecture_note.pdf`: the 14-page paper, with full proofs.
- `stern_conjecture_note.tex`: complete LaTeX source; references are embedded.
- `code/verify_exact.py`: standard-library-only exact verifier.
- `code/numerical_checks.py`: optional high-precision and spectral diagnostics.
- `results/exact_verification.json`: all check counts, sample coefficients,
  Eisenstein cases, and Sturm counts.
- `results/exact_verification.txt`: human-readable exact-run summary.
- `results/root_asymptotics.csv`: high-precision numerical root data.
- `results/numerical_verification.json` and `.txt`: numerical diagnostic log.
- `figures/root_geometry.pdf` and `.png`: the prebuilt numerical illustration.
- `requirements-optional.txt`: tested optional package versions.
- `Makefile` and `build.sh`: convenience build commands.
- `VALIDATION.md`: scope of the checks performed before delivery.

## Reproduce exact checks

Python 3.10 or newer is sufficient; the recorded run used Python 3.13.5.
Run these commands from the extracted archive directory:

    python3 code/verify_exact.py

No packages need to be installed for this step. Expected result: PASS,
6,722 exact checks with the default settings. Integer polynomial arithmetic
checks every n from 0 through 160. Separate Eisenstein cases extend through
n=364 (degree 728); exact rational Sturm counts cover n=1,...,12.
The primary evaluator uses binary Stern-index transitions independently
of the special-family recurrence being tested.

The default run takes only a few seconds in the environment used to create
this archive; runtime is machine-dependent. For a larger finite audit:

    python3 code/verify_exact.py --max-n 250 --sturm-n 15 --out results/extended.json

The finite checks do not replace the universal proofs in the paper.

## Build the PDF

A TeX installation with pdfLaTeX, newpx, amsmath/amsthm, tcolorbox, xurl,
microtype, and the other packages listed in the source is required.

    pdflatex -interaction=nonstopmode -halt-on-error stern_conjecture_note.tex
    pdflatex -interaction=nonstopmode -halt-on-error stern_conjecture_note.tex

The figure PDF is already included, so this does not need Python numerical
packages. Alternatively run `sh build.sh` or `make pdf`.
No font files are distributed in this archive.

## Optional numerical illustrations

The tested optional package versions are recorded in requirements-optional.txt.
Install them in a virtual environment using your normal package workflow, then:

    python3 code/numerical_checks.py

This uses 80 decimal digits for the sine-equation solves and checks the
result with a separate Chebyshev polynomial recurrence. The matrix tests
use floating-point eigenvalues. These are diagnostics, NOT interval
certificates and NOT a proof of zero exclusion.

The scripts themselves make no network requests. They write only the local
output files specified by their command-line arguments. The main theorem
and exact verifier are independent of all optional numerical calculations.
