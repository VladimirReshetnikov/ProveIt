SHARP WASSERSTEIN CONTACT ORDERS FOR FINITE UNIFORM FACTORS
Research manuscript prepared with OpenAI
October 2026

MAIN RESULT
For mu_q = Law(sum_{k>=0} q^k Z_k), with independent Z_k uniform on
[-1/2,1/2], prescribe sigma_D = convolution_i U_{B^{-d_i}}, where B>=2
is an integer, D=(d_1<=...<=d_s) is a finite multiset, and U_a has width a.

Exact factorability at q=1/B is equivalent to d_i >= i-1.
For a feasible profile with s>=2, the optimal W1 approximation error has
exact order |q-1/B|^e, with e=min_{i>=2}(d_i+2-i). The same exponent holds
in total variation. A singleton factor is exact for every q; an infeasible
profile has a positive gap at the resonance.

The article also proves an exact clipping identity for convolution
approximation, attainment by a compact remainder, Fourier derivative
obstructions of every order without original higher-moment hypotheses,
and a constructive upper bound for arbitrary summable uniform series.

FILES
article.tex                  Complete, self-contained LaTeX source.
article.pdf                  Compiled article.
code/verify_hall.py           Exact combinatorial and diameter checks.
code/verify_transport.py      Exact CDF clipping and coefficient checks.
code/fourier_diagnostics.py   High-precision Fourier diagnostics.
data/hall_verification.json  Recorded exact verification results.
data/transport_verification.json
                             Recorded clipping/coefficient results.
data/fourier_diagnostics.csv All 60 numerical samples.
data/fourier_summary.json    Numerical setup and selected results.
data/document_validation.json
                             Compilation and visual validation record.
SOURCE_NOTES.txt             Repository pin, source links, scope.
requirements.txt             Optional numerical dependency.
build.sh                     PDF build command.

REPRODUCE
From this directory:
  python3 code/verify_hall.py
  python3 code/verify_transport.py
  python3 code/fourier_diagnostics.py
  latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The first two programs require only the Python standard library.
The numerical program requires mpmath. Install with:
  python3 -m pip install -r requirements.txt
The PDF requires a standard TeX Live or MiKTeX setup and latexmk.
All references are inline in article.tex; no .bib file is needed.

STATUS AND LIMITS
This is a research manuscript with full English proofs. It is not peer
reviewed or proof-assistant verified. The finite checkers corroborate
arithmetic and boundary cases; they do not prove the infinite analytic
statements. The numerical product diagnostics are not interval certificates.
No optimal leading coefficient, growing-depth uniform estimate, or global
priority claim is asserted. Twelve further questions are included.

The paper extends two specifically inspected ProveIt research reports.
It does not claim to settle the full optimal approximation problem for
arbitrary infinite divisibility-ladder factors.
