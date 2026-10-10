JOINT REFLECTED LOG-GAMMA MOMENT TRANSITION

Baseline: ProveIt commit cc34f73596336f2466d9754cb0f3635bd2bedade.
Relevant source chapters examined:
  chapters/07-loggamma-moments.tex
  chapters/07-reflected-moments.tex
  chapters/07-sharp-moments.tex
  chapters/09-herglotz-jets.tex
The parent task also checked the six pinned incoming reports. No joint
reflected-moment transition was present in their abstracts/section lists.
No global bibliographic-priority claim is made.

MAIN PROVED RESULT
For t=(n+1)/(m+1), lambda=m*exp(-t) in a fixed compact positive interval,
normalize M[n,m] by gamma^m*n!/(m+1)^(n+1). The ratio equals
exp(delta*lambda) times a complete expansion in 1/m, with polynomial
coefficients in t,lambda and uniform error O((t/m)^(J+1)) after J terms.
delta = zeta(2)/(2*gamma)-gamma.
Explicit corrections through order 1/m^2 are supplied. The opposite
endpoint is exponentially negligible by a separate proven estimate.
Exact offset-residue polynomial identities and a finite coefficient
algorithm are also provided, including two all-order leading-degree
identities involving Touchard polynomials.

FILES
../../sections/04-joint-moments.tex
  Proof-complete chapter contribution; parent supplies theorem environments.
  Cites gaussian:ACEMKM (already in manuscript) and new key joint:DLMF.
verify_joint_moments.py
  Independent mpmath quadrature of the defining moment integral, centered
  and standardized in y=-log(x). Diagnostics are not interval certificates.
joint_moment_diagnostics.json
  80-digit diagnostics at 15 (n,m) pairs, three transition offsets;
  comparisons of two integration windows and first/second corrections.
derive_correction.py
  Exact SymPy derivation of corrections from centered gamma moments.
correction_symbolic.txt
  Output from that derivation.
verify_residue_polynomials.py
  Independent exact derivation of P1,P2 from offset residues. Also checks
  the first three offset polynomials directly for symbolic m.
symbolic_checks.txt
  PASS output of exact checks.
generate_transition_polynomials.py
  Finite exact coefficient algorithm at arbitrary user-selected order.
  Defaults to generic P0,...,P3; no divergent pole sum is evaluated.
transition_polynomials.json
  Generic P0,...,P3, as exact SymPy expressions and LaTeX.

REPLAY
python derive_correction.py
python verify_residue_polynomials.py
python generate_transition_polynomials.py --order 3
python verify_joint_moments.py
Dependencies: Python 3, sympy, mpmath.

BIBLIOGRAPHY
Existing key gaussian:ACEMKM:
T. Amdeberhan, M. W. Coffey, O. Espinosa, C. Koutschan,
D. V. Manna, V. H. Moll, Integrals of powers of loggamma,
Proceedings of the AMS 139 (2011), no. 2, 535--545.
https://doi.org/10.1090/S0002-9939-2010-10589-0
Author preprint: https://www.math.tulane.edu/~vhm/papers_html/lg-subm.pdf

New key joint:DLMF:
NIST Digital Library of Mathematical Functions, Chapter 5, section 5.7,
Series Expansions. https://dlmf.nist.gov/5.7
Accessed 2026-10-10.

EVIDENCE BOUNDARY
The asymptotic results and coefficient identities are proved analytically
and algebraically in ../../sections/04-joint-moments.tex. Numerical quadrature
corroborates these results and is not asserted to be an interval certificate.
The compact-lambda condition is explicit. The proportional interior-saddle
regime on compact positive exponent ratios is proved separately in
../../sections/04b-proportional-moments.tex, using the exact certificate
certify_gamma_saddle.py. Uniform bridges between the two regimes, moving
transition parameters, and sharp truncation with growing m remain open.
