# Critical Euler Errors for Harmonic Polylogarithms

**Sharp constants, positive surplus kernels, and a drifting extremizer**  
Research continuation for Vladimir Reshetnikov's ProveIt programme.  
9 October 2026 (America/Los_Angeles).

## Read the article

- `article/critical_euler_transport.pdf`: complete research article.
- `article/critical_euler_transport.tex`: self-contained LaTeX source.

The article proves the incoming *Real-Order Threshold* report's Conjecture 12.3:
`a -> -2 Im F_(a,1-a)(i)` strictly decreases, and the optimal all-depth uniform
critical Euler constant is `pi/4 + log(2)/2`.

It also proves fixed-total-order comparisons at imaginary radii through sqrt(3),
a positive surplus-density identity, stronger harmonic/Hurwitz moment
inequalities, a zero-free difference factorization, an endpoint-uniform Euler
asymptotic, and a moving-maximizer law with a Stieltjes-constant correction.
Every maximizer satisfies

    1 - a_N = 1/ell - 2d/ell^3 + O(ell^-4),
    ell = log((log N)/2),
    d = gamma_1 + (gamma^2 + zeta(2))/2.

These are large-N statements, not accurate low-depth parameter predictions.
The exact finite-depth reversal `R_128(1/2) > R_128(1/4)` is separately certified.

## Replay

Run from any directory:

    python code/certify.py
    python code/symbolic_checks.py
    python code/diagnostics.py
    python code/build_article.py

Adjust the script paths when not in the package root. Scripts resolve data and
article paths relative to their own locations. The first command uses only
Python's standard library and independently checks all finite interval
calculations and integer-root inequalities. It uses the *proved prior* tail
bound `(1/a) 2^-K`; it does not depend on the new optimal constant. No numerical
polylogarithm oracle is used in the certificate.

The other computations require the optional packages in
`requirements-diagnostics.txt`. Building requires `pdflatex` and the LaTeX
packages declared in the source; it leaves only the PDF in `article/`.

The delivered `data/` is a record of actual runs. Replaying overwrites the
corresponding records. Use a copy to preserve the delivered evidence snapshot.
The optional SciPy Jacobi quadrature may emit an internal removable-singularity
warning on the critical beta parameter line; the recorded values are finite
and independently compared with Euler values. This is not used in certification.

## Evidence boundaries

The article contains the analytic proofs. `certify.py` proves finite enclosures
conditional only on the analytic tail theorem. The SymPy checks validate finite
algebra, not convergence or asymptotic uniformity. Quadrature and numerical
optimizer outputs are diagnostics, not certified global optima. Eventual
unimodality, the S6 arithmetic relation, subcritical angular uniqueness, and the
broader normalized-radius conjecture remain unresolved here. No global priority
or proof-assistant verification is claimed.

## Integration

Suggested destination:
`Analysis/Polylogarithms/docs/reports/critical-euler-transport/`.
See `integration/INTEGRATION.md` and the labelled manuscript fragment. No upstream
repository file or branch was modified in preparing this package. The inspected
revision and exact incoming-source identity are in `data/provenance.json`.
