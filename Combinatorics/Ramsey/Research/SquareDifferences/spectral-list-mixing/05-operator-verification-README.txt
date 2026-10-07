Finite verification

From the report directory run:

    python verification/check_bounds.py
    python verification/check_spectra.py

The script prints deterministic JSON and does not write files. Compare its
output with verification/results.json. It needs NumPy and the Python standard
library. Inputs use the fixed seed 20261007; output has no timestamps or paths.

The 64 product-kernel cases use nonuniform positive probability
measures on each coordinate. Normalized L2 operator matrices include the
square roots of both probability weights. Every edge count from 0 through 7
is covered. Heterogeneous sorted telescoping bounds are compared with all
permutations, including q=0, q=1 and a zero-error q=1 edge. The same kernels
are also tested with the common comparison constant 1/2.

Direct Paley-star matrices at primes 3, 7, 11 and degrees 1, 2, 3 are compared
with the exact analytic singular-value expression. The larger-prime scalar
checks evaluate that expression only, not a large field-label matrix.
The h=3, t=1 address check tests simplicity, absence of opposite edges,
reflection invariance and the designated directed cycle for every
nonterminal mark set. It does not construct a full reflection-positive law.

These are floating-point sanity checks. They do not establish the general
operator inequality, sharp asymptotic order, hierarchy positivity or global
induction theorem. Those assertions rest on the article's analytic proofs.
The tolerance is 2e-11. Significant digits in the output are rounded to 12;
minor numerical variation across NumPy or linear-algebra versions is possible.

The second script prints spectral and mixture checks. Compare its output
with verification/spectra_results.json. It needs NumPy and the standard
library. It explicitly constructs Paley matrices at primes 3, 5, 7, 13,
the full reflected-matching operators, the phase-corrected complex
negative eigenfunctions, and the diagonal repair. At primes 3 and 5,
it enumerates the four-label mixture for five weights, including the
degenerate weights 0 and 1, and checks every balanced reflection cut.
Its tolerance is 3e-11. Runtime version metadata and last floating-point
digits may differ across environments.

The optional make_figure.py script requires Matplotlib as well as NumPy.
It regenerates the included vector PDF from the exact displayed formulas.
The figure is illustrative analysis, not experimental evidence.
