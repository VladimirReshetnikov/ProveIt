DOMINANT SINGULARITIES, SHARP EULER EXTREMA,
AND LAMBERT POLYNOMIAL ZEROS

A rigorous continuation of the ProveIt polylogarithm and harmonic-order programs
Prepared for Vladimir Reshetnikov — October 10, 2026

START HERE
==========

article.pdf is the complete research article. article.tex is its consolidated
LaTeX source. main.tex and sections/ provide the equivalent modular source.
The five figures are supplied in both vector PDF and raster PNG formats.
The ZIP is intended to be extracted with its directory structure intact.

The source comparison is pinned to ProveIt revision
4c173c06cc32c9cea554b39be1837ad2ae897fc1
(2026-10-10 19:07:31 UTC). It includes the manuscript, the harmonic-order
continuation, and all six incoming archives present at that revision.

RESULTS AND THEIR SCOPE
======================

1. The global normalized Euler optimum C_N eventually equals its a=0 axis
   maximum, with a unique optimizing inner order. The conjectured sharp law
   C_N = 1 + c N^(-p) + O(N^(-p-delta)) is proved over the full positive-order
   domain. The positive-quadrant supremum is not attained there. A joint
   boundary profile gives the exact sqrt(pi) loss and an if-and-only-if
   characterization of asymptotically near-optimal parameter sequences.

2. A second fractional Euler scale and its first inverse-logarithmic
   correction are derived from a positive gamma-transition remainder.
   The next exponent is mu = 1.969590414470..., with an explicit positive
   gamma-function amplitude. The large inverse-log coefficient explains an
   exceptionally slow approach to this finer asymptotic regime.

3. The attained axis maximum is unique and nondegenerate at every integer
   index. Its continuous envelope is strictly log-convex. Global axis
   reduction is proved only eventually; the all-index question remains open.

4. Every global pointwise-kernel maximizer converges to the same interior
   scaled limit. The value M_infinity = 1.053861930362711626... differs from
   the order-averaged limit C_N -> 1. The optimum has a convergent expansion
   in 1/N, with eventual uniqueness and strict decrease.

5. At N=2, the pointwise kernel has a unique interior maximum M_2, satisfying
   an irreducible degree-seven polynomial. An exact rational/finite-field
   verifier certifies the elimination and a 40-decimal rational enclosure.
   This theorem does not itself prove the separate inequality M_3 < M_2.

6. For every A>1, an exact barrier selects the analytic inverse of
   exp(U)=A+tU and its two accessible dominant square-root singularities.
   The repository's conditional diagonal-velocity asymptotics become
   unconditional, with arbitrary-order additive expansions, bounded sign
   gaps, a complete rational/irrational density alternative, convergent
   identities, and a critical finite-part identity.

7. The positive roots of Cohen's Lambert polynomials have an explicit
   limiting distribution, parametrized by
   L = 1-theta*cot(theta)+log(theta/sin(theta)),  0<theta<pi.
   Their limiting CDF is theta/pi.

8. The fixed-positive-parameter real-root, strict-interlacing, and
   extreme-root assertions discussed in Cohen's Conjecture 7.1 are proved
   in the scope stated in Section 14. For fixed positive integers j,k,
   the j-th largest root has an expansion to every fixed order in 1/n.
   The coefficient of n^(-m) is a polynomial in k-1 of exact degree m-1.
   Its coefficients belong to Q[zeta(2),...,zeta(2m+1)].

   In particular, the largest root has the expansion

   X_(n,k,1) = n+k-1+log(n)+gamma + C_0/n + C_1(k)/n^2 + O_k(n^-3),

   C_0 = -3/2-zeta(2)-zeta(3),
   C_1(k) = (k-1)(zeta(2)+zeta(3)) + zeta(2)^2-zeta(2)zeta(3)
            +2zeta(3)+3zeta(5)-1/12.

   No convergence of the all-orders Lambert expansion or uniformity in
   growing j,k is claimed. The nonpositive generalized parameter cases
   are outside this theorem.

9. The smallest positive roots have a Bessel limit. For fixed positive
   j,k, n^2 times the j-th smallest root tends to z_(k,j)^2/2, where
   z_(k,j) is the j-th positive zero of J_k. For k=j=1 the constant is
   7.3409853210619466286....

10. Section 18 proposes further work and an explicitly conjectural indexed
    bulk-phase formula. The conjecture is not a premise of any theorem.

ATTRIBUTION AND AUDIT
=====================

The inverse-series coefficient array and convergence-radius formula have
antecedents in Kalugin–Jeffrey, arXiv:1208.0754. The article provides an
independent selected-sheet proof and further consequences, and credits the
antecedent explicitly. The polynomials are identified with Cohen's Lambert
polynomials, arXiv:2012.11698v2. His MathOverflow normalization with n+H_n
has a first correction differing by 1/2 from the log(n)+gamma normalization.

The pinned incoming reports already establish the sharp all-order,
all-truncation universal Euler constant, the S_2 and S_4 reductions, and
the radial double-extremum phenomenon. These are not claimed as new here.
The S_6 reduction remains open.

integration/PROPOSED_CHANGES.txt identifies source paths, theorem labels,
scope, and suggested status updates. integration/notation-cleanup.patch
proposes only two confirmed notation fixes in the canonical manuscript.
No remote repository changes were made.

integration/INDEPENDENT_REVIEW.txt records separate internal mathematical
reviews of the principal proofs. These are not external peer review or
Lean formalization. The article gives ordinary mathematical proofs;
the scripts serve the separate roles described below. The targeted
literature comparison is not an exhaustive claim of worldwide priority.

BUILD THE ARTICLE
=================

Requirements: Python 3.11 or newer, a standard LaTeX installation with
latexmk/pdflatex and the packages used in preamble.tex. A full TeX Live
installation suffices. The supplied figures allow compilation without
installing the Python numerical packages.

From the extracted package directory:

    python3 code/assemble_article.py
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The modular alternative is:

    latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

Edit the modules, then reassemble. Regeneration replaces article.tex and
main.tex. Compiling either entry point should produce the same article.

REPLAY THE CHECKS
================

Install the tested Python packages if needed:

    python3 -m pip install -r requirements.txt

The default replay is short and writes to a separate reproduction/ folder:

    python3 code/reproduce.py

It runs four finite verifiers. The first two use only the standard library:

    python3 code/verify_kernel_algebra.py /tmp/kernel_algebra.json
    python3 code/verify_cohen_c1.py /tmp/cohen_c1_certificate.json
    python3 code/verify_diagonal_inverse.py --output /tmp/diagonal_checks.json
    python3 code/verify_cohen_edges.py --output /tmp/cohen_edge_checks.json

The last uses SymPy for an exact symbolic cancellation. All assertions in
these four default runs are finite exact checks; none certifies the full
analytic-continuation or asymptotic arguments by computation.

To replay the high-precision numerical diagnostics and exact bulk-root
isolation, then render figures from the new data:

    python3 code/reproduce.py --numerical --figures

To add the normalized transition quadratures through N=10^(1000000):

    python3 code/reproduce.py --numerical --transition --figures

The numerical options are substantially slower than the default finite
checks. They require mpmath and, for figures, NumPy and Matplotlib. They
never form an array of length 10^(1000000). Use --output-dir PATH to choose
another reproduction directory. Supplied data/ and figures/ are preserved.

To rebuild just the figures from the supplied data:

    python3 code/reproduce.py --figures

Direct make_figures.py accepts --data-dir, --output-dir and --samples-output.
Its defaults regenerate the supplied figures/ and data/figure_samples.json.
All scripts use local files and require no network or repository write access.

DATA AND NOTATION
=================

data/kernel_algebra.json                 Exact N=2 elimination and intervals
data/cohen_c1_certificate.json           Exact largest-root coefficient algebra
data/diagonal_checks.json                Exact identities and 360-digit diagnostics
data/cohen_edge_checks.json              Exact normalization and 45 root diagnostics
data/kernel_diagnostics.json             85-digit stationary-kernel calculations
data/axis_large_n_diagnostics.json       65-digit gamma quadrature through N=10^8
data/transition_remainder_diagnostics.json 75-digit normalized gamma quadrature
data/bulk_root_examples.json             Exact rational isolation, n=12,30,60
data/figure_samples.json                 Plot samples and conjecture diagnostics

The algebra verifier retains the local coordinate name p used in its
development. Its p2 field equals r_2 in the article. The article's exponent
p in the Euler asymptotic is unrelated. D_0 is the second Euler amplitude;
A>1 is reserved for the harmonic lattice parameter. Working precision
is not a certified number of correct digits for floating-point diagnostics.

PROVENANCE AND VERIFICATION RECORDS
===================================

provenance/repository_sources.json lists 86 retrieved files, verifies their
Git blob hashes against the pinned tree, and also records SHA-256 hashes.
provenance/primary_sources.json gives the primary literature URLs and roles.
provenance/finite_verification_receipt.json records the final exact replay.
provenance/document_verification.json records PDF compilation and visual QA.
MANIFEST.sha256 identifies every delivered file except the manifest itself.

The final package contains no original incoming ZIPs or copied full
repository: those are identified through hashes and pinned source links.
LaTeX auxiliary files, temporary renderings, caches, and experiment drafts
are excluded. All requested research, proofs, open questions, and relevant
reproducibility artifacts are included in the article and accompanying files.
