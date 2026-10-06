REPORT 118
Inversion sequence asymptotics from iterated kernels
Rigorous asymptotics and counting index inverses
2 October 2026

START HERE

Read report118.pdf. The complete editable mathematical source is
report118.tex. The report proves the leading asymptotic laws stated
numerically for classes 214 and 1509 in Britt and Beaton, Completing the
enumeration of inversion sequences avoiding triples of relations,
arXiv:2512.21943v3 (29 September 2026), and establishes every fixed
algebraic correction and a counting-index inverse theorem.

The sequences are ordinary counts of inversion sequences, indexed from
n=0. A279544 forbids e_j >= e_k and e_i >= e_k for i<j<k; A279567 forbids
e_j >= e_k and e_i > e_k. Their growth constants are respectively 4 and
3+2*sqrt(2), with exponent -3/2. The first two relative correction
constants and the leading amplitudes have exact outward interval
certificates. Numerical amplitude values were already recorded by
Vaclav Kotesovec in both OEIS entries in 2021; the report supplies proofs
and certificates, not a claim to have discovered those digits.

The first model uses a convergent forward Mobius-orbit sum. The second
uses a backward sum and a quotient, requiring a uniform proof that its
denominator does not vanish. Global continuation and positive critical
derivatives are established before coefficient transfer. The local
square-root expansions converge, whereas the coefficient expansions
are proved to every fixed order; no convergence of the inverse-power
series as its order increases is asserted.

The inverse takes a target count to the least index meeting that target.
Its leading real approximation uses the W_-1 branch of Lambert W.
Rigorously shrinking two-ceiling brackets preserve the possible
ambiguity near exact integer thresholds. The inverse error constants
and starting thresholds are existential: this is not an effective
certified finite-target inverse routine. The report does not establish
nonalgebraicity or non-D-finiteness, all exponentially small sectors,
literature priority, or external peer review.

FILES

report118.tex                  Standalone mathematical source
report118.pdf                  Rendered report
build.py                       Two clean byte-identical PDF builds
build-environment.txt          Tested Python and PDF toolchain
pack.py                        Deterministic verified ZIP generation
integrity.py                   Closed outer SHA-256 inventory check
CHECKSUMS.sha256                Closed package inventory
checks/                        Independent exact checks and fixtures
checks/MANIFEST.json            Closed inner checker inventory
test_integrity.py              Negative tests for outer inventory
verification_results.json      Successful checker validation summary

The package contains no source-paper PDFs, private research notes,
rendering intermediates, or private machine-specific source paths.

DEPENDENCIES

All exact checks, schema and integrity checks, and negative tests need
only Python 3.10+ standard library; tested with Python 3.12. No network
or installation is needed.

PDF build: pdfTeX/pdflatex and the standard LaTeX packages geometry,
fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, booktabs, microtype,
hyperref and enumitem. Tested with pdfTeX 1.40.26.

The build creates its TeX format in an isolated temporary directory.
Different TeX/font versions may produce different PDF bytes without
changing the mathematics. ZIP byte identity likewise assumes the same
Python/zlib compression toolchain. A fresh-directory replay is not a
newly provisioned operating system. No script installs software or
accesses the network.

CHECK THE RECEIVED PACKAGE

Run from the report118 directory after extracting the ZIP:

  python3 -B integrity.py .
  python3 -B checks/check.py
  python3 -B -O checks/check.py
  python3 -B checks/validate_bundle.py --output /tmp/report118-checks.json
  python3 -B test_integrity.py

Use -B to prevent Python from adding bytecode-cache files to the closed
package. Put new validation outputs outside the extracted package.
Do not use integrity.py --write when validating a received package: it
replaces the inventory and is intended only for deliberate repackaging.
The inventory rejects missing, changed and unexpected files. Checksums
are modification detectors, not authenticated signatures.

The exact checker distinguishes 29 external posted prefix terms for
A279544 and 26 for A279567 from the 81 coefficients n=0,...,80 generated
internally for each class. Independent state dynamic programming and
orbit-series reconstruction agree at every one of those 81 indices for
both models. Brute force over the original inversion-sequence definition
independently agrees for n=0,...,8 in each class.

Exact certificates include the normal-convergence majorants used in
the displayed analytic tails; the critical derivative recurrences;
Machin arctangent intervals and integer square roots; rational local
jets and outward Cauchy-error widening; the class-1509 global nonzero
denominator bound; gamma-ratio coefficient recurrences; and symbolic
checks of the first inverse corrections. Every executable guard remains
active under Python -O. The mathematical arguments proving infinite
convergence and continuation appear in the report; finite checking does
not replace them.

The checker README specifies its closed fixture schema and full
mutation scope. The final successful campaign individually mutates all
312 fixture leaves and runs 369 named negative cases in both normal and
optimized modes, totaling 738 negative subprocesses. Every failure must
match its expected diagnostic. Full baseline outputs agree between
normal and optimized modes and after fresh-directory replay; source
hashes remain unchanged. validate_bundle.py repeats this campaign.
test_integrity.py adds ten named outer-inventory mutations in normal
and optimized modes (20 negative runs), all in fresh temporary folders.

REBUILD THE PDF

  python3 -B build.py
  python3 -B integrity.py .

The build fixes timestamps and metadata, compiles three passes in each
of two independent temporary directories, rejects overfull boxes and
unresolved references, and requires the two PDFs to be byte-identical.
It writes report118.pdf without changing report118.tex. Every page of
the final PDF was rendered and visually checked for clipping, overlap,
legibility and broken references.

RECREATE THE ZIP

  python3 -B pack.py /tmp/report118-reproducibility.zip

The output must be outside the package. The archive script first checks
the complete inventory, then writes sorted files under report118/ with
fixed timestamps and modes. The delivered archive was freshly extracted,
its PDF rebuilt, its checks replayed, and its ZIP reproduced byte for
byte in the tested toolchain.

SOURCES

Primary paper: https://arxiv.org/html/2512.21943v3
Sequence definitions and previously posted numerical amplitudes:
https://oeis.org/A279544 and https://oeis.org/A279567
Full mathematical references are given in report118.pdf and report118.tex.
