EXACT RECONSTRUCTION AND HIGHER RESONANCES IN POLYGAMMA–ZETA CALCULUS
Research continuation prepared for ProveIt — 11 October 2026 (UTC)

START HERE

Read Polygamma_Reconstruction_and_Resonance.pdf for the complete article.
The file Polygamma_Reconstruction_and_Resonance.tex is a self-contained
single-file LaTeX version. The modular source is article.tex, sections/,
and references.tex. Both contain the same text and proofs.

This package is an additive research contribution for integration into
VladimirReshetnikov/ProveIt. Its source baseline is commit
446dca9bd65c20e409d1d2561d4ffad408103e2a. The baseline comprises the
canonical polylogarithm manuscript and the six incoming reports present
at that revision. No repository file was overwritten or submitted.

MAIN ADVANCEMENTS

1. All reconstruction rows for the pair of tail orders (2,2b).
   A finite factorial/Bernoulli formula constructs every entry of the
   inverse moment matrix, resolving the specified reconstruction target.
   It gives ordinary polynomial-subtracted polygamma series with a
   prescribed even-zeta value and exact polylogarithmic boundary operators.

2. A new infinite family in the optimal-prefix conjecture at p=8.
   For q=2b>8 and b not congruent to 1 modulo 16, the first q moments
   have full formal rank q. The proof combines an exact symbolic
   determinant certificate with a uniform doubled-Bernoulli congruence.
   The excluded residue class and general p>=10 remain unresolved.

3. Every regular odd centered moment of the cubic trigamma tail.
   An explicit finite Bernoulli formula places the entire family in
   Q + Q*zeta(2) + Q*zeta(3) + Q*zeta(4). The article gives rational
   and zeta(3) extraction series, an analytic exponential generator,
   and its finite expression using six depth-two polylogarithms.

4. The next two-particle Gamma-determinant resonance.
   Exact finite Pearson identities determine the hard-cutoff constant.
   A normally convergent grouped subtraction gives every spectral
   derivative, explicit generalized Stieltjes identities, parameter
   derivatives, and an anchored primitive through Hurwitz-zeta derivatives.
   The comparison with the spectral finite part includes both amplitude
   derivatives required at a double pole.

5. Ordinary spatial Mellin formulas for every residue coefficient.
   The shift difference of an arbitrary finite differential polynomial
   in the polygamma functions yields absolutely convergent logarithmic
   moments. The article specifies all higher-pole harmonic corrections,
   all scalar-filter Stieltjes terms, and the essential second-order
   endpoint constant. Concrete linear and nonlinear examples are evaluated.

SCOPE AND AUDIT

The article distinguishes new work relative to the inspected repository
from classical ingredients and existing source theorems. It does not
claim exhaustive historical priority or arithmetic independence of the
displayed formal coordinates. It does not prove the manuscript's short
Gaussian S6 or revised S8 conjectures.

No new counterexample to an inherited theorem was established in the
statements audited. The article records exact normalization requirements,
one corrected zeroth-power Faulhaber scope error in an early draft of
this contribution, and counterexamples to an unrestricted determinant
valuation extrapolation considered during this research. Those valuation
counterexamples do not refute the optimal-prefix conjecture.

Section 9 contains a claim-status table, integration recommendations,
verification evidence, and fourteen further research questions with
concrete missing mathematical steps.

BUILD

Install a normal TeX Live or MiKTeX distribution with the standard
packages listed in article.tex. No network access, external assets,
special fonts, or BibTeX run are needed to compile.

  python build.py

This regenerates the single-file TeX source and builds the modular source
with three pdflatex passes. Temporary build products go to .build/.

  python build.py --standalone

This instead compiles the regenerated single-file source. It writes the
same final PDF name. BUILD_REPORT.json records the source, engine, page
count, and final PDF checksum. Rebuilding may change PDF metadata and
therefore its checksum even when the mathematical content is unchanged.

REPLAY

Use Python 3.10 or later. The supplied results were produced with Python
3.12, SymPy 1.14.0, and mpmath 1.3.0. Install the two dependencies with:

  python -m pip install -r requirements.txt

Then run the independent programs in sequence:

  python verification/run_checks.py

Each program can also be run separately. They use no network and need
none of the original incoming archives. The rank-eight verifier reads
rank_eight_certificate.json, reconstructs its finite matrices, and checks
the full determinant identity coefficient by coefficient. Individual
programs write their JSON results beside the script; the wrapper saves
standard output in verification/replay_logs/.

The reconstruction tables contain all twenty rows for 2<=b<=6, as both
JSON and readable text. Their integer-scaled convention is stated in
the table header: sum[W*A2*A(2b)-R] = multiplier*zeta(2k).

Exact arithmetic checks and independent numerical diagnostics are kept
distinct. The latter are not interval certificates and do not substitute
for the analytic proofs. Their precision and truncation data are retained.

INTEGRATION ARTIFACTS

INTEGRATION_NOTES.txt  — destinations and status changes to consider.
CLAIM_STATUS.json      — machine-readable claims, proof labels, and scope.
SOURCES.json           — pinned repository paths and source hashes.
VERIFICATION_SUMMARY.json — concise replay and visual-review record.
MANIFEST.sha256        — SHA-256 checksums of the delivered package files.
verify_manifest.py     — standard-library-only integrity check.

The source archives are not duplicated in this package. New research
sections, exact certificates, coefficient tables, verification scripts,
the complete article, and its reproducible build are all included.
