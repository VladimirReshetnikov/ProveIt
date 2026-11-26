BEYOND DIRICHLET GRH
Validated transfers, a sharper density certificate, and a concrete Hecke target
Prepared for Vladimir Reshetnikov, 25 November 2026 (Pacific time)

START HERE
Read report.pdf. The complete editable manuscript is report.tex together
with sections/*.tex and references.tex.

MAIN RESULTS AND ATTRIBUTION
1. The earlier ProveIt polynomial-density report's counterexample to
   Asada et al. Conjecture 6.3 was independently rechecked. It works for
   every prime power and for UPPER density with POLYNOMIAL ratios.
   This is inherited work, not a new discovery in this session.
2. This report improves the explicit binary guarantee to
       beta_2 > m_2 + 2^(-2^476).
   It uses the same 74-point witness and prime-degree cutoff 480.
   The coefficient-search cutoff is improved by a variance argument.
3. A factorial kernel-moment hierarchy is derived from the Lean proof's
   positive-type Fourier argument and a prior ordered-frame extension.
   No worldwide novelty claim is made.
4. A precise conditional route is supplied for the conductor-23 Hecke
   L-function of eta(z) eta(23z). The needed arithmetic inequality is
   NOT proved. Selmer quantifiers and nonvanishing assumptions are explicit.

REPRODUCE
  bash run_checks.sh
uses Python 3 standard library only and no network. The mathematical
proofs for all parameters are in the PDF, not established by finite tests.

  bash build.sh
uses latexmk/pdflatex and standard TeX packages. It writes temporary
files into build/ and copies the resulting PDF to report.pdf.

ARTIFACTS
code/                    Three independent exact verification programs
data/                    Actual JSON/CSV results and prior-audit records
sources/prior_archives.csv
                         Pinned inventory of 39 earlier ProveIt archives
sources/lean_source_map.csv
                         Paths and hashes of five selected source snapshots
sources/lean_snapshots/   Reference snapshots, NOT a complete Lean project
sources/density_review.txt
                         Independent paper-proof and cutoff review
sources/prior_work_review.txt
                         Prior-result map and limits
formalization_plan.txt   Proposed Lean theorem decomposition
SHA256SUMS.txt           SHA-256 digests of shipped files except itself

SOURCE PINS
lsernau/grh-lean:
  72fead102f663d5c7a407964a13dc0cf9d977207
VladimirReshetnikov/ProveIt:
  7af2d6e471b198372a2825f502c44c0de8ef4415

VERIFICATION LIMITS
The original Lean project was not rebuilt in this session. New mathematical
deductions have human proofs and finite checks, not completed Lean proofs.
The report distinguishes existing mathematics, inherited ProveIt results,
additional derivations, and conditional research targets.

LICENSE / SOURCE ATTRIBUTION
The upstream Lean snapshots retain their Apache-2.0 license; see
sources/APACHE_LICENSE.txt and sources/UPSTREAM_NOTICE.txt.
The 74-point set is inherited from ProveIt's weighted density report and
ultimately from Gavin Theobald's record in J. Wroblewski's database.
Its exact entries and midpoint property are checked independently.
