BEYOND DIRICHLET GRH: EXACT TORSION SPECIALIZATION AND THE LIMITS OF TRANSFER
Research memorandum for Vladimir Reshetnikov
25 November 2026

START HERE
report.pdf is the complete illustrated report. report.tex and sections/*.tex
contain its editable LaTeX source, including the complete mathematical proofs.

MAIN RESULT
For p prime, rho>0, B>=0, h0>=1, and
  1/((p-1)*p^(h0-1)) <= rho,
an integral polynomial or bounded integral formal power series F of
positive-radius Gauss valuation G_rho(F)<=B has a p-power torsion tuple
with v(F)<=G_rho(F), where each coordinate has order p^h and
  h0 <= h <= H0 = h0 + ceil(p^h0 * B * (h0+B+2)).
The same bound works in every finite number of variables. A product gives
an exact AGGREGATE valuation bound for a packet. Two explicit obstructions
rule out uniform exact individual bounds and an exact moving-Gauss target.
This is a complete paper proof, with finite exact-arithmetic checks.
No new Lean formalization or full upstream rebuild is claimed.
Novelty is relative to the 26 inspected prior archives, not a worldwide
priority certification or a claim to resolve a named major conjecture.

CONTENTS
report.tex                 Main LaTeX source and package list
sections/*.tex             Assessment, source architecture, theorem/proof,
                           applications, targets, verification, corpus, references
checks/verify_exact_torsion.py
                           Main exact-arithmetic checker (standard library)
checks/referee_exact_shell.py
                           Separately written checker (standard library)
checks/compare_bounds.py    Exact comparison table and illustrative figure
checks/*results.json and checks/exact_torsion_checks.json
                           Recorded successful finite-check outputs
data/                      Exact comparison table in CSV and LaTeX
figures/                   Standalone bound comparison in PDF and PNG
evidence/source_manifest.json
                           18 inspected source-file identities and hashes
evidence/prior_inventory.json
                           All 26 predecessor archive identities and hashes
evidence/prior_review.txt   Targeted prior-corpus review and attribution
evidence/proof_review.txt   Independent mathematical proof review
evidence/literature_comparison.txt
                           Bounded primary-literature comparison
evidence/k_theory_transfer_audit.txt
                           Detailed original-versus-shortened source audit
build.sh                   Rebuild checks, figure, and PDF
SHA256SUMS.txt              Checksums for the packaged files (except itself)

REPRODUCIBILITY
Run from this directory:
  python3 checks/verify_exact_torsion.py
  python3 checks/referee_exact_shell.py
  python3 checks/compare_bounds.py
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
Or run: bash build.sh

The first two checkers need only Python 3's standard library. The figure
script additionally uses NumPy and Matplotlib. Use a standard TeX Live or
MiKTeX installation with latexmk and the packages named in report.tex.
The included outputs and figure allow reading or compiling without rerunning
Python. Checksums describe the delivered versions; rebuilding may change
PDF metadata and therefore checksums without changing mathematics.

SCOPE OF VERIFICATION
The supplied tests are finite consistency checks of the paper proof.
They do not prove the universal theorem by exhaustive search, certify a
full Lean dependency graph, or validate all prior archive computations.
The source review was pinned to:
  lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207
  VladimirReshetnikov/ProveIt@6fe2c1bd450aa7f19eab17fb9a6e76170b4fce00
Original archive comparison:
  CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4

The source endpoint is RH and GRH for Dirichlet L-functions. Other Dedekind
or automorphic instances require their own arithmetic construction.
The K-theory discussion reports and carefully qualifies recent preprints;
it supplies neither a new K124 vanishing certificate nor a Vandiver proof.

All third-party source locations are cited in the report and evidence.
The full upstream repositories and the 26 prior ZIPs are not duplicated.
