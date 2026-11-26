BEYOND THE DIRICHLET GRH ENDPOINT
=================================
Research analysis prepared for Vladimir Reshetnikov
Assessment date: 25 November 2026 (America/Los_Angeles)

START HERE
----------
Open report.pdf. Its editable source is report.tex plus the files in sections/.
The report contains complete proofs and a bibliography, not merely proposals.

The archive's main results are:

1. A uniform torsion-selection theorem for arbitrary families of bounded
   power series over O_{C_p}, assuming a finite total witness-valuation budget.
   One finite grid, fixed before the family, gives total positive excess at
   most epsilon. Matrix inverses and normalized cokernel lengths are controlled.

2. A precise nonabelian A5 transfer criterion, with positive character detector
   W=(21,1,0,1,1), full inertia and prime-power coefficients, exact normalization,
   and an explicit splitting field of X^5+20X+16. A stated one-sided arithmetic
   prime-sum estimate would give RH for the degree-60 field and three subfields.
   That prime-sum estimate is NOT proved here.

3. A new intermediate genus-field certificate improving the exponent-six
   imaginary-quadratic exclusions in one prior report. In the remaining
   census window and with t>=7 ramified primes, the products P_j of the
   j smallest ramified rational primes must satisfy:
       P_(t-2)>1,200,000; P_(t-3)>75,000;
       P_(t-4)>850; P_(t-5)>14.
   This is a partial classification result, not the complete 432-field census.

4. A counterexample to one maximal-order, no-loss torsion rule with arbitrary
   ramified coefficients, and precise obstacles to direct BSD/Goldfeld/Selmer
   and Vandiver-type deductions.

SCOPE AND STATUS
----------------
The pinned upstream repository exports RH and GRH for Dirichlet L-functions,
including imprimitive characters. It does not export arbitrary nonabelian
Dedekind, Artin, or automorphic GRH.

Upstream commit:
  72fead102f663d5c7a407964a13dc0cf9d977207
  https://github.com/lsernau/grh-lean

Prior-report repository commit:
  a92443f00663b1b8b3c233d17df0ad49dc4f2b2c
  https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming

All five selected prior archives were inspected. Their SHA-256 digests, exact
sizes, Git blob hashes, internal report paths, and comparison notes are in
evidence/prior_reports_manifest.json.

The mathematical extensions in this report are written proofs, independently
cross-reviewed during the analysis. They are not newly Lean-verified theorems.
The upstream's formal checks are cited as external reports. No local full Lean
build, kernel replay, or fresh axiom check was run in this analysis.

The finite Python computations were executed. They check explicit group,
polynomial, rational, and valuation calculations. They do not verify the
infinite analytic statements, the published class-group census, or GRH.

Novelty is claimed only relative to the five inspected reports, not as a
determination of worldwide publication priority.

CONTENTS
--------
report.pdf                  Complete typeset research report.
report.tex                  Main LaTeX source.
sections/                   Included source sections and bibliography.
code/a5_detector.py         Exact A5/coset/local-factor/Galois certificate.
code/genus_certificate.py   Exact exclusion constants and example discriminant.
code/torsion_checks.py      Finite illustrative valuation and resultant checks.
code/source_audit.py        Limited static inventory of a full upstream clone.
code/reproduce.sh           Certificate and PDF reproduction driver.
data/                      Recorded JSON/CSV computational results.
evidence/                  Source/prior-report provenance and review notes.
evidence/upstream/          Selected unchanged upstream source and notices.
SHA256SUMS.txt              Digests of delivered files, excluding itself.

The excerpt in evidence/upstream is not a standalone Lean project. Original
Apache licenses and notices are preserved there. No third-party research
article PDFs or original prior-report ZIPs are redistributed.

REPRODUCE
---------
Run from the extracted archive root:

  bash code/reproduce.sh

To also repeat the static audit of a separately obtained full clone:

  bash code/reproduce.sh /absolute/path/to/grh-lean

The clone must be at the pinned commit for identical inventory results.

Dependencies:
  - Bash and Python 3
  - SymPy (tested with 1.14.0), only for torsion_checks.py
  - latexmk and pdflatex with standard LaTeX packages, for rebuilding the PDF
  - Git and a complete upstream clone, only for the optional source inventory

Python 3.12.14 was used for the delivered results. The A5 and genus programs
need only the standard library. Their decisive arithmetic is exact.
Illustrative decimals in JSON are not used to establish the inequalities.

To run only the exact certificates:

  python3 code/a5_detector.py
  python3 code/genus_certificate.py
  python3 code/torsion_checks.py

To build only the PDF:

  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

To check the delivered bytes on a system with GNU coreutils:

  sha256sum -c SHA256SUMS.txt

Rebuilding the PDF can change its byte hash because of TeX version and
timestamp metadata. The manifest describes the delivered files. It is not
a cryptographic attestation of mathematical correctness.

READING GUIDE
-------------
Results at a glance: completed deductions versus remaining inputs.
Sections 1-2: exact upstream scope, method, and prior-report comparison.
Section 3: bounded analytic torsion selection, proof, matrix corollaries,
           necessary hypotheses, and the elliptic Tate-module obstruction.
Section 4: explicit A5 nonabelian detector and conditional RH certificate.
Section 5: general intermediate genus-field theorem and numerical exclusions.
Section 6: maximal-order counterexample with its exact quantifier limit.
Section 7: research priorities and what is still needed for named conjectures.
Section 8: verification ledger and reproduction.
