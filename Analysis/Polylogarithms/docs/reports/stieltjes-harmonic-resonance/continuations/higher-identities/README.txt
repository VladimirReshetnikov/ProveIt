HIGHER HARMONIC RECONSTRUCTION AND EXACT COLLISION IDENTITIES
Research continuation for Vladimir Reshetnikov's ProveIt project
12 October 2026

START HERE

Higher_Identities.pdf is the complete article.
Higher_Identities.tex is a standalone source: no local inputs are required.
Higher_Identities_modular.tex builds the same article from sections/.
INTEGRATION_NOTES.txt maps the new results to the existing project questions.

MAIN RESULTS

1. Arbitrarily many polygamma factors have an explicit, uniform local
   collision correction for all positive shift paths. The kernel is one
   Hermite divided difference of z^d log z. The one-trigamma centered
   family has an all-N zeta coefficient formula. The uncentered triple
   has nonresonant constants zeta(3), 0, -zeta(3), in scale order; the
   resonant (epsilon^3, epsilon^2, epsilon) constant is also evaluated.

2. Any number of labelled mixed mass derivatives of the logarithmic
   simplex face reduce to a divided difference of a classical polylog.
   A finite colored depth-three dictionary evaluates every B^r,C,D face
   and gives its ordinary convergent Gamma spectral sum.

3. Every unequal even harmonic-tail pair with gap ten has the optimal
   first-q formal moment prefix. The proof combines an analytic tail
   b>=73728 with 73,722 exact nonzero determinant residues. A general
   bounded-size Green determinant describes every inverse coefficient
   whenever the boundary block is nonsingular; this is unconditional
   at gap ten.
   The (14,24) example includes all coefficients of the resulting
   ordinary convergent polygamma-product sum.

4. Classical Euler homotopy gives a nonrecursive formula for every
   compensator in the inherited Gamma normal hierarchy. Locally analytic
   infinite-jet normal and primitive series are proved, including their
   Gamma and all-index Stieltjes translation identities.

BUILD

With an ordinary TeX Live installation including latexmk, amsmath,
amsthm, mathtools, lmodern, geometry, booktabs, longtable, tabularx,
microtype, enumitem, xurl, fancyhdr and hyperref:

  latexmk -pdf -interaction=nonstopmode -halt-on-error Higher_Identities.tex

Alternatively run pdflatex three times. The bibliography is embedded;
BibTeX and network access are unnecessary.

VERIFICATION

Required for exact checks: Python 3.10 or newer, SymPy, and a C++17
compiler. The numerical checks also need mpmath. The generation
environment used Python 3.12, SymPy 1.14 and mpmath 1.3.

  python3 reproduce.py --exact
  python3 reproduce.py --numeric

The runner copies code to a temporary directory, preserving supplied
records. It captures logs and writes a receipt in checks/. Exact and
numerical checks can be requested together. No network access is used.

Individual commands, from the indicated code directory:

  code/gap_ten/:
    c++ -O3 -std=c++17 verify_gap_ten.cpp -o verify_gap_ten
    ./verify_gap_ten 73728 gap_ten_certificate.csv
    python3 verify_gap_ten_independent.py
    python3 create_gap_ten_example.py

  code/collisions/:
    python3 verify_exact_contacts.py
    python3 check_polygamma_contacts.py

  code/three_clusters/:
    python3 verify_three_clusters.py --dps 75 --output three_cluster_checks.json

  code/normal_forms/:
    python3 normal_forms.py
    python3 check_compensator_signs.py

Unlike the top-level runner, the individual scripts may regenerate their
neighboring records. Keep an original copy if comparing byte identities.

CONTENTS

  sections/                 Modular TeX, with pc:, tri:, gt:, hp: labels.
  code/gap_ten/              C++ certificate, independent Python checks,
                            all 73,722 residues and full example coefficients.
  code/collisions/           Exact contact checks and ordinary quadratures.
  code/three_clusters/       Exact harmonic checks and independent numerical
                            polylogarithm, integral and spectral comparisons.
  code/normal_forms/         Sparse rational normalizer and Euler homotopy.
  data/source_manifest.json Hashes of all retrieved incoming ZIPs and the
                            92 manuscript chapter snapshots.
  data/dependency_files.json Exact paths/hashes of the specific source
                            sections used by the proofs and status audit.
  checks/                   Reproduction logs and receipts.
  SHA256SUMS.txt             Integrity record for the delivered package.

PROOF STATUS AND SCOPE

The gap-ten finite interval is an exact computer-assisted proof, not a
floating-point test. Its recurrence, prime, denominators and transform
roots are checked explicitly. The independent verifier also compares
the original Bernoulli source matrices and factorial/sign normalization.

Numerical residuals in the other suites are diagnostics. The universal
statements have analytic or algebraic proofs in the article. The general
merged polygamma finite part is not always evaluated by the contact
theorem. Positive Stieltjes-index collisions with arbitrary factor count,
the unrestricted unequal-even-pair conjecture, Gaussian S6 and revised
S8, general arithmetic collapse of Gamma spectral sums, and sharp
canonical-series convergence domains remain open.

The methods of divided differences, finite-part integration and Euler
homotopy are classical and attributed. Novelty is assessed relative to
the retrieved project sources; no worldwide priority claim is made.
Historical source questions are preserved as provenance. The article
proposes a current status update and a verified README duplication cleanup.
No remote repository files have been modified or published.
