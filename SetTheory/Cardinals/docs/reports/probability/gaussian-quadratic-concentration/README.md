SHARP GAUSSIAN QUADRATIC CONCENTRATION FROM SIGNED SPECTRAL MOMENTS
Research manuscript and reproducibility package -- 8 October 2026
Research draft with proofs and reproducible artifacts

WHAT THIS PACKAGE ESTABLISHES

For a nonzero real symmetric matrix A and standard Gaussian vector g,
write Q=g^T A g-tr(A), L=||A||op, v=tr(A^2),
s=tr(A^3)/(L v), and k=tr(A^4)/(L^2 v).

The principal theorem determines the best coefficient c(s) in

  P(Q >= t) <= exp[-c(s) min(t^2/v, t/L)],  t>0,

for every fixed real cubic spectral balance s in [-1,1]. Its formula is
c(s)=min(1/4,J_s(1)), with c(-1)=1/4; the manuscript defines the explicit
rate J_s and proves sharpness within every exact-s matrix class.
The transition is s=-0.705589538603... . At s=0 the coefficient is
0.188714038110..., compared with the established unrestricted coefficient
(1-log 2)/2=0.153426409720... . The fourth spectral moment gives a further
explicit exponential bound through a two-node Gauss--Radau envelope.

An exact example uses eigenvalues +1 (m copies) and -1/2 (8m copies).
It has s=0, k=1/2, v=3m and attains the fourth-moment envelope. At t=v,
the rate divided by v is J*=0.200474048491... . For m=2 ell, the true
probability is the exact rational number

  P_ell = 3^(-(9 ell-1)) sum_{j=0}^{ell-1}
          binom(9 ell-1,j) 2^(9 ell-1-j).

It satisfies

  P_ell = exp(-6 ell J*)/[3 sqrt(pi ell)]
          * [1-505/(864 ell)+O(ell^(-2))].

This is also a harmonic normal-mode energy contrast. Other applications
cover ordinary Gaussian trace estimates, diagonal-free subgaussian forms,
and random cuts in triangle-free graphs.

PRIOR ART AND SCOPE

The unrestricted coefficient, Gaussian determinant identity, classical
moment quadrature, and beta/binomial/Stirling tools are established work.
The proposed contribution is the complete information-dependent optimal
coefficient frontier and its proof, together with the explicit signed
four-moment refinement and its quantitative validation. The article
reports its literature audit and does not assert unconditional priority
over all unpublished or unlocated work. Optimality of the relaxed Radau
moment problem is distinguished from realizability by finite matrices.
The result improves constants and exponents; it does not change the
quadratic/linear asymptotic shape of Hanson--Wright concentration.

The supplied openai/math repository inspired retaining the full spectral
kernel before simplifying it. No interacting-model theorem from that
repository is assumed. The proofs are self-contained mathematical
arguments supported by computations, not a Lean or other formal proof.

QUICK START

Run these commands from the extracted research_package directory.
The delivered PDF and figures are ready to read without running anything.

  python -m pip install -r requirements.txt
  python code/reproduce.py
  python code/exact_certificates.py --k 1 2 5 10 20 50 100 200 500 > data/exact_sandwich_certificates.jsonl
  latexmk -pdf -interaction=nonstopmode -halt-on-error spectral_concentration.tex

An isolated Python environment is optional:

  python -m venv .venv

Activate it with "source .venv/bin/activate" on a POSIX shell, or
".venv\Scripts\activate" in Windows Command Prompt, before installing.
Package installation may require network access. Once dependencies are
installed, all reproduction and PDF generation run offline.

The Makefile provides equivalent targets:

  make all           Reproduce data, figures, and exact checks; build PDF.
  make verify        Reproduce data/figures and exact sandwich certificates.
  make reproduce     Run the full symbolic and numerical reproduction.
  make certificates  Regenerate the bundled exact sandwich JSONL records.
  make pdf           Rebuild the PDF using the existing figures.
  make clean         Remove LaTeX auxiliary files, preserving the PDF/data.

Override executables if needed, for example:

  make all PYTHON=python3 LATEXMK=latexmk

Python/library versions in the delivered verification_summary.json are
Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0, Matplotlib 3.10.8,
SymPy 1.14.0, and mpmath 1.3.0. The scientific libraries are also
pinned in requirements.txt. Python 3.12 is recommended for reproducing
this run. Other Python or dependency versions were not exhaustively tested.

PDF compilation requires latexmk and a LaTeX distribution with pdflatex,
Latin Modern, AMS packages, geometry, microtype, booktabs, tabularx,
enumitem, tcolorbox, graphicx, fancyhdr, and hyperref. The bibliography is
embedded in the .tex source; there is no separate BibTeX/Biber step.

EXACT CHECKS WITHOUT SCIENTIFIC PYTHON

The following commands require only Python's standard library:

  python code/exact_certificates.py
  python code/exact_certificates.py --k 1 5 20 100 500
  python code/exact_certificates.py --help

The script writes one JSON record per requested positive integer k.
Its CLI variable k is the integer replication parameter ell, NOT the
normalized fourth spectral moment k used in the article. The exact
numerator, denominator, and finite sandwich are computed with integers
and fractions. Logarithms and normalized rates in those same records
are floating-point summaries of the exact fractions. The script also
checks P_1=256/6561. Its default parameters are powers of two through 128;
the explicit --k command above reproduces the delivered nine-record file.

The main reproduction script takes no command-line options. It writes
outputs into data/ and figures/ relative to the package, independent of
the process's working directory. It regenerates five symbolic identity
checks, 1,309 CGF comparisons, 1,122 rate comparisons, 45 independent
optimizer checks, 20 high-precision kernel integrals, 34 boundary checks,
and the exact probabilities. Its spectral audit uses a fixed random seed;
it does not estimate rare-event probabilities by Monte Carlo.

USING THE REFERENCE MODULE

code/spectral_concentration.py uses only the standard library. Add code/
to Python's import path and import spectral_moments, sharp_constant,
signed_rate, radau_rate, two_sided_bound, or sample_count. For example:

  import sys
  sys.path.insert(0, "code")
  from spectral_concentration import spectral_moments, radau_rate
  m = spectral_moments([1.0] + [-0.5]*8)
  exponent = m.r * radau_rate(m.s, m.k, 1.0)
  print(exponent)  # approximately 0.601422145473, at t=v/L

Rate functions return normalized Chernoff exponents, which are multiplied
by r as in the example; they do not return exact tail probabilities.
The code is floating-point reference code, NOT outward-rounded interval
arithmetic. It clips moment infeasibilities within 1e-12 and handles
saddles that round to a singular endpoint. These practical safeguards do
not certify an evaluated bound against every floating-point rounding
error. Use exact/certified input moments and interval arithmetic if a
machine-certified numerical inequality is required. Numerical audits
check the implementation and do not replace the mathematical proofs.

ARTIFACT MANIFEST

  spectral_concentration.tex / .pdf
      Complete manuscript, proofs, applications, literature audit,
      bibliography, and proposed research program.
  README.txt, requirements.txt, Makefile
      Usage, tested dependencies, and build/reproduction commands.
  PROVENANCE.txt
      Source URLs, known ingredients, proposed contribution, and review scope.
  VALIDATION.txt, SHA256SUMS.txt
      Final validation record and integrity hashes of packaged files.
  code/spectral_concentration.py
      Signed and fourth-moment reference formulas and helper functions.
  code/reproduce.py
      Full tables, plots, symbolic identities, and numerical audits.
  code/exact_certificates.py
      Independent standard-library exact probability/sandwich checks.
  data/sharp_constants.csv
      Optimal coefficients and the transition parameter.
  data/heterogeneous_spectrum_comparison.csv
      Norm, cubic, fourth-moment, and full-spectrum exponent comparisons.
  data/exact_tail_comparison.csv
      Exact-example probabilities summarized as rates and prefactor ratios.
  data/exact_rational_certificates.json
      Exact integer numerators and denominators for nine replication sizes.
  data/exact_sandwich_certificates.jsonl
      Separate exact rational certificates and finite-sandwich checks.
  data/verification_summary.json
      Audit counts, numerical residuals, constants, and environment record.
  figures/sharp_constant_frontier.pdf / .png
      Optimal cubic-balance coefficient plot.
  figures/rate_and_exact_tail.pdf / .png
      Rate hierarchy and convergence of the exact rational example.

No proprietary input data, downloaded figure assets, or runtime web
services are needed. Regeneration may change PDF metadata and insignificant
floating-point digits; byte-identical output across environments is not
claimed. Source provenance and citations are given in the manuscript.
