EXACT STRUCTURE AND CERTIFIED COMPUTATION IN THE POLYLOGARITHM DRAFTS
==================================================================

Research continuation for VladimirReshetnikov/ProveIt
Prepared for Vladimir Reshetnikov with OpenAI assistance
Date: 2026-10-08 UTC

Reviewed source commit:
3a6d80ed618d839915deb0d19ab687f45e81d995

Repository directory:
https://github.com/VladimirReshetnikov/ProveIt/tree/3a6d80ed618d839915deb0d19ab687f45e81d995/Analysis/Polylogarithms/docs

START HERE
----------
article.pdf is the complete 46-page research article.
article.tex is its master LaTeX source; keep sections/, figures/, and
references.tex alongside it.
CORRECTIONS.txt is the source-specific correction register.

The principal results are:

1. An all-weight partial-fraction reduction of inverse-argument mixed double
   polylogarithms to the already present (z,1) family. Four advertised
   mixed-point survivors are explicitly evaluated in single-value data.

2. An exact formula for every odd-index alternating harmonic sum S_(2m+1),
   with a self-contained Mellin/beta proof, and a meromorphic generator
   with exact poles, residues, and removable singularities.

3. An arbitrary-prime-weight character normal form for rational-grid
   distributions. It proves the all-denominator formal rank laws and
   determines the coordinate defect at resonant finite jets.

4. A normalized local functional equation for every derivative bridge
   between reflected Dirichlet L-values, including trivial-zero
   regularization and the complex conjugation missing in an older report.

5. A spectral expansion for parameter derivatives of generalized Stieltjes
   constants, 78 exact rational enclosures, and a uniform two-term
   reciprocal-gamma asymptotic for n=O(log k), with a sign corollary.

6. A direct proof of the weight-two Eisenstein summation-order anomaly,
   all differentiated CM row evaluations, and explicit exponential tails.

The article includes twelve concrete further-research projects and a
detailed source audit. It distinguishes classical results and known
specializations from extensions relative to this corpus. It does not
claim a new transcendence or period-independence theorem, and it does not
claim worldwide priority for the classical mechanisms used in its proofs.

CONTENTS
--------
article.tex                         Master source
article.pdf                         Compiled article
references.tex                      Bibliography included by the master
sections/euler.tex                  Euler family and generators
sections/distribution.tex           Formal rank and resonant-jet proofs
sections/bridges.tex                All-order normalized L-function bridges
sections/asymptotics.tex            Spectral, rational, and uniform results
sections/modular.tex                Modular rows, order anomaly, CM jets
sections/research.tex               Reproducibility and further questions
sections/audit.tex                  Principal source corrections
CORRECTIONS.txt                     Expanded review register and locators
requirements.txt                   Versions used for verification
build.sh                           PDF rebuild command
code/verify_mixed_and_euler.py      Exact identities and numerical comparisons
code/verify_distributions_and_bridges.py
                                   Exact ranks and analytic bridge comparisons
code/parameter_asymptotics.py       Exact rational enclosures and profile figure
code/modular_rows.py                Rational rows, CM jets, and tail checks
data/*.json                        Recorded full verification runs
figures/derivative-profile.pdf      Vector figure used in the article
figures/derivative-profile.png      Figure preview
provenance/source-manifest.json     All 40 source files and verified hashes
verification-summary.json          Reproduction and validation summary
SHA256SUMS                         Hashes of all other package files

BUILD THE PDF
-------------
Use a recent TeX Live installation with latexmk and the ordinary LaTeX
packages loaded in article.tex. The supplied PDF was built with pdfTeX
1.40.25 (TeX Live 2023/Debian) and latexmk 4.83.

From this directory:

  sh build.sh

The equivalent command is:

  latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

No shell-escape option, network access, BibTeX pass, or external font
download is needed. The prebuilt vector figure is included, so rebuilding
the PDF does not require running Python first.

REPRODUCE THE COMPUTATIONS
-------------------------
Python 3.11 or later is recommended. The recorded run used Python 3.12.14.
Install the versions in requirements.txt in your preferred environment:

  python3 -m pip install -r requirements.txt

Run each script from this directory or by its absolute path:

  python3 code/verify_mixed_and_euler.py
  python3 code/verify_distributions_and_bridges.py
  python3 code/parameter_asymptotics.py
  python3 code/modular_rows.py

The first three scripts also accept --quick for smaller checks.
The modular script accepts --dps and --rows; its default run uses
90 decimal digits and 48 paired rows for each CM comparison.
parameter_asymptotics.py accepts --no-figure.
Every script writes its JSON result into data/ relative to its own file.
Running a quick check overwrites that script's result with a clearly
labelled quick-mode report; rerun without --quick to restore the full run.

INTERPRETING THE VERIFICATION
----------------------------
Exact algebra:
  64 rational partial-fraction checks;
  1,734 exact distribution/reflection matrix checks through q=60;
  72 independently generated rational coefficient comparisons;
  rational modular differential polynomials.

Exact enclosures:
  78 intervals for (-1)^(n+k) gamma_n^(k)(1)/(k! n!).
  Every center and endpoint is stored as an integer numerator and
  denominator. The analytic theorem proves the enclosure. In 72 of these
  cases, the lower endpoint is strictly positive and certifies the sign.
  The remaining six deliberately use n=k+1 and do not assert a sign.

Numerical comparisons:
  Independent integrals and zeta/polygamma representations check the mixed,
  Euler, bridge, spectral-tail, and modular formulas. These use ordinary
  high-precision mpmath, not directed interval arithmetic.
  A numerical residual is not an independence proof.

The analytic spectral bound in profile data is the difference between the
exact mathematical first spectral term and the exact normalized derivative.
It does not include floating-point roundoff or decimal serialization.
This distinction matters because some spectral bounds are far smaller
than the 40 printed digits of the numerical plot values.

The computations check normalization and implementation. The all-weight
and all-denominator conclusions depend on the proofs in the article,
not on extrapolation from the finite tables.

INTEGRATION NOTES
-----------------
The package can be placed in a dedicated subdirectory under
Analysis/Polylogarithms/docs. Preserve the relative structure when moving
the master source, or update its input and figure paths consistently.

CORRECTIONS.txt is intentionally separate from the new article. It gives
exact source filenames, line ranges, status, and replacement formulas.
It distinguishes newly established errors, gaps resolved by this paper,
warnings already noted in the repository README, and claims that remain
unproved. Apply proposed source edits after maintainer review.

The provenance manifest covers the eight article sources, 31 supporting
reports, and the Polylogarithms README. Every Git blob hash was verified
against the exact bytes retrieved at the pinned commit. SHA-256 hashes
are included as a second convenient integrity check.
The original drafts are not duplicated in this package. The audit of the
reports is focused, not exhaustive, and the package does not certify all
statements in the original directory.

No original source file was overwritten and no change was pushed to the
repository. The absent upstream evaluator stores were not reconstructed.

For attribution in an integrated version, retain the cited mathematical
sources and the explicit distinction between established prior results,
their applications here, and unresolved arithmetic conjectures.
