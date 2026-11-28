# Research extensions of the ProveIt GRH article

Prepared for Vladimir Reshetnikov on 27 November 2026.

This archive contains two research papers with complete mathematical proofs,
editable LaTeX sources, reproducible verification code, figures, numerical and
exact-arithmetic outputs, a separate mathematical review, and source provenance.

## Start here

| Paper | Main result | Files |
|---|---|---|
| Spectral quantile transition | An explicit conditional large-deviation rate, a change in the active total-mass constraint, and a full rare-conditioned profile for regularly varying gamma spectra | spectral_quantile_transition/spectral_quantile_transition.pdf and .tex |
| Symplectic precision invariance | An optimal first-residue-digit test and exact total variation at every finite and full p-adic precision, for any number of source pairs with a sufficiently large complement | symplectic_precision/symplectic_precision.pdf and .tex |

The spectral theorem is unconditional for deterministic regularly varying
spectra. RH/Dirichlet GRH identifies its gamma sum with reciprocal completed
L-functions in the stated real-character or conjugation-closed setting.
The symplectic theorem is unconditional and transfers a different method from
the inspected article.

## What was analyzed

The repository snapshot is
[VladimirReshetnikov/ProveIt at 2e714ce3d8e33aa8160391cf5dd95f3af3c34045](https://github.com/VladimirReshetnikov/ProveIt/tree/2e714ce3d8e33aa8160391cf5dd95f3af3c34045/Analysis/GeneralizedRiemannHypothesis/).
Its consolidated article README describes 194 reports merged into 895 pages
with 1,200 numbered results. It explicitly describes the merge as distinct from
an independent review. The present work used the consolidated article and its
result inventory to select extensions, then examined the relevant arguments
and primary references. It does not claim an audit of all 1,200 results.

| Existing result or question | Extension in this archive |
|---|---|
| ana:thm:condlaw: typical conditional spectral profile and Gaussian fluctuations | Exact fixed-deviation quantile cost and full profile after the additional rare event |
| ana:thm:medianheight: median-height central-limit theorem with exact centering | A universal transition at c = 1.626121264897... and a rate whose first derivative is continuous but second derivative jumps |
| spn:sec:padic: one symplectic source pair at every precision | Arbitrarily many source pairs, provided the complement contains at least as many pairs as the source |
| spn:q:symplectic: multi-pair local densities, optimal tests, and precision persistence | The residual-Pfaffian test, a closed total-variation formula, and an explicit distinction between equal and unequal prior probabilities |

The novelty claim is limited to these extensions of the inspected corpus and
the exact combinations of conclusions proved here. Classical gamma tilting,
weighted-measure conditioning, alternating local densities, and finite-field
Fourier/counting methods are credited. A targeted literature check did not
identify the same combined theorems; worldwide priority has not been certified.

## Rebuild the PDFs

The PDFs are ready to read. Rebuilding requires Python 3 and a LaTeX installation
with pdflatex and the standard packages used by the sources. Bibliographies are
embedded in the TeX files, so no BibTeX run or network access is needed.

From the extracted archive directory:

    python3 build.py

The build script runs each source three times and writes TeX build byproducts under
each paper's build directory. It copies the resulting PDF back next to its TeX
source.

## Reproduce the calculations

Install the Python dependencies in an environment of your choice:

    python3 -m pip install -r requirements.txt
    python3 build.py --verify

Or run either verification script separately:

    python3 spectral_quantile_transition/code/verify.py
    python3 symplectic_precision/code/verify.py

The spectral script computes constants at 70 decimal digits, compares closed
integrals with numerical quadrature, checks the general integration-by-parts
identity and transition curvature, compares exact discrete product saddles
with continuum limits, and recreates both figures. These are numerical checks,
not certified intervals. The discrete saddle comparison is not an estimate of
the finite-saddle probability itself.

The symplectic script uses exact rational Fourier inversion and integer
enumeration. Its recorded run covers 13 Gram parameter sets and 11 compression
parameter sets, enumerating 1,863,252 Fourier characters and 407,106 observed
blocks. Every asserted comparison passed. This independently checks small
instances without using the Hall-polynomial density as the computational method.

The proofs establish the infinite and all-dimensional statements; computations
support the formulas and implementations. Neither new theorem has been
formalized in Lean. The separate review is another mathematical derivation and
check within this research session, not external journal peer review.

## Scope

The spectral theorem fixes the spectrum, gamma shape, quantile and cutoff.
It gives a logarithmic probability asymptotic and a limiting profile. It does
not provide finite-saddle error bounds, a probability prefactor, a critical
window law, or uniformity in growing conductor or degree. All randomness is in
the auxiliary gamma weights; the zero ordinates are deterministic.

The symplectic theorem concerns one block, independent Haar entries as the
alternative, and equal prior probabilities. Its dimension assumption is
c >= r. The paper proves that additional digits can improve unequal-prior
decisions, so first-digit optimality is not a claim of statistical sufficiency.
The theorem does not cover a smaller complement, degenerate frames, or an
arbitrary collection of correlated observations.

## Provenance and integrity

PROVENANCE.json records the pinned source files, reported Git blob identifiers,
local SHA-256 hashes of inspected article text, relevant theorem labels,
primary references, and the Python versions used. SHA256SUMS records the
delivered files. It can be checked with:

    sha256sum -c SHA256SUMS

Rebuilding may change PDF metadata or floating-point output formatting, so the
checksums describe the delivered files rather than promising byte-identical
outputs under every software version. Third-party research papers and the full
upstream article are cited rather than redistributed in this archive.
