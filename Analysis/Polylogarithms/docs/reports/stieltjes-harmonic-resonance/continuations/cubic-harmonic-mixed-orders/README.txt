CUBIC TORNHEIM DERIVATIVES AND HARMONIC STIELTJES CONSTANTS
Research continuation for the ProveIt project
11 October 2026 (UTC)

MAIN DELIVERABLES

Cubic_Tornheim_Harmonic_Stieltjes.pdf
    The complete 29-page article, including proofs, explicit examples,
    normalization and source-status notes, and 12 further research questions.

Cubic_Tornheim_Harmonic_Stieltjes.tex
    Complete standalone LaTeX source. It needs standard TeX packages only.
    No external images, bibliography database, or source sections are needed
    to compile this file.

article.tex, preamble.tex, references.tex, sections/
    The same article in modular form, for editing and repository integration.

integration/CLAIM_LEDGER.json
integration/INTEGRATION.txt
    Proposed claim status and integration guidance. No repository changes
    have been pushed or merged by this package.

provenance/repository_inventory.json
    Pinned source revision, all 80 manuscript chapter Git blob hashes, and
    the metadata and Git blob hashes of all 11 incoming archives checked.
    Metadata is retained as retrieved. Some browsing URLs contain "main";
    use the recorded full commit or immutable blob hashes for a replay.

verification/
    Portable Python scripts and their recorded JSON results.
    The results distinguish exact algebra, interval-certified evaluation,
    and ordinary high-precision numerical diagnostics.

SOURCE REVISION

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit:     5a790187c8e186e41e2b990b4941cb7a1a3c7b6b
Source roots:
    Analysis/Polylogarithms/docs/manuscript
    docs/incoming

MAIN RESULTS AND LIMITS

1. FP integral_0^1 psi(x)^3 dx = 3*zeta(2)-6*eta(1)-6*gamma*gamma_1.
   Here eta(1) is the coefficient of u in the strict double zeta
   Z2(1+u,1;1). The finite part is the cutoff constant in the coordinate x.
   A convergent harmonic series, a normalized complex primitive, and an
   all-order polygamma identity accompany the theorem.

2. Every admissible cubic Tornheim ray has an explicit formula in Omega3,
   kappa, zeta'''(0), log(2*pi)*zeta''(0), and zeta'''(-1). Omega3 reduces
   to eta(1) by result 1 and the earlier coincident spectral identity.
   The second coordinate has an independent convergent integral.
   Transverse curved paths require a precise fourth-jet correction.

3. Arbitrary mixtures of integer inner orders, with positive integer
   weights, reduce finitely to nested polylogarithms while retaining the
   full complex outer order. If q inner orders are positive and at least
   one is nonpositive, the guaranteed depth is at most q+1. Repeated poles,
   coincident colors, all outer-order derivatives, and Mellin principal
   parts are included.

The finite mixed-sign closure question (Q11 of the preceding coincident
directional report) is resolved. The asymmetric cubic question (Q2) has a
complete explicit spanning formula. The diagonal question (Q1) is reduced
to established harmonic Stieltjes data, with a convergent arithmetic series.
Finite ordinary-constant evaluations of eta(1) and kappa, their arithmetic
independence, and the Gaussian S6 / revised S8 conjectures remain open.
Specific novelty is claimed relative to the inspected repository corpus;
the report does not assert exhaustive worldwide priority.

BUILD THE PDF

From this directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error \
        Cubic_Tornheim_Harmonic_Stieltjes.tex

For modular editing, compile article.tex instead. To regenerate the
standalone file after editing the modular source:

    python3 build_standalone.py

The delivered PDF was compiled with pdfTeX 1.40.25 (TeX Live 2023/Debian)
and latexmk 4.83. Its final build has no unresolved references, LaTeX
warnings, or overfull/underfull boxes. All 29 pages were visually reviewed.

REPRODUCE THE MATHEMATICAL CHECKS

Python 3.12 was used. Tested package versions are in requirements.txt.
In an appropriate Python environment:

    python3 -m pip install -r requirements.txt
    python3 verification/verify_cubic_ray_algebra.py
    python3 verification/verify_mixed_reduction.py
    python3 verification/verify_local_coefficients.py
    python3 verification/verify_cubic_harmonic_bridge.py
    python3 verification/verify_cubic_rays_numeric.py
    python3 verification/evaluate_extra_coordinate.py

Each script writes its JSON next to itself. The generic symbolic curved
calculation is the slowest exact check and may take several minutes.

The exact suites comprise 760 checks:
    16 generic cubic/ray/curve identities;
    624 mixed-order coefficient and finite-antidifference checks;
    120 local Gamma/Mellin and finite harmonic algebra checks.

The Arb route certifies the digamma-cube scalar with an explicit Binet
tail bound; its stored displayed enclosure has radius 4.86e-62.
The independent quadratures and Mellin-series ray evaluations are
diagnostics, not interval certificates. Finite algebra checks do not
replace the analytic proofs of convergence and continuation in the article.
No proof-assistant formalization or external referee report is claimed.

The helper tornheim_mellin.py is adapted from verify_rays.py in the
preceding ProveIt coincident-directional report. It does not use the
new cube identity or a finite-part correlation formula to evaluate T.

INTEGRITY

package_manifest.json records the SHA-256 hash and size of each delivered
file except the manifest itself. Build logs, temporary renders, Python
bytecode, and copies of prior source archives are not included.
