SHARPER LOCAL BOUNDS IN GOWERS'S PROOF OF SZEMEREDI'S THEOREM
Prepared for Vladimir Reshetnikov — 6 October 2026

CONTENTS

gowers_quantitative_refinements.pdf
    The complete article, with proofs, examples, quantitative comparisons,
    twelve research questions, a Lean interface map, and references.

gowers_quantitative_refinements.tex
    Complete editable manuscript source. No separate section files or
    bibliography database are needed. Its vector figure is included below.

figures/cube_refinements.pdf
    Vector comparison of the proved cube bounds and the exact two-frequency
    correction model. Used by the manuscript.

make_figures.py
    Optional figure regeneration script; requires NumPy and Matplotlib.

verify_refinements.py and verification_results.json
    Standard-library verification of graph energies, Boolean cube support
    counts, kernel inequalities, sharpness identities, and progression
    telescoping. Exact and floating-point checks are distinguished.

verify_selection.py and selection_verification.json
    Exact rational checks of the weighted-selection expectations, including
    repeated entries, rank-two bounds, and distinct unrespected tuples.
    These finite checks use a degree-one kernel and supplement the general
    proof; they do not replace it.

pattern_census.py and pattern_census.json
    Complete rational certificates for F1,F2,F3 = 1,2,10 and
    A1,A2,A3 = 2,6,38. Verification uses only the Python standard library.
    Generating fresh certificates additionally requires SciPy and NumPy.

source_manifest.json
    Repository snapshot, inspected file identifiers, and external references.

SHA256SUMS.txt
    SHA-256 checksums of the distributed files, excluding this checksum list.

BUILD THE ARTICLE

Run from the directory containing the extracted TeX source:

    latexmk -pdf -interaction=nonstopmode -halt-on-error \
      gowers_quantitative_refinements.tex

Alternatively run pdflatex three times:

    pdflatex -interaction=nonstopmode -halt-on-error \
      gowers_quantitative_refinements.tex

The article was built with pdfTeX from TeX Live 2023. It uses common packages:
amsmath, amssymb, amsthm, mathtools, lmodern, geometry, microtype, graphicx,
booktabs, tabularx, array, xcolor, enumitem, fancyhdr, hyperref, and bookmark.
No shell escape, external bibliography processor, or Python installation is
needed to rebuild the PDF using the supplied figure.

RUN THE SUPPLEMENTARY VERIFICATION

    python3 -S verify_refinements.py --output verification_results.json
    python3 -S verify_selection.py --report selection_verification.json
    python3 -S pattern_census.py --verify pattern_census.json

The -S flag demonstrates that verification does not require third-party
Python site packages. The first program includes exhaustive small graph
checks; its --skip-exhaustive option omits only that portion.

OPTIONAL REGENERATION

    python3 make_figures.py
    python3 pattern_census.py --generate pattern_census.json

The first command regenerates the PDF and PNG figure. The second command
uses a numerical solver only to propose certificates; every accepted
certificate is checked by exact rational arithmetic.

MAIN RESTRICTION RESULT

For d >= 2, let

    kappa_d = 1 / [2(400d)^d],
    Lambda_d = 2[1 + binomial(2d,2)](400d)^d.

If B is a subset of F_p, phi:B -> F_p respects at least
alpha |B|^(2d-1) additive 2d-tuples, and

    |B| >= Lambda_d (alpha eta)^(-2d),

then some B' subset B retains at least

    kappa_d alpha^(2d) eta^(2d-1) |B|^(2d-1)

additive 2d-tuples, with respected proportion at least 1/(1+eta).
The assumptions include p prime and 0 < alpha,eta <= 1.

For d=8, if the input respects at least gamma |B|^3 quadruples and
|B| = beta p, a convenient sufficient hypothesis and conclusion are

    p >= 2^102 gamma^(-112) eta^(-16) beta^(-1),
    retained count >= 2^(-95) gamma^112 eta^15 |B|^15.

STATUS AND SCOPE

The article proves local refinements of the specified estimates in Gowers's
paper and the inspected ProveIt transcription. It supplies equality and
sharpness examples where claimed. It does not assert worldwide priority
for every refinement or a new best global bound in Szemeredi's theorem.
No new Lean declarations were compiled or kernel checked in this project.
The existing repository was inspected but not modified.

Repository snapshot:
    327773149bd272239f1f6c0015f76d5097512c88

The original paper and full repository are not redistributed in this archive.
