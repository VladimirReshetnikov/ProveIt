CONVEX CONTAINERS FOR EVERY UNIT-LENGTH SPACE CURVE
Research report, 19 November 2026
Prepared for Vladimir Reshetnikov

MAIN ANSWER

The exact minimum is not known. For compact convex bodies and proper
rotations plus translations, this report proves

    3/220 <= V_3 <= pi/54

or approximately

    0.013636363636... <= V_3 <= 0.058177641733....

It also proves that the infimum is attained. The exact minimizing body
is not identified. Curves are continuous rectifiable paths, of total
length one; endpoints need not coincide. Containment includes boundary.
For length L, the minimum scales by L^3.

The upper-bound body is explicitly

    x^2 + y^2 + 36 z^2 <= 1,
    x >= 0,
    |y| <= (2-sqrt(3)) x.

It is an ellipsoid intersected with a 30-degree dihedral wedge.
The proof uses the published alternating-support theorem of Wienholtz
as established by Ghomi, and Panraksa-Wichiramala's planar sector theorem.

The lower bound uses a unit segment and a four-edge unit curve through
the five integer points

    (3,0,0), (0,3,2), (-3,0,4), (0,-3,6), (3,0,8),

after scaling by 1/(4 sqrt(22)). The minimum area of an orthogonal
projection of its convex hull is exactly 9/220. A concave-fiber argument
then forces container volume at least (9/220)/3.

RECENT PREPRINT DEPENDENCY

The report separately explains a stronger upper bound
0.054740497155799... obtained by applying its lifting theorem to a
September 2026 planar-cover preprint. The source's covering certificates
were not independently replayed; its area calculation was checked
exactly. The pi/54 upper bound does not depend on this preprint.

CONTENTS

report.pdf                       Compiled 15-page mathematical report.
report.tex                       Main LaTeX source.
sections/*.tex                   All component source files.
references.bib                   Bibliography with source URLs.
code/verify_lower_bound.py        Exact standard-library certificate.
code/reproduce.py                 Rebuilds figures, constants, and data.
data/bounds.json                  High-precision values and status labels.
data/keller_quadrilateral.json    Exact preprint quadrilateral and area.
data/lower_bound_verification.txt Actual output of the exact checker.
data/sector_cover.json            Explicit geometric description.
figures/*.pdf                    Vector figures used in the report.
figures/*.png                    Raster previews of the same figures.
VALIDATION.txt                    Verification scope and build checks.
SHA256SUMS.txt                    Checksums of the included project files.
Makefile                         Reproduction/build commands.
requirements.txt                 Python plotting dependencies.

QUICK CHECK -- NO THIRD-PARTY PYTHON PACKAGES NEEDED

    python3 code/verify_lower_bound.py

The certificate must print "Exact certificate: PASS". It uses only
integers and fractions for every calculation relevant to the lower
bound. The global reduction to fifteen candidate directions is proved
in the report; it is not inferred from numerical sampling.

REGENERATE FIGURES AND DATA

    python3 -m pip install -r requirements.txt
    make reproduce

BUILD THE PDF

Use a normally initialized TeX Live or MiKTeX installation with pdfLaTeX,
latexmk, BibTeX, Latin Modern, natbib, and the packages loaded by report.tex.

    make

The PDF and all figures are already included. Building is optional.
The build directory is temporary and is not included in this archive.

SCOPE

The calculations support bounds, not an exact solution. No priority or
best-known claim is made for the bounds deduced in this report.
The PDF explains all external dependencies and distinguishes exact
finite verification from illustrative numerical plotting. Third-party
papers and third-party proof repositories are cited rather than bundled.
