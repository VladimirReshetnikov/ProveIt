LEXICOGRAPHIC ORDERS OF WELL-ORDERINGS OF THE SURREAL NUMBERS
Set Approximations, Class Orders, and Higher-Order Structure
3 October 2026

CONTENTS

surreal_well_orders.pdf      Complete article, with proofs and bibliography.
surreal_well_orders.tex      Standalone LaTeX source; all sections are included.
repository_audit.md          Targeted source audit and immutable repository links.
finite_checks.py            Reproducible finite comparison and encoding checks.
finite_checks_results.txt   Recorded output of the finite checks.
README.txt                  This file.

BUILD

With a conventional TeX Live or MiKTeX installation and latexmk, run:

    latexmk -pdf surreal_well_orders.tex

Alternatively, run pdflatex repeatedly until references stabilize.
The bibliography is built into the source; BibTeX and Biber are unnecessary.
No external graphics or additional TeX source files are required.
The source uses standard packages, including amsmath, amsthm, mathtools,
lmodern, geometry, microtype, booktabs, longtable, enumitem, listings,
hyperref, and cleveref.

To run the optional finite checks with Python 3:

    python3 finite_checks.py

SCOPE AND VERIFICATION

The report separates ordinary set orders, classes of set-length words,
set-like global class well-orders, and unrestricted global class well-orders.
Each theorem records its foundational setting. Higher-order notation does
not silently assert the existence of a class whose members are classes.

The mathematical proofs underwent a separate proof review. The standalone
source was compiled and the resulting PDF was rendered for visual inspection.
The finite checks detect mistakes in finite encodings and comparisons; they
do not verify transfinite proofs, cardinal arithmetic, or class comprehension.
No new Lean formalization is claimed, and no Lean build was performed.
No bibliographic-priority claim is made for constructions proved in the report.
Research questions are proposed directions, not a certified list of published
open problems.

REPOSITORY BASIS

https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: ae7c1e6aae3dc58c9c638b35646865ad6c10387d
Commit timestamp: 2026-10-03 01:03:53 UTC

The audit is targeted. Repository-wide correctness was not assessed.
The repository was not modified. Original repository files are not bundled;
the article and audit provide immutable source links and declaration names.
