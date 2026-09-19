FINITE CHOICE AT THE ULTRAEXACTING BOUNDARY
Research continuation prepared for Vladimir Reshetnikov
18 September 2026

CONTENTS
  Large_Cardinals_Finite_Choice_Continuation.tex
  Large_Cardinals_Finite_Choice_Continuation.pdf
  finite_orbit_check.py
  finite_checks.json
  README.txt

MAIN MATHEMATICAL RESULT
Let lambda be ultraexacting and let Q_lambda be the quotient modulo finite
symmetric difference of the cofinal subsets of lambda of order type omega.
For every 1 <= r < n < omega, there is no nonempty finite family, ordinal
definable with parameters in V_lambda, of functions choosing exactly r
members from each n-element subset of Q_lambda.

The proof preserves a family as a set, allows its members to be permuted,
and uses a critical-sequence cycle of length n*lcm(1,...,m), where m is the
family size. The finite permutation argument is fully proved in the paper.
It does not iterate an embedding on a domain that is not closed under it.

ADDITIONAL RESULTS
- An explicit selector-coded strong Icarus enrichment is inconsistent.
- The theory asserting an ultraexacting lambda, V_lambda contained in HOD,
  an ordinal-definable well-order on the bounded-countable quotient, and
  the above cofinal-quotient prohibition is equiconsistent with ZFC + I0.
  This last comparison is derived from existing ABGL consistency and
  preservation theorems, not a new reduction of the strength of I0.

STATUS
The paper gives conventional proofs of the stated deductions. The basic
even/odd cycle method is credited to an existing presentation in Goldberg's
2026 notes. Historical novelty of the finite-family formulation has not
been established. The manuscript is not a refutation of bare ultraexacting
cardinals, I0, a canonical sharp enrichment, or the other main open
large-cardinal assertions in the supplied report. No proof-assistant
verification of the set-theoretic argument was performed.

BUILD THE PAPER
Use a standard TeX Live installation with newpx, amsmath, amsthm,
mathtools, geometry, microtype, tcolorbox, booktabs, longtable, tabularx,
titlesec, fancyhdr, enumitem, needspace, xurl, and hyperref.

  latexmk -pdf -interaction=nonstopmode -halt-on-error \
    Large_Cardinals_Finite_Choice_Continuation.tex

Alternatively run pdflatex three times. No shell escape, network access,
external bibliography, image assets, or custom font files are required.

FINITE CHECKS
Requires Python 3.10 or later; standard library only.

  python finite_orbit_check.py --output finite_checks.json

The supplied output records successful checks of:
- 32,738 nonempty proper subsets of cycles of lengths 2 through 14;
- 91 sharp-period constructions;
- all binary selectors on cyclic sets of sizes 2 through 6; and
- 132 finite-exponent amplification cases.

These tests concern finite arithmetic and permutation actions. They do not
construct a model of ZFC, prove consistency, or machine-check the
large-cardinal proof. They are supplementary to the written proof.

PROVENANCE
This is a separate continuation of the user-supplied file
Large_Cardinals_Unified_Report.tex. Its Palatino-style newpx text and
mathematics, geometry, heading and theorem styles, and Forest/Olive/Sage
color palette were retained. The original source was left unchanged.
Primary mathematical sources and precise theorem locators appear in the
paper's bibliography. Font files are not distributed in this archive.
