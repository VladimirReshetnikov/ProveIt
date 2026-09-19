LARGE CARDINALS AT THE INCONSISTENCY FRONTIER
Local complete-definability barriers, finite symmetry,
and an I0-calibrated consistency result

Prepared for Vladimir Reshetnikov -- 18 September 2026

CONTENTS
  Large_Cardinals_Continuation.pdf   20-page research article
  Large_Cardinals_Continuation.tex   Complete, self-contained LaTeX source
  build.sh                          Rebuilds the PDF with pdfLaTeX
  finite_symmetry_checks.py          Standard-library finite algebra checks
  finite_checks.json                Results of the executed checks
  README.txt                        This file

MAIN RESULTS AND THEIR SCOPE

Theorem 4.3 proves that a gamma-cover-exacting cardinal lambda is regular
in HCD(gamma^+), using the stationary-cover and definability-transfer
interfaces in Goldberg's July 2026 lecture notes. HCD(eta) is the inner
model of sets hereditarily definable from eta-complete ultrafilters on
ordinals; completeness means closure under fewer than eta intersections.

Theorem 5.2 combines this with Goldberg's strongly compact covering
theorem. If delta < lambda <= gamma, delta is strongly compact, and lambda
is gamma-cover exacting, a cofinal subset of lambda of order type below
delta belongs to HCD(delta) but not to CD(gamma^+). Thus the local
stability principle in Definition 5.1 is incompatible with that
configuration (Corollary 5.3). The stability principle is an ADDITIONAL
hypothesis, not a proved consequence of strong compactness. A separate
small-forcing-ground formulation is proved in Section 6.

Theorem 8.2 gives a finite-permutation obstruction at an ultraexacting
cardinal. Its corollaries prohibit ordinal-definable fixed-size proper
selections from finite families of cofinal omega-subsets modulo finite
difference. Theorem 8.5 prohibits an ordinal-definable finite-valued
transversal. Ambient choice functions are not excluded.

Theorem 9.1 uses existing equiconsistency and forcing theorems to calibrate
these choice failures: they can coexist with an ultraexacting lambda,
V_lambda contained in HOD, and no smaller exacting cardinal, at the
consistency strength of I0. This is a derived calibration, not a new
separation of large-cardinal consistency strengths.

STATUS

This is a proof-oriented continuation of the supplied unified report.
The additions are beyond that report; historical publication priority
has not been established. Imported theorems, lecture-note interfaces,
and new deductions are distinguished in the article. No unconditional
refutation of bare cover exactingness, ultraexactingness, I0, or the
strongly compact/cover-exacting coexistence theory is claimed. The proofs
are conventional mathematical arguments, not machine-checked set theory.

REBUILDING THE PDF

Install a current TeX distribution with pdfLaTeX and the packages listed
in the source preamble. In particular, newpxtext and newpxmath provide
the report's typography; TeX Gyre Heros supplies the sans-serif text.
No font files are included in this archive.

On a POSIX system:
  sh build.sh

Alternatively, run the following command three times in this directory:
  pdflatex -interaction=nonstopmode -halt-on-error Large_Cardinals_Continuation.tex

The bibliography is included directly in the source: BibTeX, external
images, and network access are unnecessary. The layout, font packages,
Forest/Olive/Sage palette, theorem styling, and page geometry follow the
user-supplied report.

FINITE CHECKS

Run with Python 3.10 or later:
  python3 finite_symmetry_checks.py --output finite_checks.json

The actual included run checked 5,913 permutations through degree 7,
483,828 affine-index shift instances, 8,166 proper-subset nonfixed
instances, and 6 orientation actions. It also checked the S3 example
where every group element has a fixed point but there is no common fixed
point. All checks passed. These computations audit finite combinatorics;
they do not construct a model of set theory or verify infinitary proofs.
