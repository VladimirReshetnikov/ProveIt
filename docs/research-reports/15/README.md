# Orbit saturation at the ultraexacting frontier

Research continuation prepared on 18 September 2026 from the two reports in
`Cardinals2.zip`.

## Files

- `Orbit_Saturation.pdf`: the 19-page report, with detailed proofs and references.
- `Orbit_Saturation.tex`: the complete, standalone LaTeX source.
- `build.sh`: a clean three-pass pdfLaTeX build script.
- `README.md`: this guide.

## Principal results

For an ultraexacting cardinal lambda, let D_lambda be the cofinal subsets of
lambda of order type omega, modulo finite symmetric difference.

The main theorem proves that every family F of subsets of D_lambda, definable
from ordinal parameters and one parameter in V_lambda, with |F| < lambda,
admits lambda pairwise disjoint cofinal test sets a such that every intersection
T with the class [a], for T in F, has cardinality either zero or lambda.
The individual members T need not be definable or fixed by an embedding.

This rules out small definable families of thin partial sections whose union
meets every class, and in particular rules out definable complete sections
with all widths below lambda. Widths need not have a uniform bound.

The report also proves a preserved-parameter version over choiceless inner
models, an exclusion for thin strong-Icarus enrichments, a lower bound on
small definable sets containing a thin complete section, and an exact
classification and count of periodic quotient classes for one embedding.
A bounded/cofinal separation theory is calibrated at the known consistency
strength of I0 using explicitly cited external results.

## Status and dependencies

The arguments are conventional, unrefereed, and not machine-checked.
Novelty is asserted relative to the supplied reports, not as a worldwide
priority claim. No unconditional inconsistency of ultraexactingness, I0,
or an unspecified Icarus hypothesis is claimed.

The main proof imports local Kunen inconsistency and the published
high-critical-point characterization of ultraexactingness. The consistency
calibration additionally imports the known ultraexacting/I0 equiconsistency
and a preservation-and-HOD-coding forcing theorem. All new implications
are proved in the report; the imported theorems are labeled Inputs A-C.

## Building

A standard TeX Live or MiKTeX installation with pdfLaTeX and the packages
listed in the preamble is sufficient. In particular, the report uses
`newpxtext` and `newpxmath` to match the supplied typography. No font files
or external graphics are included or required alongside the source.

On a POSIX system:

    sh build.sh

On any system with pdfLaTeX, the following command may instead be run three
times in this directory:

    pdflatex -interaction=nonstopmode -halt-on-error Orbit_Saturation.tex

The bibliography is embedded in the source; BibTeX is not required.

## Delivery checks

The delivered PDF was compiled with pdfLaTeX, with no warnings or unresolved
references on the final pass. All pages were rendered for visual inspection,
and the source typography was compared with the supplied synthesis.
These are document-production checks, not formal verification of the proofs.
