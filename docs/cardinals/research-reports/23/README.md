# Normal measures from critical-sequence tail classes
## A canonical Prikry layer at the ultraexacting boundary

Research continuation of the supplied `Cardinals3.zip`, dated 18 September 2026.

## Contents

- `Normal_Measures_and_Prikry_Layers.tex` — self-contained LaTeX source.
- `Normal_Measures_and_Prikry_Layers.pdf` — compiled 21-page report.
- `build.sh` — reproducible PDF build using an installed TeX distribution.

The bibliography is embedded in the TeX file; no separate BibTeX database is
needed. No font files, third-party papers, or copies of the supplied Lean
sources are included.

## Main results

Theorem 5.1 constructs, from an ultraexacting cardinal lambda, one critical-
sequence tail class q that works simultaneously for every parameter p in
V_lambda. The hereditary OD(q,p) inner model contains a canonical normal
measure on lambda. The new proof ingredient is eventual constancy of
relative-definable regressive functions along the actual critical sequence.

Theorem 6.3 identifies a Prikry-generic intermediate model inside the ambient
universe. It is independent of the representative of q. Corollary 6.5 gives
full agreement on V_lambda when V_lambda is contained in ambient HOD.

Theorem 8.2 gives an inconsistency with a pointwise relative-definable
splitting principle. Theorem 8.4 enhances the existing I0 equiconsistency
calibration by adding the canonical measure, Prikry layer, and low-rank
agreement. The existing ultraexacting/I0 comparison and coding theorem are
explicitly imported, not presented as new results.

Theorem 9.3 applies the archive's stationary-set obstruction to the new
canonical layer: a strongly-compact ambient universe must either collapse
its successor of lambda or destroy a specific stationary subset.

Proposition 7.1 shows why normality is a genuine extra conclusion: shifting
the critical-sequence entries to their successors gives the same relative
HOD model but a nonnormal tail ultrafilter. Appendix A supplies the classical
Prikry genericity and preservation proofs used in the report.

## Scope and verification

This is an unrefereed mathematical argument, with detailed English proofs.
It is not a claim of unconditional inconsistency of ultraexacting cardinals
or I0, and worldwide priority is not asserted. No new Lean formalization or
machine verification of the mathematical proofs is claimed.

The normal measure is complete inside the indicated relative-HOD model.
It is explicitly not countably complete in the ambient universe. The Prikry
layer is not assumed to be the whole universe, nor is an ambient quotient
forcing supplied.

The PDF was compiled successfully and all pages were rendered and visually
checked. The final LaTeX log has no overfull/underfull boxes, unresolved
references, or citation warnings.

## Build

Use a reasonably complete TeX Live or MiKTeX installation. The document uses
pdfLaTeX, `newpxtext` and `newpxmath` (Palatino-style text and mathematics),
`microtype`, `tcolorbox`, `titlesec`, `fancyhdr`, `hyperref`, and other packages
listed in its preamble. Its Forest/Olive/Sage/Pale palette and layout follow
the supplied synthesis report. Install dependencies through your TeX
installation's package manager; fonts are not redistributed here.

On a Unix-like system with a TeX distribution installed:

    sh build.sh

Or run the following command three times in this directory (also suitable
for a Windows terminal with MiKTeX/TeX Live on PATH):

    pdflatex -interaction=nonstopmode -halt-on-error Normal_Measures_and_Prikry_Layers.tex

A LaTeX editor configured for pdfLaTeX can also build the document. The shell
script keeps auxiliary files in a temporary directory and places the PDF
beside the source. It makes no network requests.
