# Finitely Additive Kernels at Ultraexacting Cardinals

Research continuation of the two reports supplied in Cardinals3.zip.
Prepared 18 September 2026.

## Files

- `Finitely_Additive_Kernels.tex`: self-contained LaTeX source.
- `Finitely_Additive_Kernels.pdf`: compiled report with detailed English proofs.
- `build.sh`: reproducible pdfLaTeX build, using a temporary build directory.
- `README.md`: this file.

The typography follows the supplied synthesis: newpxtext/newpxmath,
letter paper, the same geometry, and the Forest/Olive/Muted/Sage/Pale palette.
No font files or original archive contents are redistributed.

## Principal results

1. Common null partitions. Under regularity of lambda in the relevant
   relative HOD, every nonempty definable family of fewer than lambda
   finitely additive laws on cofinal omega-sets has one countable
   partition null for every member. Each law has no nonzero nonnegative
   countably additive minorant, even when the minorant is not definable.

2. Positive kernels. A low-rank shift-invariant mean produces a
   representative-independent finitely additive kernel on every
   cofinal-mod-finite quotient class. Prefix-tail kernels and mixtures
   give sharp examples for the two separate coordinate-continuity defects.

3. Phase balance and conditional inconsistency. At an ultraexacting
   lambda, lambda many simultaneous test classes force every
   OD_(V_lambda union {q}) charge to have translation-invariant phase
   distribution. There is no nonempty finite OD_(V_lambda) family of
   ultrafilter-valued kernels. Equivalently, the displayed compact convex
   family permits a definable point selection but no definable
   extreme-point selection, even with finitely many unordered candidates.

4. Consistency calibration. The simultaneous ordinal-definable version,
   with V_lambda contained in HOD and lambda least exacting, is
   equiconsistent with I0 by applying the published ultraexacting
   equiconsistency and coding result. This does not improve the existing
   upper or lower bound for ultraexactingness itself.

## Status and scope

The report supplies conventional proofs of its new refinements and
identifies the imported large-cardinal theorems precisely. It is an
unrefereed research contribution, not a claim of literature priority or
of inconsistency of ultraexactingness, I0, ZFC, or the Axiom of Choice.
No Lean formalization or compilation of the supplied Lean files is
claimed. The source reports' orbit and parameter-elimination machinery
is rederived before being applied to charges.

The countably infinite *unordered* definable family of ultrafilters
question remains unresolved by these arguments. No countable-family
ultrafilter exclusion should be inferred from the finite-family theorem.

## Build

Install a standard TeX Live or MiKTeX distribution with pdfLaTeX and the
packages named in the preamble (including newpx, tcolorbox, titlesec,
fancyhdr, hyperref, and xurl). Then run:

    bash build.sh

Alternatively, run pdfLaTeX three times on the source. The bibliography
is included directly; BibTeX, external images, and network access are
not required. The build script leaves only the final PDF in this folder.
