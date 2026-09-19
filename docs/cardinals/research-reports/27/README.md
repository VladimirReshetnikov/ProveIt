# Normal measures hidden in critical-sequence quotients

A Prikry factorization of ultraexacting witnesses and two exact consistency calibrations.
Prepared for Vladimir Reshetnikov, 18 September 2026.

## Files

- `Normal_Traces_and_Prikry_Factorization.pdf`: the 20-page report.
- `Normal_Traces_and_Prikry_Factorization.tex`: complete LaTeX source, including references.
- `build.sh`: reproducible PDF build command.

## Main results

Theorem 1.2 constructs, at an ultraexacting cardinal lambda, a fixed rank-bijection b and a critical-sequence quotient q such that the eventual-containment trace is a normal measure in HOD_{ {b,q} }. It concentrates there on measurable cardinals below lambda. Every representative of q is Prikry-generic over this inner model, and finite changes of the representative give the same Prikry subextension.

Theorem 1.3 calibrates two precisely defined trace principles, NT and NT+ (Definition 1.1). NT is equiconsistent with a measurable cardinal. NT+ adds concentration on measurables and is equiconsistent with a cardinal of Mitchell order at least two. Section 6 proves the forcing realization using quotient-relative cone homogeneity.

Section 8 removes b under the boundary hypothesis V_lambda subset HOD and gives an enhanced I0-equiconsistent boundary package. Its I0 consistency bounds are inherited from the cited published work, not claimed as a new comparison.

## Scope and proof status

The measure is internal to the named HOD model. It is not an ambient countably complete measure on the singular cardinal lambda. Section 9 gives an explicit external countable intersection that fails and audits this distinction, the reflection requirements, the parameter convention, and the forcing argument.

The new results have conventional English proofs. They are not independently refereed or Lean-certified, and literature priority is not asserted. The supplied Lean material was used for reference; no Lean compilation or formalization of the new results is claimed. Standard background, particularly the rank form of Kunen's inconsistency, is explicitly identified rather than re-proved from ZFC.

## Building

Run `sh build.sh` from this directory, or run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
  Normal_Traces_and_Prikry_Factorization.tex
```

The document uses pdfLaTeX and standard TeX Live packages, including `newpxtext`, `newpxmath`, `tcolorbox`, `titlesec`, and `hyperref`. No BibTeX step is required. The font selections, page geometry, heading styles, and Forest/Olive/Sage/Pale palette follow the supplied synthesis. Font files are not bundled.

The PDF was compiled with pdfLaTeX and visually checked after rendering all 20 pages. The final LaTeX build has no overfull/underfull box warnings or unresolved references. The input archive is not modified or redistributed in this package.
