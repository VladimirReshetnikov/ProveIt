# Canonical Prikry cores at ultraexacting cardinals

Research continuation of the user-supplied Cardinals3 archive.
Prepared 18 September 2026.

## Contents

- `Ultraexacting_Prikry_Cores.tex`: self-contained LaTeX source, including bibliography.
- `Ultraexacting_Prikry_Cores.pdf`: compiled 23-page report.
- `build.sh`: three-pass pdfLaTeX build script.

## Principal result

For a suitable critical-sequence class q modulo finite symmetric difference at an
ultraexacting cardinal lambda, the tail filter on the subsets of lambda in
HOD_{ {q} } belongs to that inner model and is a normal measure there. Every
representative of q is Prikry-generic over that core and yields the same extension.
An additional fixed bijection b: lambda -> V_lambda produces a core with exactly
the ambient sets of rank below lambda. When V_lambda is already contained in HOD,
the extra parameter b is unnecessary for rank agreement.

The original HOD model allowing arbitrary V_lambda parameters also contains the
restricted internal normal measure (with ZF, without a claim of Choice).

The report proves the definability and reflection interface, ultrafilterhood,
internal completeness, normality, the needed Mathias criterion, finite-modification
invariance, and the main assembly. It also gives a successor-shift example where
the core remains the same but the canonical tail measure is non-normal.

The final consistency comparison is a structural strengthening of the existing
I0/ultraexacting equiconsistency. The published ABGL comparison and coding theorem
are explicit external inputs, not claimed as new proofs. The report also proves
an incompatibility with the explicitly defined cofinal definable-splitting
principle DS(lambda).

## Scope

Completeness and measurability of the canonical measures are INTERNAL to their
parameter-HOD cores. In the ambient universe, lambda has cofinality omega and these
measures fail external countable completeness. The report does not assert that
ultraexacting cardinals are inconsistent, that the ambient universe is the Prikry
extension of the core, or that lambda is measurable in ordinary HOD.

These are conventional English research proofs. No new Lean formalization or
compilation is claimed, and the mathematical arguments have not been independently
refereed. Novelty is relative to the supplied synthesis; literature-wide priority
has not been established.

## Building

Use a TeX Live or equivalent installation containing `newpxtext`, `newpxmath`,
`tcolorbox`, `xurl`, and the other standard packages named in the preamble.
No separate bibliography processor is required.

    sh build.sh

Alternatively run:

    pdflatex -interaction=nonstopmode -halt-on-error Ultraexacting_Prikry_Cores.tex

three times. The final build was checked for undefined references and citations,
LaTeX warnings, and overfull boxes; the rendered pages were inspected. No font
files, third-party article PDFs, or supplied reference files are included.
