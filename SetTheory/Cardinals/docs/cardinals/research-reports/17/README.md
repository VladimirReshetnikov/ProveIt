# Thin sections and simultaneous saturation

A research continuation of the two manuscripts in `Cardinals2.zip`, prepared
for Vladimir Reshetnikov on 18 September 2026.

## Contents

- `Thin_Sections_and_Saturation.pdf`: the complete typeset report.
- `Thin_Sections_and_Saturation.tex`: the self-contained LaTeX source.
- `build.sh`: a three-pass PDF build for Unix-like systems.
- `build.ps1`: the equivalent PowerShell build.

## Principal theorem

Let lambda be ultraexacting. Let D_lambda consist of the cofinal subsets of
lambda of order type omega, and let Q_lambda be its quotient by finite
symmetric difference. There are at least lambda classes q in Q_lambda such
that, simultaneously for every T subset D_lambda ordinal-definable from
finitely many parameters in V_lambda and finitely many arbitrary ordinals,

    |T intersect q| is either 0 or lambda.

The same classes work for ALL low-rank parameters. No hypothesis
V_lambda subset HOD is needed for this theorem. The key technical steps are
uniform bounded-rank correctness of ordinal definability and an internally
available, embedding-fixed bijection from lambda onto V_lambda.

The report also proves the small-family extension (individual sections need
not be definable; fiber sizes need not have a uniform bound), a preserved
thin-predicate obstruction, a bounded-rank separation theorem under ordinary
exactingness, and an I0-equiconsistency refinement. Both the fiber-cardinality
cutoff and the simultaneous parameter-rank cutoff are sharp in the specified
senses. The exact statements, qualifications, and proofs are in the PDF.

## Build

Install a LaTeX distribution with the packages named in the source preamble,
including newpxtext, newpxmath, tcolorbox, microtype, and hyperref. A full
TeX Live distribution supplies them. The default pdfLaTeX engine is used;
no external bibliography processor or shell escape is needed.

Unix-like systems:

    ./build.sh

PowerShell, from this directory:

    pwsh -File ./build.ps1

Or run this command three times:

    pdflatex -interaction=nonstopmode -halt-on-error Thin_Sections_and_Saturation.tex

The report uses the supplied manuscripts' font packages, dimensions,
forest/olive/sage colors, headings, and callout treatment. No font files
are included.

## Mathematical and verification status

The results are presented as conventional proofs, not as machine-checked
formalizations. They have not been independently refereed. The manuscript
identifies the improvements relative to the supplied reports but does not
claim worldwide priority.

The high-critical-point witness characterization, local Kunen inconsistency,
and the I0/ultraexacting consistency comparison and preservation/coding theorem
are external inputs. The fixed-code construction is credited to the
corresponding preserved-wellordering device in the cited primary literature.
The new thin-section and saturation implications are proved in full.
The I0 comparison itself is not claimed as new.

The PDF was compiled successfully in three passes with no LaTeX warnings,
undefined references, or overfull boxes in the final log. Every page was
rendered and inspected. Successful typesetting and visual inspection are
not mathematical proof verification.
