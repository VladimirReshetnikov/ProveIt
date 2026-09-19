# The measurable strength of cofinal-orbit rigidity

Research continuation IV, prepared for Vladimir Reshetnikov, 18 September 2026.

## Main result

The exact rigid-class assertion used in `Cardinals3.zip`, with the rank bounds stated in Definition 1.2 of this report, is equiconsistent over ZFC with the existence of one measurable cardinal. The same calibration applies to the assertion that the singular cardinal is regular in HOD with all lower-rank parameters, and to the package of lambda many rigid classes with pairwise disjoint representatives and a common relative hereditary model.

The upper bound uses ordinary Prikry forcing. Its cone isomorphisms preserve the finite-symmetric-difference class of the generic cofinal set, although they do not preserve a representative. The lower bound applies the classical Dodd–Jensen covering theorem.

The report also constructs the ordinal-coded Vopěnka algebra of a class q and proves that every a in q induces a generic filter G_a with

    HOD_{ {q} }[G_a] = HOD_{ {a} }.

This is a single weakly homogeneous algebra and a single extension for all representatives. Under rigidity the extension is proper and the algebra is atomless. Under the additional hypothesis V_lambda is contained in ambient HOD, it adds no bounded subsets of lambda while changing its cofinality to omega.

This calibrates a consequence of ultraexactingness, not ultraexactingness itself. It does not lower the consistency strength of the ultraexacting embedding axiom or resolve the I0 or cover-exacting questions.

## Files

- `Cofinal_Orbit_Consistency.pdf`: 18-page report with detailed English proofs, bibliography, and a proof/dependency audit.
- `Cofinal_Orbit_Consistency.tex`: standalone LaTeX source, with bibliography included directly.
- `build.sh` and `build.ps1`: optional build scripts for Unix-like systems and PowerShell.
- `SOURCE_AND_VERIFICATION_NOTES.md`: provenance, hypotheses, and verification boundaries.

## Building

Use a TeX Live or MiKTeX installation with pdfLaTeX, `newpxtext`, `newpxmath`, `microtype`, `tcolorbox`, `titlesec`, `fancyhdr`, `mathtools`, `tabularx`, `xurl`, and their standard dependencies. No bibliography processor or shell escape is needed.

Run `pdflatex -interaction=nonstopmode -halt-on-error Cofinal_Orbit_Consistency.tex` three times, or use the appropriate build script.

The source uses the same newpx text and mathematics fonts, page geometry, theorem styles, and Forest/Olive/Muted/Sage/Pale color palette as the supplied synthesis. Fonts are obtained from the TeX installation; no separate font files are included.

## Verification

The source was compiled successfully with pdfLaTeX; the final log had no undefined references, undefined citations, overfull boxes, or underfull boxes. All pages were rendered and the layout was checked. The proofs are mathematical arguments in English, not Lean formalizations. The Dodd–Jensen covering theorem is an explicitly imported classical theorem. The work is presented as an extension of the supplied dossier, without a global priority claim.
