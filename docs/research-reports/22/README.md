# Canonical tail measures and Prikry cores

A research continuation of the reports in Cardinals3.zip, prepared for Vladimir
Reshetnikov, 18 September 2026.

## Contents

- Canonical_Tail_Measures.pdf — the complete report, with detailed English proofs.
- Canonical_Tail_Measures.tex — self-contained LaTeX source and bibliography.
- PROOF_AUDIT.md — dependency map and scope of the mathematical claims.
- build.sh / build.ps1 — reproducible PDF builds on Unix-like systems / Windows.

## Principal conclusions

At an ultraexacting cardinal lambda, a suitably chosen critical sequence c has a
finite-change class q=[c] with the following properties:

1. Every subset of lambda ordinal definable from q and finitely many parameters
   in V_lambda either contains a tail of c or misses a tail of c.
2. The resulting tail filter is an internally normal, lambda-complete,
   nonprincipal ultrafilter in HOD_{ {q} }, and in HOD_{V_lambda union {q}}.
3. The sequence c is Prikry generic over HOD_{ {q} }. Every representative of q
   generates the same proper intermediate inner model HOD_{ {q} }[c].
4. The boundary condition V_lambda subset HOD makes that ground model contain
   the full ambient rank segment V_lambda.
5. The boundary theory enriched by these conclusions remains equiconsistent
   with ZFC + I0, using the published ultraexacting/I0 calibration as an input.

The report also proves an explicit pointwise definable-splitting obstruction and
constructs three mutually definable rigid quotient parameters giving the same
relative HOD but normal, nonnormal, and non-ultrafilter tail filters.

## Proof status

The report gives conventional mathematical proofs, not Lean formalizations.
The supplied Lean source was consulted as a reference, not compiled or extended.
No claim of independent peer review or publication priority is made. The results
are presented as a continuation beyond the supplied synthesis; the I0 consistency
calibration and basic witness dynamics remain explicit literature inputs.

In particular, internal completeness is NOT external countable completeness.
The report exhibits an external countable family of measure-one sets with empty
intersection. The intermediate Prikry model is NOT asserted to equal the whole
ambient universe.

## Build

Install a TeX distribution with pdfLaTeX and the packages named in the preamble,
including newpxtext, newpxmath, tcolorbox, titlesec, fancyhdr, hyperref, and xurl.
TeX Live or MiKTeX with the corresponding packages is suitable.

Run `./build.sh` or `./build.ps1`, or run the following command three times:

    pdflatex -interaction=nonstopmode -halt-on-error Canonical_Tail_Measures.tex

The scripts keep auxiliary files in `_build` and place the resulting PDF next to
the source. The source preserves the supplied synthesis's newpx text/math fonts,
page geometry, Forest/Olive/Sage/Pale colors, heading styles, and assessment boxes.
No font files are bundled.
