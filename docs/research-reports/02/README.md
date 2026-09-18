# Cover exactingness, definability, and conditional inconsistency

Research follow-up prepared for Vladimir Reshetnikov, 18 September 2026.

## Files

- `Cover_Exacting_Definability_Followup.pdf`: the 17-page report.
- `Cover_Exacting_Definability_Followup.tex`: self-contained LaTeX source.
- `README.md`: build and verification notes.

## Results and scope

The main derived theorem is that a gamma-cover-exacting cardinal lambda is
regular in HCD(gamma^+). HCD(eta) is computed in the ambient universe and
means the inner model of sets hereditarily ordinal definable from eta-complete
ultrafilters on ordinals.

This gives two different negative consequences:

1. If a strongly compact delta lies below lambda, there is an unbounded
   a subset of lambda in HCD(delta), of order type less than delta, which
   has no cover in HCD(gamma^+) of ambient cardinality less than lambda.
   Thus the explicitly stated local covering or small-set agreement principle
   is inconsistent with the configuration. The unrestricted coexistence
   question is not resolved.
2. If a strongly compact kappa lies above the fixed cover bound gamma,
   HCD(kappa) is a proper set-forcing ground in which lambda is regular.
   Therefore the Ground Axiom is incompatible with these hypotheses.
   Any forcing over this particular ground that produces the ambient universe
   has ground-model cardinality at least lambda.

The report also gives an I0-equiconsistent package: an ultraexacting lambda
can be the first exacting cardinal, with V_lambda contained in HOD, while a
single countable cofinal set outside HOD witnesses the stated approximation
and covering failures.

Historical priority of the derived formulations is not certified. The
ultrafilter trace technique, HCD covering and ground theorems, and the
ultraexacting/I0 construction are explicitly attributed. The affirmative
package is an assembled corollary of an existing construction, not a new
forcing construction.

## Build

A standard TeX Live or MiKTeX installation with the packages used in the source
is sufficient. In the directory containing the source, run:

```text
pdflatex -interaction=nonstopmode -halt-on-error Cover_Exacting_Definability_Followup.tex
pdflatex -interaction=nonstopmode -halt-on-error Cover_Exacting_Definability_Followup.tex
```

Alternatively:

```text
latexmk -pdf Cover_Exacting_Definability_Followup.tex
```

No external images, bibliography database, or custom font files are needed.
The supplied report's preamble was reused: newpxtext/newpxmath, TeX Gyre Heros
sans-serif accents, the same page geometry, and the Forest/Olive/Muted/Sage/Pale
color definitions. Fonts are embedded in the PDF; no separate fonts are included.

## Verification

The PDF was compiled with pdfLaTeX, its citations and cross-references were
resolved, and all pages were rendered and visually inspected. The final LaTeX
log has no overfull or underfull boxes and no undefined-reference warnings.
The source report was also compiled to compare the typography and font families.

The mathematical deductions were audited as conventional proofs. They are not
proof-assistant formalizations, have not been independently refereed, and the
successful LaTeX build is not a claim of mathematical machine verification.
The primary inputs and their exact roles are listed in the report's references
and dependency appendix.
