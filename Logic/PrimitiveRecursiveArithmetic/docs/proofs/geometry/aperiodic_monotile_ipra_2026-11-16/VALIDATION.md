# Validation record

Validation was performed on 2026-11-16.

## Exact reference verifier

Command:

```bash
python tools/verify_hat_certificate.py --levels 6
```

Result: **PASS**.

Checked exactly with `fractions.Fraction`:

- hat polygon simplicity;
- axial shoelace sum `32`, hence area `8*sqrt(3)`;
- fixed patch type counts;
- supertile child counts and substitution matrix;
- characteristic polynomial `x^4-7*x^3+7*x-1`;
- the complete mod-2 table for `Q(m,n)=m^2+mn+n^2`;
- convexity and strict containment of the distinguished H child for six exact rational
  generations.

The six-generation containment check is a regression test, not an extrapolation proof.
Uniform radius growth is proved in the report through substitution depth in the elementary
kite adjacency graph; formal verification of that finite interface table is a Lean
milestone.

## PDF

- LaTeX compiled twice with `pdflatex -halt-on-error`.
- 17 pages, US Letter.
- Rendered all pages at 130 DPI with the PDF skill renderer.
- Contact-sheet inspection found no clipped figures, missing glyphs, or unresolved
  references.

## Lean

Lean was not installed in the generation environment.  The scaffold was therefore not
compiled.  It contains explicit `sorry` and `opaque` placeholders and is not presented as
a completed formal proof.
