# Validation record

## Exact coefficient checks

Command:

```bash
python3 code/verify.py
```

Recorded output: `validation/validation_output.txt`.

The program uses `fractions.Fraction`; there is no floating-point comparison in
any asserted test. It checks univariate and bivariate formulas, Bell
polynomials, algebraic examples, both Lambert expansions, Catalan numbers,
the exact rational enclosure of `W(1)`, and the associahedron normalization
countercheck.

## PDF build

Command:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  paper/lagrange_inversion_ipra.tex
```

The final PDF has 24 letter-size pages. `validation/pdf_preflight.txt` records
that it is openable, unencrypted, text-based, and has no form/XFA content.

The PDF was rendered page by page at 150 dpi with:

```bash
python /home/oai/skills/pdfs/scripts/render_pdf.py \
  paper/lagrange_inversion_ipra.pdf --out_dir <temporary-render-dir> --dpi 150
```

All pages were visually inspected. No clipped text, overlaps, black squares, or
broken glyphs were found. Temporary page renders are not included in the final
archive.

## Lean status

The Lean artifact is a blueprint. It was not claimed or recorded as a
kernel-checked proof. Its imports and API names were chosen against Mathlib
v4.32.0 and the inspected ProveIt snapshot, but the schematic target theorems
remain to be implemented.
