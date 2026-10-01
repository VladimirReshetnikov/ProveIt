# Build and validation report

## Artifact

- Title: *Sharp C^r Spectral Disks for the Rvachev--Thue--Morse Transfer Operator*
- Repository comparison pin: `ffddaa8b9c89e7bf027e1442cc6216bb010906d0`
- Prepared: 30 September 2026, Pacific time
- Output: 16-page A4 PDF
- PDF size: 493,704 bytes

## LaTeX build

The PDF was built from `article.tex` with three successful passes:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The final log contained no undefined references, multiply defined labels,
overfull boxes, underfull boxes, or package warnings matching the standard
warning scan. The bibliography is internal; no BibTeX or external assets are
used.

## Exact finite verification

Executed command:

```text
python verify.py --output verification.json
```

Result: **pass**.

- Asserted exact checks: 361
- Three-mode matrix entries recorded: 9
- Descendant-frequency cases: 130
- Endpoint-jet orders: 13 (`r = 0,...,12`)
- Spectral-threshold orders: 13
- Arithmetic: `fractions.Fraction` plus formal polynomials in `q = pi^2`

The program tests only finite algebraic consequences. It deliberately does
not present finite sampling as proof of the Fredholm, Calkin, compactness, or
regularity arguments.

## PDF preflight and visual inspection

- PDF opened successfully and is unencrypted.
- Page count: 16.
- Preflight warnings: none.
- Fonts: embedded subsetted Type 1 Latin Modern/AMS fonts; no Type 3 fonts.
- Text extraction: no Unicode replacement characters or black-square glyphs.
- Render validation: all 16 pages rendered at 180 dpi and inspected; no clipped
  text, overlaps, missing formulas, broken glyphs, or malformed tables were
  observed.

## SHA-256 checksums

```text
73a934721f38ecdb4b6c319602bdb2e83e3ccebaaaedea3ed35bb22105306e69  article.tex
48b7c99774b247bbcbd4f080e1fbbb5525d74c5ee87a4ae407080cf52e20705e  article.pdf
b7a577646236a157a88adea23140260440789d404ce72f32186bcdf306d016e7  verify.py
55b9b4d77fcd147afc61798f526966d02dec2e55ad2684747fffcaa73580675f  verification.json
```

## Scope

No Lean or Rocq theorem was added or built. The manuscript proves an exact
integer-`C^r` result and records noninteger Hoelder/Zygmund, collision, and
formalization questions as future work. Global literature priority is not
claimed.
