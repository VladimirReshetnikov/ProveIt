# The Surreal Numbers as a Real Vector Class

**Subtitle:** Conway–Hahn Coordinates, Hamel Bases, Strong Duality, and Canonical Operators

This package contains the final 32-page research article prepared on October 1, 2026.

## Files

- `surreal_numbers_real_vector_class.tex` — self-contained LaTeX source.
- `surreal_numbers_real_vector_class.pdf` — compiled article.
- `SHA256SUMS.txt` — integrity hashes for the source and PDF.

## Build

A standard TeX Live installation with `latexmk` is sufficient. From this directory, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_numbers_real_vector_class.tex
```

The source uses only standard LaTeX packages available in current TeX Live distributions; the bibliography is embedded in the `.tex` file, so no separate `.bib` file is required.

## Repository snapshot and status

The repository context was inspected at `VladimirReshetnikov/ProveIt`, commit
`f7e7d8607d3b1c49c93b844cae20a77ab3689fe7`.

This is an AI-assisted, unrefereed research draft. It distinguishes classical inputs from deductions proved in the article, and it does not claim that the new statements have been independently refereed or formally verified in Lean.
