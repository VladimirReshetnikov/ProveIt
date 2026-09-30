# Build and inspection report

Date: 30 September 2026

## Compilation

The delivered source was compiled using:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The final build completed successfully. The resulting document has **26
physical pages**, US Letter size (612 by 792 PDF points). The final LaTeX
log contains no warnings, undefined references, overfull boxes, or underfull
boxes. The source is standalone, with an internal bibliography and two TikZ
figures. Text and mathematical fonts are embedded in the PDF; font files are
not included in this package.

## PDF inspection

All 26 pages of the final PDF were rendered to PNG at 75 dpi and inspected
in three contact sheets. The contents, the finite-description rigidity
proof, the sharp-family figure and scalar-extension warning, the moment
polar theorem, and the final bibliography were additionally inspected in
higher-resolution page renders during final revisions. The final text
extraction check found nonempty text on every page. No clipping, overlap,
missing figures, blank pages, or orphaned bibliography page was observed.
The temporary render images are not part of the deliverable.

## Exact finite regression run

```sh
python3 code/verify.py --output data/verification_results.json
```

The supplied program completed successfully with **28,890 exact rational
checks**. Its output and grouped counts are included in `data/`. These
finite checks are not an independent proof of the infinite statements,
not a Lean certificate, and not an implementation of the entire surreal
field. The mathematical proofs are in the article.

## Source and PDF identity

- `article.tex`: `6fa7cae1c6d70d8325446529821de1812d14a735bd0733e3bfcfd2cf96b10c65`
- `article.pdf`: `93a7ceabab9c7dfe6d66e20fec6622bd1bdc6cee7196ae14ce75d807c03a4828`

`SHA256SUMS.txt` records hashes of all delivered files other than itself.
LaTeX auxiliary files, transient build logs, and inspection renders are
excluded from the ZIP. No ProveIt repository build was attempted and no
remote repository was modified.
