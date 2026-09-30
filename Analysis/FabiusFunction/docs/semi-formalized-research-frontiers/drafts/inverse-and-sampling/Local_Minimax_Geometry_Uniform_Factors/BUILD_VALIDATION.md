# Build and validation record

## PDF

- Built from the delivered `article.tex` using pdfLaTeX (pdfTeX 1.40.26).
- Final build used three successful consecutive passes after the last source edit.
- Final compiler output contains no warnings, undefined references, underfull boxes,
  or overfull boxes.
- Output is a 20-page A4 PDF with 15 table-of-contents/bookmark entries.
- All 20 pages were rendered at 120 dpi using the supplied PDF rendering tool.
- Page contact sheets were inspected for layout; theorem/equation pages and the
  final reference page were also inspected at full rendered size.
- A text-coordinate pass found no spans outside a 30-point horizontal and
  10-point vertical safety boundary. No unresolved `??` references were found.
- No clipping, overlapping text, or broken mathematical glyphs was observed.

The visible date is 29 September 2026. The PDF metadata uses UTC, which can
show 30 September for the same evening in America/Los_Angeles.

## Supporting computation

Environment: Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0.

Command run successfully after the final script edit:

```sh
python verify_results.py --numerics --output verification_results.json
```

Outcome: 186 exact assertions passed and four high-precision finite-window
likelihood diagnostics completed. The exact rational constants and numerical
values agree with the entries in Section 11 of the article. Numerical work
uses 65-digit arithmetic over [-12,12], not interval arithmetic or certified
tail/error bounds.

## Mathematical status

The article's universal results are supported by its conventional proofs.
Compilation, rendering, and finite checks are not substitutes for independent
mathematical review or formal proof verification. No Lean/Rocq checking is
claimed. The eight research questions are explicitly outside the proved scope.

## Archive

Only the final article source/PDF, supporting code and results, build commands,
and explanatory files are distributed. TeX intermediates, rendered inspection
images, and font files are excluded. `SHA256SUMS.txt` covers every other file in
the package; it is not self-referential.
