# Delivery validation

Date: 6 October 2026.

## PDF and source

The final `article.tex` compiled successfully with pdfLaTeX. Multiple passes
resolved the cross-references. The final compilation has no undefined references,
LaTeX errors, or overfull boxes. Minor underfull-box diagnostics are limited to
text wrapping and do not indicate clipping.

The resulting PDF has 19 A4 pages. All pages were rendered; contact-sheet review
and larger views of the title, contents, proof pages, computation table,
provenance table, and references were used to inspect layout. The final PDF has
no observed clipping, overlapping text, or missing-glyph boxes. Extracted text
contains no unresolved `??` references or replacement characters, and every
extracted text block lies within its page bounds.

## Mathematical computation

`checks/verify.py` was run after the final code changes. It reported:

```text
All exact assertions passed.
```

The recorded results cover 17,682 affine normal forms representing 846,650 maps,
4,976 sparse/error-value cases, three subgroup equality examples, a two-torsion
counterexample to the odd-target formula, and exact rational substitution of
eight inverse coefficients. See the JSON and log for the individual results.
All inequality tests use exact integers or rational numbers.

These checks do not establish universal theorems or publication priority. The
mathematical proofs are in the article. No Lean build was run and no kernel
verification is claimed. No source repository was modified.

## Package hygiene

The ZIP includes the finished article, editable source, verification program and
results, build script, provenance, and formalization notes. It excludes LaTeX
intermediates, page-render images, original third-party papers, and standalone
font files.
