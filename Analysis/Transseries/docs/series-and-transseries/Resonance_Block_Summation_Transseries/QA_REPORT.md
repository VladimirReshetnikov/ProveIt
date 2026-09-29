# Build and quality-assurance record

Date: 29 September 2026.

## Article

- PDF: 25 A4 pages, including the title page and contents.
- Engine: pdfLaTeX (pdfTeX 1.40.26).
- Final source compiled successfully on repeated passes.
- Final log: 0 TeX errors, 0 undefined references/citations, 0 overfull boxes.
- Two underfull-box notices remain in bibliography paragraphs. They cause no
  clipping or overlap and were visually checked.
- The bibliography is embedded in the TeX file. No BibTeX run is required.
- All generated-table dependencies are included in the distribution.

## Visual inspection

All 25 pages were rendered with Poppler's `pdftoppm` and inspected in contact
sheets and selected full-page images. The final modified appendix, source
paths, build commands, and references were rendered and checked again at
105 dpi. The inspection included the title/contents, theorem displays,
residue formulas, numerical tables, proof-dependency table, and bibliography.

Two initially overlong paths/paragraphs were corrected. The proof-dependency
table was moved to a fresh page to avoid leaving one row at the bottom of the
preceding page, and the build-command block was kept intact. The final PDF has
no observed clipped text, overlapping equations, missing symbols, or broken
tables. The contact sheets and temporary build artifacts are not packaged.

## Program execution

Recorded environment:

- Python 3.13.5
- SymPy 1.14.0
- mpmath 1.3.0

Executed successfully:

```text
python verify.py --stage symbolic   -> 36 exact assertions passed
python verify.py --stage numeric    -> 15 numerical assertions passed
python verify.py --stage tables     -> table and aggregate results written
python -m py_compile verify.py      -> passed
```

Total: 51 passing assertions. Contour checks use 90 decimal digits; reference
pair calculations use 200 digits. The deliberate 50-digit raw-formula failure
is recorded as a conditioning demonstration, not counted as a failed assertion.

The tests are not interval-arithmetic certificates, an exhaustive proof audit,
or a Lean build. The source contains the actual mathematical proofs and states
its unresolved extensions explicitly.

## Distribution

The archive contains the article, verification source, executed results,
generated TeX table, build/dependency files, provenance, this QA record, and a
SHA-256 manifest. It excludes TeX auxiliary files, execution caches, raw tool
responses, external source documents, and font files. Archive integrity and
its per-file hashes were checked at packaging time.
