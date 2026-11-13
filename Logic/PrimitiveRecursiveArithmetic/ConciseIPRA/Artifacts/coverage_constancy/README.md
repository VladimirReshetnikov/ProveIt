# Coverage does not recover induction from scalar constancy

Prepared for Vladimir Reshetnikov, 13 November 2026.

## Status

The requested positive axiomatization below the current ConciseIPRA complexity
envelope was **not obtained**. This package contains a new obstruction result,
relative to the inspected repository, and a reproducible current baseline audit.
It does not claim a new smallest checker or a complexity lower bound.

The main theorem proves that scalar computation, numerical coverage, an actual
Boolean equality test, and contextual scalar constancy do not recover equation
induction. The theory is not ordinarily bi-interpretable with iPRA, even allowing
finite parameters, finite-dimensional definable domains and quotient equality.
The countermodel also validates mixed fusion, fixed-point preservation, seed
shift and body extensionality. Deleting the primitive equality test does not
remove the obstruction.

This answers the explicit coverage questions in the consolidated article's
“Scalar constancy” question, item 1, and “Root conversion” question, item 4,
at commit `95d3dd192e97a19bd4f8783c764331ec41126264`.

## Files

- `report.pdf`: the complete research report.
- `report.tex`: complete self-contained LaTeX source; no external figures needed.
- `controls/`: nine unchanged attributed baseline checkers and their license.
- `evidence/source_snapshot.json`: pinned provenance and exact source hashes.
- `evidence/measurements.json` and `.csv`: source, token, AST and gzip-9 sizes.
- `evidence/finite_shadow.json`: explicitly limited finite illustration.
- `evidence/independent_review.md`: independent written audit of the core proof.
- `evidence/independent_audit.md`: a second independent audit of the proof.
- `evidence/census_screen.json.gz`: static measurements of 1,623 Python modules
  in the inspected snapshot and extracted incoming packages; screening data,
  not a list of semantically certified checkers.
- `evidence/verification.json`: build, rendering and reproduction record.
- `tools/measure.py`: remeasure the controls without executing them.
- `tools/finite_shadow.py`: illustrate the ambient construction and show the
  failed coverage boundary of every finite cutoff; not a model proof.
- `STATUS.json`: machine-readable claim boundaries.
- `MANIFEST.sha256`: hashes of all other delivered files.

## Reproduce

```sh
python3 tools/measure.py --check
python3 tools/finite_shadow.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Exact measurement reproduction uses CPython 3.12.14 and the recorded zlib
runtime. Normalization is `ast.unparse(ast.parse(source)) + '\n'`; gzip uses
compression level 9 and `mtime=0`. Sources with different input contracts must
not be treated as a single checker attaining every coordinate minimum.

The new mathematics is a detailed written proof, independently reviewed, not
a Lean or Rocq formalization. The finite script does not validate nonstandard
model existence, all-term rule soundness or the automorphism obstruction.
The inherited checkers have been remeasured; this package does not independently
certify all of their semantic correctness theorems.
