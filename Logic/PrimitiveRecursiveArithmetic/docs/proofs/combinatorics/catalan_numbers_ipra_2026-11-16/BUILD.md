# Build and validation

## Requirements

- Python 3.11 or later (the delivered run used 3.13.5)
- `pdflatex` with standard AMS, `hyperref`, `microtype`, `booktabs`,
  `longtable`, and `listings` packages
- Optional: Lean 4 plus the ProveIt derivation environment to compile the Lean
  scaffold after copying it into the repository

## Exact verification

From the package root:

```bash
python code/verify_catalan.py > verification/run.log
```

Success writes `verification/certificate.json` with status `PASS`.

## PDF build

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error catalan_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error catalan_ipra.tex
```

The second pass resolves the table of contents and cross-references.

## PDF render validation

The delivery was rendered with the installed PDF workflow:

```bash
python /home/oai/skills/pdfs/scripts/render_pdf.py \
  paper/catalan_ipra.pdf --out_dir /tmp/catalan_render --dpi 160
```

Inspect the rendered PNGs for clipping, overlaps, and broken glyphs. A PDF
structure check can be run with:

```bash
python /home/oai/skills/pdfs/scripts/pdf_inspect.py paper/catalan_ipra.pdf
```

## Lean

The delivery environment had no `lean` or `lake`, so no Lean compile result is
claimed. In a ProveIt checkout at the recorded snapshot, place
`CatalanProveItBlueprint.lean` under the derivations package and run the
repository's normal Lake command. `CatalanExecutable.lean` needs only `Std`.
Neither file contains `sorry`.

## Checksums

Regenerate after any modification:

```bash
find . -type f ! -name MANIFEST.sha256 ! -name MANIFEST.txt -print0 | sort -z | \
  xargs -0 sha256sum > MANIFEST.sha256
```
