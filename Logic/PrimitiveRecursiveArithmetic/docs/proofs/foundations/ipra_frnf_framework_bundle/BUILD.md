# Build and integration instructions

## Local artifact build

Requirements:

- Python 3.10 or later;
- `pdflatex`;
- `pdftotext` and `pdfinfo` from Poppler.

Run:

```bash
chmod +x build.sh
./build.sh
```

The script uses no third-party Python packages. The paper uses common TeX Live
packages and an inline bibliography, so BibTeX is not required.

## Python reference validation

```bash
cd reference
python -m unittest -v test_frnf.py
```

The algorithms use `fractions.Fraction`, so the numerical comparisons are exact.
They model the finite algorithms; they are not an iPRA proof checker.

## Lean integration

The audited ProveIt root pins:

```text
leanprover/lean4:v4.32.0
mathlib v4.32.0
```

A recommended migration path is:

1. Copy `lean/FRNF/Kernel.lean` and the other files into
   `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/FRNF/`.
2. Change imports from `FRNF.Kernel` to the resulting library path where needed.
3. Add a root module under `IPRADerivations/FRNF.lean`.
4. Replace every `opaque` endpoint in `ObjectTargets.lean` with an explicit
   object formula.
5. Eliminate every visible `sorry` by reusing the checked modules listed in
   Section 20 of the paper.
6. Build and audit:

```bash
lake build IPRADerivations
lake env lean \
  Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/FRNF/Audit.lean
```

The audit module should contain `#print axioms` for every exported result and a
check for `sorryAx`. A theorem should be labeled object checked only after the
pinned build succeeds and its endpoint is visibly of type `Prf PRAAx ...`.

## PDF visual validation

The final PDF was rendered with:

```bash
python /home/oai/skills/pdfs/scripts/render_pdf.py \
  paper/ipra_frnf_framework.pdf --out_dir <temporary-directory> --dpi 140
```

All 60 rendered pages were inspected, including the title page, theorem pages,
the multi-page obstacle table, Lean code listings, artifact map, and references.
Temporary renders are not included in the archive.
