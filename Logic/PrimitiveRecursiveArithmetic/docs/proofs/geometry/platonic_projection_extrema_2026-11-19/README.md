# Extreme orthographic shadows of the five Platonic solids

Research packet prepared for Vladimir Reshetnikov, 19 November 2026.

## Results

All solids have edge length a > 0. Multiply the following values by a².

| Solid | Minimum | Maximum |
|---|---|---|
| Tetrahedron | 1/(2 sqrt(2)) | 1/2 |
| Cube | 1 | sqrt(3) |
| Octahedron | 1/sqrt(2) | 1 |
| Dodecahedron | (5+2 sqrt(5))/2 | sqrt(250+110 sqrt(5))/4 |
| Icosahedron | sqrt(35+15 sqrt(5))/4 | sqrt(3)(3+sqrt(5))/4 |

The report specifies all coordinate models, viewing directions, screen coordinates,
and shadow shapes. The icosahedron's minimum is not a usual vertex, face, or
edge-midpoint symmetry view.

## What is proved and what is checked

`report.pdf` and its complete source `report.tex` give the human proof, including
an explicit bounded cone decomposition and exact arithmetic in Q(phi).
The iPRA endpoint is a universal numerical theorem over coded algebraic vectors,
with closed algebraic attaining witnesses. Its represented-real extension is a
schema for each fixed PR name with a supplied modulus; ordinary arbitrary-real
geometry is the semantic corollary. No universal PR interpreter is assumed.

The exact Python checks were executed successfully. Across all five solids they
check 1,128 signed sums and 75 pair cross products, plus the facets, face area
vectors, regular-face distance identities, spanning determinants, and witnesses.
The universal proof is in the report: finite numerical checks alone would not
prove a bound for all directions.

**Lean status:** `lean/ProjectionOutline.lean` and
`lean/ObjectTargetOutline.lean` are uncompiled outlines. They introduce no axioms
or `sorry`, but their proof-obligation records are not instantiated. They are not
a completed kernel-checked proof of the projection theorem. No Lean executable
was available during preparation.

## Files

- `report.tex`, `report.pdf`: complete report.
- `lean/ProjectionOutline.lean`: exact field, vectors, five data instances,
  certificates, projection definitions, and proof obligations.
- `lean/ObjectTargetOutline.lean`: precise ConciseIPRA `Prf PRAAx` endpoint.
- `code/exact_verify.py`: uniform verifier using Python standard-library
  rational arithmetic only. No floating-point decisions.
- `code/icosahedron_independent.py`: independent integer-pair reconstruction of
  the icosahedral upper and lower tables and triple determinants.
- `certificates/*.json`: full exact data. A pair `[a,b]` denotes a+b*phi,
  with phi²=phi+1. The uniform verifier represents rational coefficients as strings;
  the independent checker uses integer coefficients.
- `code/draw_shadows.py`, `figures/`: reproducible vector and raster illustrations.
- `verification/`: successful exact check log and PDF quality summary.
- `sources/proveit/`: inspected source snapshots and pinned source/blob URLs.
  These are provenance references, not a complete transitive dependency bundle.
- `SHA256SUMS.txt`: integrity hashes for the packet files other than the manifest.

## Reproduce the exact checks

Use Python 3.10 or later, with assertions enabled (do not use `python -O`):

```bash
python3 code/exact_verify.py --output certificates
python3 code/icosahedron_independent.py > certificates/icosahedron_independent.json
```

The second command writes the independently reconstructed JSON certificate.
Neither checker needs SymPy, SciPy, floating-point optimization, or network access.

To rebuild figures, install the optional packages listed in
`requirements-figures.txt`, then run:

```bash
python3 code/draw_shadows.py
```

The plotting code performs a separate numerical hull/shoelace check as a visual
sanity check; this is not part of the exact mathematical proof.

To rebuild the PDF on a normal TeX Live installation with the packages imported
in the preamble:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`make verify`, `make figures`, and `make pdf` provide the same workflows.

## Repository integration

Inspected ProveIt commit: `09fe17194da14cdd100947737952e44100bb71b8`.
Exact paths and Git blob hashes are in `sources/proveit/SOURCES.md`.
The report explains which existing object-theory derivations can be reused and
which new lemmas remain to be formalized. In particular, existing quadratic-ring
identities do not already provide ordered-field coding, and existing dodecahedral
coordinate certificates do not already prove the complete projection bridge.

No changes were made to the GitHub repository as part of this packet.
