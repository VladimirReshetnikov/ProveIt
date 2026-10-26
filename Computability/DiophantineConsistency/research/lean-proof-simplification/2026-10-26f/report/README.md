# Simplifying the DiophantineConsistency Lean proofs

The PDF and editable TeX report review ProveIt commit
`60e9c5d620c6c387d932876cfa2d9376f64ea56c`.

## Build the report

```sh
bash build.sh
```

Required tools: XeLaTeX/TeX Live, with fontspec, amsmath/amssymb, microtype,
xcolor, booktabs, array/tabularx/longtable, enumitem, fvextra, xurl, hyperref,
bookmark, titlesec, needspace, etoolbox and fancyhdr. Fonts: Latin Modern Roman, Latin Modern Sans,
and DejaVu Sans Mono. The build script makes three passes to resolve contents
and cross-references. It includes an isolated fallback for the preparation
environment's incomplete TeX filename database/format installation; normal
TeX Live installations do not need that fallback.

`make qa` uses Poppler (`pdftoppm`, `pdftotext`) to render page images and
extract text for inspection. QA images, caches and auxiliary logs are not
needed to read or rebuild the final report and are omitted from the release.

## Evidence status

The PDF was typeset and visually checked. No Lean or Lake executable was
available; every proposed Lean candidate is uncompiled. A successful TeX/PDF
build is not Lean validation. Source text checks and the future Lean replay
workflow are described in the report and in `../validation/README.md`.

All repository references are immutable links at the full reviewed commit.
The focused source snapshot is not a complete buildable ProveIt project.
