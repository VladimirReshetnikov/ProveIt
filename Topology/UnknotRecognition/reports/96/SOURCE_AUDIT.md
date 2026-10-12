# Source audit — 12 October 2026

## Reference revision

`4840e384b5a2961aabbb9cc78023b9ac5990acb0`

The GitHub connector returned this main-branch checkpoint during inspection.
The repository was changing concurrently. This is a reference checkpoint,
not a claim that a complete local checkout was obtained.

## Targeted repository reads

- `Topology/UnknotRecognition/README.md`: current scope and implemented pipelines.
- `Topology/UnknotRecognition/synthesis/cut_cells.tex`: complete binary raw-cut
  construction and the remaining separation from bounded-core reduction.
- `Topology/UnknotRecognition/reports/README.md`: report catalogue, including
  reports 82–87 and prior low-nullity/source-certificate work.
- `Topology/UnknotRecognition/reports/87/README.md` and
  `article/support_theory.tex`: maximal support, source reuse, and the already
  established GLOBAL intrinsic-dimension branching theorem.
- `Topology/UnknotRecognition/fast/tests/test_normal_sector_integration.py`:
  the one-tetrahedron and capped solid-torus face pairings and expected meridian
  coordinates; the file explicitly distinguishes positive Euler values from
  essential-disc conclusions.
- `docs/incoming/README.md` and the directory listing: intake context and inventory.

The report-87 support theory was re-fetched at the exact reference revision;
its returned blob identity was `23effdcdd4dbbf89a172943d77e30d25793fc7e0`.
The fetched fixture source had blob identity
`efb7b9348a66a9ee7b57420c354e9baf8c5ef75f`.
The raw-cut manuscript read had identity
`dc12b1a58aedaed78f00b63109b0aa5214832ca1`.
These identities document the targeted reads; they do not imply that other
repository files or arbitrary earlier reports were exhaustively inspected.

## Incoming archives not inspected

The observed inventory included:

- `ProveIt_Disconnected_Tile_Kernels_2026-10-12.zip`
- `ProveIt_Moment_Coded_First_Returns_2026-10-12.zip`
- `ProveIt_Unknot_Hierarchy_Kernels_2026-10-12.zip`
- `ProveIt_Unknot_Sparse_Cut_Grammars_2026-10-12.zip`

The connector supported their directory metadata but not binary downloads;
a container network checkout/download also failed. No claims about the
unseen ZIP contents, their validity, or their overlap with this work are made.
They were not executed, extracted, modified, or deleted.

## Primary public literature

Marc Lackenby's author page and 2021 quasi-polynomial lecture listing were
checked, together with the July 2026 preprint *Incompressible surfaces,
hierarchies and unknot recognition*, arXiv:2607.23350v1. Section 9 is explicit
about the absence of fully specified running-time estimates for some steps.
The PDF was also visually inspected through the browser's PDF screenshot tool.

Burton and Ozlen's *A fast branching algorithm for unknot recognition with
experimental polynomial-time behaviour*, arXiv:1211.1079v3 (2014), supplies the
established positive-Euler/crushing interface. Its historical statements about
then-current complexity are not presented as current 2026 facts.

Borgwardt, Grewe, and Lee, *On the Combinatorial Diameters of Parallel and
Series Connections*, arXiv:2203.09587v3 (2023), was consulted to situate rank-one
matrix connections in the existing matroid/polyhedral setting. No claim is made
that this paper proves our exact compatibility-message theorem.

The article also cites Haken's original normal-surface framework and Khachiyan's
polynomial-time LP result as classical foundations. The contribution should not
be described as a new discovery of either foundation.

## Executed work

Only the code delivered in this package was executed. There was no Regina
installation, native ProveIt test execution, full repository clone, Lean proof
check, or production patch application. The source fixture adapters are newly
written code using the explicitly read face-pairing data. Native source validity
and diagram ancestry remain caller obligations.
