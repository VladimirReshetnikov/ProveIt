# Targeted source and evidence audit

Date: 12 October 2026.

## Repository anchor

The GitHub `main` branch response identified commit:

`704600626606a9097cfd89d4e3d2bbc63c8dd1cb`

Its recorded commit time was 2026-10-12T19:29:19Z. The raw-cut article below was explicitly fetched at this commit. Earlier initial documentation reads used the branch without an explicit revision argument; their returned blob identifiers are retained separately. They are not silently asserted to be a full coherent source checkout at the anchor commit.

| Path, relative to repository root | Read scope | Returned blob |
|---|---|---|
| `Topology/UnknotRecognition/synthesis/cut_cells.tex` | Full text; explicitly pinned to the anchor | `dc12b1a58aedaed78f00b63109b0aa5214832ca1` |
| `Topology/UnknotRecognition/README.md` | Project overview and implementation status; initial branch read | `4fb929b5689d0bc20327e241cb775789660c8013` |
| `Topology/UnknotRecognition/synthesis/closure_resets.tex` | Full text; used to distinguish Khovanov resets from hierarchy resets | `3f70a929908516470fae2aa0ab33fec8c5cf2488` |
| `Topology/UnknotRecognition/synthesis/cocycle_blocking.tex` | Full text; nearby polynomial local optimization, not a black-box ingredient | `7eb5853be900e0b431b985727c15c77ba9be8cb0` |
| `docs/incoming/README.md` | Initial 160 source lines, including topic-specific intake rules | `3e336b71356574182847c9b8e6eb4fcd60c1b449` |

A code search for `normal_cut_cells` surfaced indexed results at another revision, `20ae15571536010edbc034ded58a14dc285230c0`. Those snippets were navigation context, not a claim to have executed that revision. No production-code diff is delivered.

## Source facts used

The pinned raw-cut document describes source-authenticated binary affine CW families in dimensions zero through three, retaining source attaching data. It explicitly separates such geometry from bare cellular boundary matrices. It names `normal_cut_cell_complex`, `verify_normal_cut_cell_complex`, and `normal-cut-cells-v1`.

Its inspected native source domain is a validated finite connected compact orientable triangulation with one torus boundary. Its normal surface may be disconnected or one-sided. The candidate-system theorems in this delivery require a narrower labeled/cooriented surface contract but allow more general later ambient pieces. Neither extension is automatically supplied by the existing packet. A new adapter must prove the appropriate relation between the two interfaces.

Historical native test counts and performance measurements in the repository are not reruns by this delivery. They are not used as the evidence for the new Python modules.

## Incoming work and Library scope

The incoming directory metadata listed contemporaneous disconnected-tile, moment-coded-first-return, hierarchy-kernel, and sparse-cut-grammar archives. The complete archive contents were not all read or executed.

Targeted Library retrieval supplied individual manuscript excerpts from:

- *Corner-Aware Boundary Kernels for Compressed Unknot Hierarchies*: abstract and stated source-adapter/global-bound limitations.
- *Moment-coded first returns*: evidence ledger and references, including the distinction between mocked native API tests and source-geometric authentication.
- *Sparse Cut Grammars* and *Disconnected Tile Kernels*: related bibliographic scope.
- Report 25, *Causal-Branch Parameterization of Reidemeister-III Unlocking*: theorem statements, causal-birth scope, and its unproved hierarchy-transfer discussion.

These provide lineage and help avoid conflating distinct uses of “causal” or “reset.” No claim is made that every incoming report was audited or that the proposed combination has established worldwide priority.

## External mathematical sources

1. Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*, arXiv:2607.23350v1 (25 July 2026). The online full text was read at the relevant hierarchy, compression, and iteration passages. Proposition 9.1 states the `L(g+1)^L` iteration bound; Section 10 separately refines hierarchy length. These are background motivation, not an imported quasi-polynomial bound.
2. Ian Agol, Joel Hass, William Thurston, *The computational complexity of knot genus and spanning area*, arXiv:math/0205057v2. The interval-orbit and weighted-orbit theorems were inspected; the PDF page containing Theorem 16 was also rendered. Weighted-orbit computation is imported with its encoded-size hypotheses, not implemented or experimentally rerun in this package.

Classical chamber-graph, cycle-lattice, cographic, and spanning-tree arguments are proved self-contained in the article. They are not labeled newly invented foundations.

## What actually ran

The new standard-library modules, their finite tests, examples, and paired graph-stage benchmark ran in the working container under CPython 3.13.5. `results/validation.json`, `results/test_log.txt`, and `results/benchmark.json` contain the actual outputs. The article was compiled with pdfLaTeX and rendered for visual review.

A full native ProveIt checkout and Regina geometry were not executed. No native source adapter, native compressed route exporter, or full-recognition speedup is claimed. The graph-stage baseline is exhaustive subset search, not the previous production implementation.
