# Positive averages and prescribed Fourier zeros

Open **positive-fourier-zeros.pdf** for the collected papers, with a linked reading guide and bookmarks. Each paper also has a standalone PDF and a LaTeX source in its own directory.

| Paper | Primary source | Result |
| --- | --- | --- |
| I | `steinerberger/support.tex` | Sharp one-dimensional inverse-square estimate in Steinerberger's Problem 41, with finite-cardinality extremizers and stability. |
| II | `square_gaps/squares.tex` | Uniform order of the longest zero-free interval for a block of squares, including short-block asymptotics and long-block constants. |
| III | `global_endpoint/endpoint.tex` | Exact supremal double-exponential tail coefficient for positive laws annihilating a completed Dirichlet product, with endpoint classification in explicit families. This paper includes `general.tex` and `weighted.tex`. |
| IV | `kozma/gaps.tex` | A finite rule for arbitrary three-term arithmetic progressions of frequencies, and a certified transcendental length for the frequencies 1, 4, 7. |
| V | `ring_density/frobenius.tex` | A product criterion for positive progression-free density when finite local rings have characteristic two and cube-zero maximal ideal. |
| VI | `graph_onset/onset.tex` | A logarithmic bound on the onset of the spanning-tree valuation formula in every fixed rank, and matching examples on fixed bouquets. |

The starting article is [ProveIt, GeneralizedRiemannHypothesis, revision ff96fd44ab16](https://github.com/VladimirReshetnikov/ProveIt/tree/ff96fd44ab160e65fb8a9d861243828d07c156cf/Analysis/GeneralizedRiemannHypothesis). Each paper identifies the specific result it uses and supplies references. Papers I and II respond to [Steinerberger's Problem 41](https://faculty.washington.edu/steinerb/openproblems.pdf) and [Kozma and Oravecz's Question 2](https://arxiv.org/html/math/0601021v1). Paper III uses the critical-line property to identify its prescribed divisor with real ordinates. Its full-complex-divisor statement is unconditional under its stated real-zero criterion. Papers I, II, IV, V and VI are unconditional.

## Rebuilding the volume

From this directory, with Python 3, PyMuPDF and pdfLaTeX available, run

```sh
python3 assemble.py --compile
```

This compiles each source twice and assembles the guide and six papers in order. A standard TeX Live installation with Latin Modern, the AMS packages, microtype, hyperref and the table packages in the preambles is sufficient. To assemble the supplied individual PDFs without recompiling LaTeX, run `python3 assemble.py`. The supplied volume was assembled with PyMuPDF 1.26.6.

## Replaying the finite calculations

Run these commands from this directory. The degree-54 certificate uses SymPy (tested with 1.14.0). The other three programs use the Python standard library.

```sh
python3 square_gaps/check_squares.py
python3 kozma/check_gaps.py
python3 ring_density/check_rings.py
python3 graph_onset/verify.py
```

The corresponding output is saved beside each program. The square-frequency checks compare finite rational bounds and test the index partition. The three-frequency program checks contact conditions, isolation, and irreducibility by exact arithmetic. The ring and graph programs check the finite examples and identities specified in their papers. The analytic theorems are supported by the written proofs. Independent peer review and proof-assistant formalization of these research notes are outstanding.

On a system with GNU coreutils, run `sha256sum -c SHA256SUMS` from this directory to verify the extracted files before rebuilding them.
