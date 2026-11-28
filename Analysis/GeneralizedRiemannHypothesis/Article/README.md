# Merged article

[`article.pdf`](article.pdf) merges 209 delivered research reports into one article of
988 pages, *Beyond the Riemann hypothesis
for Dirichlet L-functions: consequences, transfers and limits*. Each result is stated once,
in the strongest form the reports prove. A result that follows from a stronger or more
general result of the collection, with hypotheses no stronger, is left out, and so is
repeated material: the reports' many accounts of the upstream Lean proof are replaced by
one section.

The article is a merge, not a review. Its mathematics is that of the reports. Nothing was
recomputed, and the claims have not been independently checked or formalized. The input
theorem, RH and GRH for Dirichlet L-functions as stated in the external Lean development
`lsernau/grh-lean`, is taken as given. Every result carries one of three marks:
*unconditional*, *uses Dirichlet GRH*, or *reduction; the target estimate is open*. No
result of the last kind proves a new Riemann hypothesis or any named conjecture.

The reports were removed from the working tree once merged. They are in the history under
`Analysis/GeneralizedRiemannHypothesis/Research/`: the first 103 at commit `10802a6b36`, the next 17 at commit `f2f9fd7531`, the next 11 at commit `64f3896557`, the next 11 at commit `fd9a9cb2bd`, the next 42 at commit `f6b5955e13`, the next 10 at commit `7f951e1dfd` and the last 15 at commit `3c4d27a69c`.
Packet names are unique, so the article's citations of delivered files, and the packet
and file columns of the provenance tables, each refer to exactly one of these commits.

## Files

- `article.tex` is the main file. It inputs `preamble.tex`, the abstract and introduction,
  and one file per section under [`sections/`](sections/). The bibliography is
  `references.bib`, merged from the per-section files under [`bib/`](bib/).
- [`provenance/`](provenance/README.md) has one table per section. It lists, for every
  section of every report, where its material went, and for every omitted result the result
  that supersedes it.
- To rebuild, run in a scratch copy of this directory: `pdflatex article`, `bibtex article`,
  then `pdflatex article` twice. The build needs only standard LaTeX packages.

## Sections

| Part | Section | File | Results | Unconditional | Uses GRH | Reductions |
|---|---|---|---:|---:|---:|---:|
| I | The source theorem and its transferable mechanism | [`src.tex`](sections/src.tex) | 6 | 5 | 1 | 1 |
| I | Spanning, completion and integral frames | [`spn.tex`](sections/spn.tex) | 30 | 28 | 0 | 0 |
| I | One-sided analytic criteria | [`ana.tex`](sections/ana.tex) | 70 | 53 | 5 | 2 |
| I | Li coefficients, moment pencils and positivity certificates | [`li.tex`](sections/li.tex) | 55 | 33 | 22 | 0 |
| I | The Li heat semigroup and random laws built from zeros | [`lih.tex`](sections/lih.tex) | 55 | 34 | 29 | 0 |
| II | Nonabelian zero detection: general reductions | [`nab.tex`](sections/nab.tex) | 37 | 22 | 10 | 10 |
| II | Detectors for specific Galois groups and fields | [`grp.tex`](sections/grp.tex) | 39 | 24 | 1 | 16 |
| II | Degree-two targets: Artin, Hecke and modular L-functions | [`hec.tex`](sections/hec.tex) | 33 | 22 | 0 | 14 |
| III | Prime races, Mertens errors and Euler products at the critical line | [`zer.tex`](sections/zer.tex) | 31 | 5 | 25 | 0 |
| III | Prime errors at several scales: covariance, balancing, peaks and merging | [`flu.tex`](sections/flu.tex) | 66 | 24 | 42 | 0 |
| III | Positive filters that cancel zeros | [`fil.tex`](sections/fil.tex) | 65 | 55 | 22 | 0 |
| III | Recovering zeros from prime data and analytic samples | [`rec.tex`](sections/rec.tex) | 44 | 24 | 24 | 0 |
| III | Characters and arithmetic parameters from zeros | [`chz.tex`](sections/chz.tex) | 84 | 25 | 62 | 0 |
| III | Hermitian couplings of completed L-functions: real zeros, inverse problems and transport | [`cpl.tex`](sections/cpl.tex) | 40 | 17 | 24 | 0 |
| III | Matching Euler factors of products of Dirichlet L-functions | [`eul.tex`](sections/eul.tex) | 33 | 28 | 6 | 0 |
| IV | Consequences through published theorems: primes, primitive roots and prime gaps | [`dir.tex`](sections/dir.tex) | 19 | 4 | 18 | 0 |
| IV | Small primes in residue classes: subset products, sign patterns and codes | [`prd.tex`](sections/prd.tex) | 98 | 57 | 54 | 0 |
| IV | Class groups of imaginary quadratic fields and orders | [`cls.tex`](sections/cls.tex) | 23 | 9 | 15 | 0 |
| IV | CM coefficient fields, reflected fields and uniform Galois bounds | [`cmf.tex`](sections/cmf.tex) | 31 | 18 | 14 | 0 |
| IV | Sparse equations for singular moduli | [`smd.tex`](sections/smd.tex) | 48 | 30 | 2 | 0 |
| V | Progression-free sets in polynomial rings and finite rings; additive constraints | [`gpp.tex`](sections/gpp.tex) | 36 | 36 | 0 | 0 |
| V | Progression-free sets of integers and of ideals | [`gpi.tex`](sections/gpi.tex) | 25 | 19 | 0 | 0 |
| V | Graph towers and spanning-tree valuations | [`gra.tex`](sections/gra.tex) | 33 | 29 | 0 | 0 |
| V | Quantum walks, signed square cycles and edge-polytope zeros | [`grw.tex`](sections/grw.tex) | 23 | 19 | 0 | 0 |
| V | Compressions of random symplectic and orthogonal matrices | [`cmp.tex`](sections/cmp.tex) | 98 | 100 | 0 | 0 |
| VI | Torsion specialization I: shells, exact costs and selection | [`tors.tex`](sections/tors.tex) | 39 | 24 | 0 | 0 |
| VI | Torsion specialization II: coefficient fields, characters and limits | [`cost.tex`](sections/cost.tex) | 36 | 30 | 2 | 0 |
| VI | Lubin–Tate branches, jet recovery and Fleck congruences | [`lub.tex`](sections/lub.tex) | 42 | 38 | 0 | 0 |
| VI | The Selmer, Galois-cohomology and K-theory interface | [`sel.tex`](sections/sel.tex) | 46 | 42 | 0 | 0 |
| | Total | | 1285 | 854 | 378 | 43 |

"Results" counts theorems, propositions, corollaries and lemmas. The status columns count
the marks in theorem headings; lemmas and corollaries are often unmarked, so the status
columns do not add up to the first.
